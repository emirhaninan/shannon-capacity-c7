"""Independent exact engine for gadget block sets in C_7^{5m}.

Every set is a list of pairwise-disjoint product blocks; a block is a tuple of m atoms,
each atom an explicit subset of C_7^5 (codes 0..16806, little-endian base 7 as in BPZ/Tan data).
Written from the definitions (Gao's lemma, Tandon's Theorem 1), not from Tan's code.
"""
import json, itertools
import numpy as np
from collections import Counter, defaultdict

N5 = 7 ** 5
import os
DATA = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'base_c7.json')


def dec(c):
    return tuple((c // 7 ** j) % 7 for j in range(5))


def enc(w):
    return sum((x % 7) * 7 ** j for j, x in enumerate(w))


TMAP = np.array([enc(((2 - w[1]) % 7, w[3], w[0], (2 - w[2]) % 7, w[4])) for w in map(dec, range(N5))])
assert len(set(TMAP.tolist())) == N5


def dilate(mask):
    # closed box neighbourhood: separable over the 5 coordinates
    m = mask.reshape((7,) * 5)
    for ax in range(5):
        m = m | np.roll(m, 1, ax) | np.roll(m, -1, ax)
    return m.reshape(-1)


# ---------------- atoms (interned) ----------------
_ATOMS = []          # id -> mask
_INDEX = {}          # bytes -> id
_NB = {}             # id -> dilated mask
_T = {}


def atom(mask):
    mask = np.asarray(mask, dtype=bool)
    key = np.packbits(mask).tobytes()
    i = _INDEX.get(key)
    if i is None:
        i = len(_ATOMS)
        _ATOMS.append(mask.copy())
        _INDEX[key] = i
    return i


def atom_of(elems):
    m = np.zeros(N5, bool)
    m[list(elems)] = True
    return atom(m)


def asize(i):
    return int(_ATOMS[i].sum())


def anb(i):
    if i not in _NB:
        _NB[i] = dilate(_ATOMS[i])
    return _NB[i]


def aT(i):
    if i not in _T:
        m = np.zeros(N5, bool)
        m[TMAP[_ATOMS[i]]] = True
        _T[i] = atom(m)
    return _T[i]


EMPTY = None


def isempty(i):
    return not _ATOMS[i].any()


# ---------------- block sets ----------------
def clean(blocks):
    return [b for b in blocks if not any(isempty(a) for a in b)]


def size(blocks):
    tot = 0
    for b in blocks:
        n = 1
        for a in b:
            n *= asize(a)
        tot += n
    return tot


def cross(A, B):
    return [a + b for a in A for b in B]


def Tset(blocks):
    return [tuple(aT(a) for a in b) for b in blocks]


def check_disjoint(blocks):
    for i, b1 in enumerate(blocks):
        for b2 in blocks[i + 1:]:
            if not any(not (_ATOMS[x] & _ATOMS[y]).any() for x, y in zip(b1, b2)):
                raise ArithmeticError('blocks not provably disjoint')


def _groups(a, refatoms):
    """Counter: (tuple of bools over refatoms) -> number of elements of atom a."""
    m = _ATOMS[a]
    cols = np.stack([anb(r)[m] for r in refatoms], axis=1) if refatoms else np.zeros((int(m.sum()), 0), bool)
    if cols.shape[0] == 0:
        return {}
    packed = np.packbits(cols, axis=1)
    keys, cnt = np.unique(packed, axis=0, return_counts=True)
    out = {}
    for k, c in zip(keys, cnt):
        bits = np.unpackbits(k)[:len(refatoms)]
        out[tuple(bool(x) for x in bits)] = int(c)
    return out


def split_by(blocks, ref):
    """Split a disjoint block set S into (S minus N(ref), S cap N(ref)), both as block sets.
    Refines every atom by its membership pattern in the coordinate neighbourhoods of the ref blocks."""
    if not ref:
        return list(blocks), []
    m = len(ref[0])
    refat = [sorted({r[i] for r in ref}) for i in range(m)]
    pos = [{a: j for j, a in enumerate(refat[i])} for i in range(m)]
    rb = [[pos[i][r[i]] for i in range(m)] for r in ref]
    cache = {}

    def cells(a, i):
        key = (a, i)
        if key not in cache:
            mk = _ATOMS[a]
            if not refat[i]:
                cache[key] = [((), a)]
            else:
                cols = np.stack([anb(r) for r in refat[i]], axis=1)  # N5 x k
                pat = np.packbits(cols, axis=1)
                d = defaultdict(lambda: np.zeros(N5, bool))
                idx = np.nonzero(mk)[0]
                for x in idx:
                    d[pat[x].tobytes()][x] = True
                res = []
                for kb, msk in d.items():
                    bits = np.unpackbits(np.frombuffer(kb, np.uint8))[:len(refat[i])]
                    res.append((tuple(bool(b) for b in bits), atom(msk)))
                cache[key] = res
        return cache[key]

    out, inn = [], []
    for b in blocks:
        lists = [cells(a, i) for i, a in enumerate(b)]
        for combo in itertools.product(*lists):
            covered = any(all(combo[i][0][rb[k][i]] for i in range(m)) for k in range(len(ref)))
            (inn if covered else out).append(tuple(c[1] for c in combo))
    return out, inn


def count_outside(source, ref, check=True):
    """|union(source) minus N(union(ref))| exactly (source blocks pairwise disjoint)."""
    if check:
        check_disjoint(source)
    m = len(ref[0])
    refat = [sorted({r[i] for r in ref}) for i in range(m)]
    pos = [{a: j for j, a in enumerate(refat[i])} for i in range(m)]
    nref = len(ref)
    # bitmask over ref blocks of those whose i-th atom is atom j
    sel = [[0] * len(refat[i]) for i in range(m)]
    for k, r in enumerate(ref):
        for i in range(m):
            sel[i][pos[i][r[i]]] |= 1 << k
    memo = {}

    def groups(a, i):
        key = (a, i)
        if key not in memo:
            g = _groups(a, refat[i])
            out = Counter()
            for flags, c in g.items():
                mk = 0
                for j, f in enumerate(flags):
                    if f:
                        mk |= sel[i][j]
                out[mk] += c
            memo[key] = out
        return memo[key]

    full = (1 << nref) - 1
    total = 0
    for b in source:
        acc = {full: 1}
        for i, a in enumerate(b):
            g = groups(a, i)
            nxt = defaultdict(int)
            for k1, n1 in acc.items():
                for k2, n2 in g.items():
                    nxt[k1 & k2] += n1 * n2
            acc = nxt
        total += acc.get(0, 0)
    return total


# ---------------- gadgets ----------------
class Gadget:
    """Physical block sets: B (= I minus R), R (centres), PH, PV, X0, XH, XV."""

    def __init__(self, m, **sets):
        self.m = m
        self.S = {k: clean(v) for k, v in sets.items()}

    def __getitem__(self, k):
        if k == 'Xr':
            return self.S['XH'] + self.S['XV']
        if k == 'I':
            return self.S['B'] + self.S['R']
        if k == 'X':
            return self.S['X0'] + self.S['XH'] + self.S['XV']
        return self.S[k]

    def profile(self):
        z = {k: size(v) for k, v in self.S.items()}
        return (z['B'] + z['R'], z['R'], z['X0'] + z['XH'] + z['XV'], z['X0'], z['XH'], z['XV'])

    def sigma(self):
        S = self.S
        return Gadget(self.m, B=S['B'], R=S['R'], PH=S['PV'], PV=S['PH'], X0=S['X0'], XH=S['XV'], XV=S['XH'])

    def aux(self):
        return {'X0': self['X0'], 'XH': self['XH'], 'XV': self['XV']}


def main_sets(L, R):
    c = cross
    return dict(B=c(L['B'], R['B']) + c(L['PH'], R['XH']) + c(L['PV'], R['XV']) + c(L['XH'], R['PV'])
                + c(L['XV'], R['PH']),
                R=c(L['R'], R['X0']) + c(L['X0'], R['R']),
                PH=c(L['PH'], R['X0']) + c(L['X0'], R['PV']),
                PV=c(L['PV'], R['X0']) + c(L['X0'], R['PH']))


def gao(L, R):
    c = cross
    S = main_sets(L, R)
    S.update(X0=c(L['X0'], R['X0']) + c(L['Xr'], R['Xr']),
             XH=c(L['XH'], R['X0']) + c(L['X0'], R['XV']),
             XV=c(L['XV'], R['X0']) + c(L['X0'], R['XH']))
    return Gadget(L.m + R.m, **S)


_SPLIT = {}


def hetgao(L, R, J0, JH, JV):
    """Tandon's Theorem 1.  J0: dict X0/XH/XV (classes w.r.t. L's transversals); JH, JV: independent block sets
    in L's space, split here against N(X_L^0)."""
    c = cross
    S = main_sets(L, R)
    ref = L['X0']
    JHq, JHn = split_by(JH, ref)
    JVq, JVn = (JHq, JHn) if JV is JH else split_by(JV, ref)
    S.update(X0=c(J0['X0'], R['X0']) + c(JHq, R['XH']) + c(JVq, R['XV']),
             XH=c(J0['XH'], R['X0']) + c(JVn, R['XV']),
             XV=c(J0['XV'], R['X0']) + c(JHn, R['XH']))
    return Gadget(L.m + R.m, **S)


# ---------------- base data ----------------
def load_base():
    d = json.load(open(DATA))
    I = set(d['I0']); X = set(d['X'])
    pairs = [tuple(p) for p in d['private_pairs']]
    PH, PV = set(d['PH']), set(d['PV'])
    Rc = {a for a, _ in pairs}
    nbm = lambda S: dilate(np.isin(np.arange(N5), list(S)))
    NH, NV = nbm(PH), nbm(PV)
    Xm = np.isin(np.arange(N5), list(X))
    X0 = Xm & ~NH & ~NV; XH = Xm & NH; XV = Xm & NV
    assert not (Xm & NH & NV).any()
    one = lambda S: [(atom_of(S),)] if S else []
    G5 = Gadget(1, B=one(I - Rc), R=one(Rc), PH=one(PH), PV=one(PV),
                X0=[(atom(X0),)], XH=[(atom(XH),)], XV=[(atom(XV),)])
    exch = [(tuple(a), tuple(b)) for a, b in d['exchanges']['pairs']]
    return G5, exch


def remove_word(blocks, w):
    """Remove the single word w (tuple of 5-dim codes) from a disjoint block set."""
    out = []
    hit = 0
    for b in blocks:
        if all(_ATOMS[a][x] for a, x in zip(b, w)):
            hit += 1
            # b minus {w} = union over i of ({w_0}x..x{w_{i-1}}) x (b_i - w_i) x b_{i+1..}
            for i in range(len(b)):
                pre = tuple(atom_of([w[j]]) for j in range(i))
                mi = _ATOMS[b[i]].copy(); mi[w[i]] = False
                out.append(pre + (atom(mi),) + tuple(b[i + 1:]))
        else:
            out.append(b)
    assert hit == 1, hit
    return clean(out)


# ---------------- fast versions ----------------
def _intersects(x, y):
    return bool((_ATOMS[x] & _ATOMS[y]).any())


def check_disjoint_fast(blocks):
    """Prove pairwise disjointness: recursively split by connected components of
    intersecting atoms at each coordinate; atoms in different components are disjoint.
    Groups surviving to the end are checked pairwise directly."""
    memo = {}
    def inter(x, y):
        k = (x, y) if x < y else (y, x)
        if k not in memo:
            memo[k] = _intersects(x, y)
        return memo[k]
    m = len(blocks[0]) if blocks else 0
    stack = [(list(range(len(blocks))), 0)]
    while stack:
        idx, i = stack.pop()
        if len(idx) < 2:
            continue
        if i == m:
            raise ArithmeticError('two blocks intersect in every coordinate')
        ats = sorted({blocks[k][i] for k in idx})
        parent = {a: a for a in ats}
        def find(a):
            while parent[a] != a:
                parent[a] = parent[parent[a]]; a = parent[a]
            return a
        for p in range(len(ats)):
            for q in range(p + 1, len(ats)):
                if inter(ats[p], ats[q]):
                    parent[find(ats[p])] = find(ats[q])
        comp = defaultdict(list)
        for k in idx:
            comp[find(blocks[k][i])].append(k)
        for c in comp.values():
            if len(c) < 2:
                continue
            # within a component, blocks with *disjoint* atoms here are still disjoint; only
            # blocks whose atoms intersect need further coordinates.  Conservative: recurse on all.
            stack.append((c, i + 1))


def count_outside_fast(source, ref, check=True):
    if check:
        check_disjoint_fast(source)
    m = len(ref[0])
    refat = [sorted({r[i] for r in ref}) for i in range(m)]
    pos = [{a: j for j, a in enumerate(refat[i])} for i in range(m)]
    nref = len(ref)
    sel = [[0] * len(refat[i]) for i in range(m)]
    for k, r in enumerate(ref):
        for i in range(m):
            sel[i][pos[i][r[i]]] |= 1 << k
    gm = {}
    def groups(a, i):
        key = (a, i)
        if key not in gm:
            g = _groups(a, refat[i])
            out = Counter()
            for flags, c in g.items():
                mk = 0
                for j, f in enumerate(flags):
                    if f:
                        mk |= sel[i][j]
                out[mk] += c
            gm[key] = list(out.items())
        return gm[key]
    full = (1 << nref) - 1
    # trie DP: process blocks sorted, share prefix states
    order = sorted(source)
    total = 0
    stack_states = [{full: 1}]   # states after prefix of length len-1
    prev = ()
    for b in order:
        # common prefix with prev
        L = 0
        while L < len(prev) and prev[L] == b[L]:
            L += 1
        del stack_states[L + 1:]
        for i in range(L, m):
            acc = stack_states[i]
            nxt = defaultdict(int)
            for k2, n2 in groups(b[i], i):
                for k1, n1 in acc.items():
                    nxt[k1 & k2] += n1 * n2
            stack_states.append(nxt)
        total += stack_states[m].get(0, 0)
        prev = b
    return total


def check_disjoint_fast(blocks):
    """Exact proof that the blocks are pairwise disjoint: two product blocks are disjoint iff
    some coordinate has disjoint atoms.  Recursive bipartite check over atom classes."""
    memo = {}
    def inter(x, y):
        if x == y:
            return True
        k = (x, y) if x < y else (y, x)
        if k not in memo:
            memo[k] = _intersects(x, y)
        return memo[k]
    m = len(blocks[0]) if blocks else 0
    def grp(lst, i):
        g = defaultdict(list)
        for b in lst:
            g[b[i]].append(b)
        return g
    stack = [(blocks, None, 0)]
    while stack:
        A, B, i = stack.pop()
        same = B is None
        if same and len(A) < 2:
            continue
        if not same and (not A or not B):
            continue
        if i == m:
            raise ArithmeticError('two blocks intersect in every coordinate')
        ga = grp(A, i)
        if same:
            keys = sorted(ga)
            for p, a in enumerate(keys):
                stack.append((ga[a], None, i + 1))
                for b in keys[p + 1:]:
                    if inter(a, b):
                        stack.append((ga[a], ga[b], i + 1))
        else:
            gb = grp(B, i)
            for a in ga:
                for b in gb:
                    if inter(a, b):
                        stack.append((ga[a], gb[b], i + 1))

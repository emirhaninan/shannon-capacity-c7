"""Exact chunk-summary DP for q = |J minus N(X^0(L))| without materialising 4^m flag tensors.

Sets are symbolic expressions over 5-dimensional units:  Blk (explicit product blocks), Cross, Uni (disjoint
union), Spl (S cap N(R) / S minus N(R)), and T is pushed to the leaves (T is a graph automorphism of C_7^5).
A reference R is compiled into a tree of summary nodes: a node over an interval holds the membership bits of a
word in N(S_1),...,N(S_n) for a few basis sets S_i over that interval; its state is a function of the states of
its two children (N(A x B) = N(A) x N(B), N(union) = union of N).  Leaves are single 5-dim units (bit masks) or
10-dim pairs with exact 10-dim neighbourhood maps (needed when a basis set is a split, e.g. J+ cap N(X^0)).
dist(S, forests) returns the exact joint distribution of the words of S over the states of several node
forests (each forest partitions S's interval); Spl inside a source adds the split reference as an extra forest.
Everything is exact (Python integers in object arrays)."""
import numpy as np, itertools
from collections import defaultdict
import engine as E
from engine import _ATOMS, N5, atom, aT, Tset, dilate, anb, split_by

KEEP = []          # keep every expression alive (ids are memo keys)


class S:
    __slots__ = ('k', '__weakref__')


class Blk(S):
    __slots__ = ('blocks',)
_BLK = {}


def blk(blocks, k):
    blocks = [b for b in blocks if not any(not _ATOMS[a].any() for a in b)]
    key = (k, tuple(sorted(set(blocks))))
    if key not in _BLK:
        o = Blk(); o.k = k; o.blocks = list(key[1]); _BLK[key] = o; KEEP.append(o)
    return _BLK[key]


class Cross(S):
    __slots__ = ('a', 'b')
_CR = {}


def cross(a, b):
    if isempty(a) or isempty(b):
        return blk([], a.k + b.k)
    key = (id(a), id(b))
    if key not in _CR:
        o = Cross(); o.k = a.k + b.k; o.a = a; o.b = b; _CR[key] = o; KEEP.append(o)
    return _CR[key]


class Uni(S):
    __slots__ = ('parts',)
_UN = {}


def uni(parts, k):
    flat = []
    for p in parts:
        assert p.k == k
        if isinstance(p, Uni):
            flat += p.parts
        elif not isempty(p):
            flat.append(p)
    if len(flat) == 1:
        return flat[0]
    if not flat:
        return blk([], k)
    key = tuple(id(p) for p in flat)
    if key not in _UN:
        o = Uni(); o.k = k; o.parts = flat; _UN[key] = o; KEEP.append(o)
    return _UN[key]


class Spl(S):
    __slots__ = ('s', 'r', 'inside')
_SP = {}


def spl(s, r, inside):
    if isempty(s):
        return s
    key = (id(s), id(r), inside)
    if key not in _SP:
        o = Spl(); o.k = s.k; o.s = s; o.r = r; o.inside = inside; _SP[key] = o; KEEP.append(o)
    return _SP[key]


def isempty(s):
    return isinstance(s, Blk) and not s.blocks


_TX = {}


def Tx(s):
    """T applied coordinatewise (an automorphism, so T(S cap N(R)) = T(S) cap N(T(R)))."""
    if id(s) in _TX:
        return _TX[id(s)]
    if isinstance(s, Blk):
        r = blk(Tset(s.blocks), s.k)
    elif isinstance(s, Cross):
        r = cross(Tx(s.a), Tx(s.b))
    elif isinstance(s, Uni):
        r = uni([Tx(p) for p in s.parts], s.k)
    else:
        r = spl(Tx(s.s), Tx(s.r), s.inside)
    _TX[id(s)] = r
    return r


# ---------------- physical materialisation (small sets only) ----------------
_PH = {}


def phys(s):
    if id(s) in _PH:
        return _PH[id(s)]
    if isinstance(s, Blk):
        r = list(s.blocks)
    elif isinstance(s, Cross):
        r = E.cross(phys(s.a), phys(s.b))
    elif isinstance(s, Uni):
        r = [b for p in s.parts for b in phys(p)]
    else:
        out, inn = split_by(phys(s.s), phys(s.r))
        r = inn if s.inside else out
    _PH[id(s)] = r
    return r


# ---------------- sizes ----------------
_SZ = {}


def size(s):
    if id(s) in _SZ:
        return _SZ[id(s)]
    if isinstance(s, Blk):
        r = E.size(s.blocks)
    elif isinstance(s, Cross):
        r = size(s.a) * size(s.b)
    elif isinstance(s, Uni):
        r = sum(size(p) for p in s.parts)
    else:
        d = dist(s.s, ((refnode((s.r,)),),))
        r = int(d[1 if s.inside else 0])
    _SZ[id(s)] = r
    return r


# ---------------- decomposition at a split point ----------------
class NoSplit(Exception):
    pass


_TA = {}


def terms_at(s, p):
    """list of (L, R): s = disjoint union of L x R, L over the first p units."""
    key = (id(s), p)
    if key in _TA:
        return _TA[key]
    if isinstance(s, Cross):
        if p == s.a.k:
            r = [(s.a, s.b)]
        elif p < s.a.k:
            r = [(l, cross(rr, s.b)) for l, rr in terms_at(s.a, p)]
        else:
            r = [(cross(s.a, l), rr) for l, rr in terms_at(s.b, p - s.a.k)]
    elif isinstance(s, Uni):
        r = [t for q in s.parts for t in terms_at(q, p)]
    elif isinstance(s, Blk):
        g = defaultdict(list)
        for b in s.blocks:
            g[b[:p]].append(b[p:])
        # merge prefixes having identical suffix sets
        h = defaultdict(list)
        for pre, suf in g.items():
            h[tuple(sorted(suf))].append(pre)
        r = [(blk(pres, p), blk(list(suf), s.k - p)) for suf, pres in h.items()]
    elif s.k <= PHYS_MAX:
        # a split cannot be cut symbolically: materialise it as exact refined product blocks
        r = terms_at(blk(phys(s), s.k), p)
    else:
        raise NoSplit
    _TA[key] = r
    return r


def natural(s):
    if isinstance(s, Cross):
        return s.a.k
    if isinstance(s, Uni):
        for q in s.parts:
            n = natural(q)
            if n is not None:
                return n
    return None


# ---------------- reference summary nodes ----------------
class Node:
    __slots__ = ('k', 'sets', 'ns', 'kind', 'p', 'l', 'r', 'tab', 'code', 'forb')


_RN = {}
_BM = {}          # packed 10-dim neighbourhood bitmaps per set id
MAXBITS = 12
PHYS_MAX = 5
COST_MAX = 1 << 14


def mask5(s):
    m = np.zeros(N5, bool)
    for b in phys(s):
        m |= _ATOMS[b[0]]
    return m


def bitmap10(s):
    if id(s) not in _BM:
        m = np.zeros((N5, N5), bool)
        for a, b in phys(s):
            m[np.ix_(np.nonzero(_ATOMS[a])[0], np.nonzero(_ATOMS[b])[0])] = True
        m = m.reshape((7,) * 10)
        for ax in range(10):
            m = m | np.roll(m, 1, ax) | np.roll(m, -1, ax)
        _BM[id(s)] = np.packbits(m.reshape(N5, N5), axis=1)
        KEEP.append(s)
    return _BM[id(s)]


def refnode(sets):
    sets = tuple(dict.fromkeys(sets, None))   # dedupe by identity, keep order
    key = tuple(id(x) for x in sets)
    if key in _RN:
        return _RN[key]
    k = sets[0].k
    assert all(x.k == k for x in sets)
    n = Node(); n.k = k; n.sets = sets; n.ns = 1 << len(sets); n.forb = frozenset()
    if k == 1:
        n.kind = 'L5'
        code = np.zeros(N5, np.int32)
        for i, x in enumerate(sets):
            code |= dilate(mask5(x)).astype(np.int32) << i
        n.code = code
    else:
        built = False
        p = None
        for x in sets:
            p = natural(x)
            if p is not None:
                break
        if p is None:
            p = 1
        try:
            tl = [terms_at(x, p) for x in sets]
            lefts = tuple(dict.fromkeys([l for t in tl for l, _ in t], None))
            rights = tuple(dict.fromkeys([r for t in tl for _, r in t], None))
            if len(lefts) > MAXBITS or len(rights) > MAXBITS:
                raise NoSplit
            built = True
        except NoSplit:
            if k != 2:
                raise
        if built:
            n.kind = 'G'; n.p = p
            n.l = refnode(lefts); n.r = refnode(rights)
            li = {id(x): i for i, x in enumerate(n.l.sets)}; ri = {id(x): i for i, x in enumerate(n.r.sets)}
            ls = np.arange(n.l.ns)[:, None]; rs = np.arange(n.r.ns)[None, :]
            tab = np.zeros((n.l.ns, n.r.ns), np.int64)
            for i, t in enumerate(tl):
                bit = np.zeros((n.l.ns, n.r.ns), bool)
                for l, r in t:
                    bit |= (((ls >> li[id(l)]) & 1) & ((rs >> ri[id(r)]) & 1)).astype(bool)
                tab |= bit.astype(np.int64) << i
            n.tab = tab
            n.forb = frozenset(n.l.forb) | frozenset(p + f for f in n.r.forb)
        else:
            n.kind = 'L10'
            for x in sets:
                bitmap10(x)
            n.forb = frozenset([1])
    _RN[key] = n
    KEEP.append(sets)
    return n


# ---------------- forests ----------------
def refine(F, p):
    """split forest F (list of nodes) at offset p; returns (F_left, F_right)."""
    out = []; off = 0
    stack = list(F)[::-1]
    while stack:
        nd = stack.pop()
        if off < p < off + nd.k:
            if nd.kind != 'G':
                raise NoSplit
            stack.append(nd.r); stack.append(nd.l)
            continue
        out.append((off, nd)); off += nd.k
    L = [nd for o, nd in out if o < p]; R = [nd for o, nd in out if o >= p]
    return L, R


def forb_of(F):
    s = set(); off = 0
    for nd in F:
        s |= {off + f for f in nd.forb}; off += nd.k
    return s


def merge_axes(t, i, tab, ns):
    """replace axes i, i+1 (states of left/right child) by the parent axis via tab."""
    t2 = np.moveaxis(t, (i, i + 1), (-2, -1))
    sh = t2.shape[:-2]
    t2 = t2.reshape(sh + (-1,))
    flat = tab.ravel()
    new = np.zeros(sh + (ns,), dtype=object)
    for s in range(ns):
        sel = np.nonzero(flat == s)[0]
        if len(sel):
            new[..., s] = t2[..., sel].sum(axis=-1)
    return np.moveaxis(new, -1, i)


def coarsen(t, cur, target, ax0=0):
    """t has axes ax0.. for nodes cur (consecutive) ; coarsen them to the target forest. returns (t, n_axes)."""
    pos = ax0; ci = 0
    for tg in target:
        # collect current nodes covering tg
        need = tg.k; seg = []
        while need > 0:
            seg.append(cur[ci]); need -= cur[ci].k; ci += 1
        assert need == 0
        t = _coarsen_one(t, seg, tg, pos)
        pos += 1
    return t


def _coarsen_one(t, seg, tg, pos):
    if len(seg) == 1:
        assert seg[0] is tg, 'forest mismatch'
        return t
    assert tg.kind == 'G'
    # split seg into parts covering tg.l and tg.r
    acc = 0; i = 0
    while acc < tg.l.k:
        acc += seg[i].k; i += 1
    assert acc == tg.l.k
    t = _coarsen_one(t, seg[:i], tg.l, pos)
    t = _coarsen_one(t, seg[i:], tg.r, pos + 1)
    return merge_axes(t, pos, tg.tab, tg.ns)


# ---------------- leaf distributions ----------------
_LD = {}


def leaf_dist(s, forests):
    """s over 1 or 2 units; forests fully refined to leaves (L5 per unit or one L10)."""
    blocks = phys(s)
    shape = [nd.ns for F in forests for nd in F]
    acc = np.zeros(int(np.prod(shape)) if shape else 1, dtype=object)
    k = s.k
    for b in blocks:
        idx = [np.nonzero(_ATOMS[a])[0] for a in b]
        if k == 1:
            code = np.zeros(len(idx[0]), np.int64)
            for F in forests:
                (nd,) = F
                code = code * nd.ns + nd.code[idx[0]]
        else:
            code = np.zeros((len(idx[0]), len(idx[1])), np.int64)
            for F in forests:
                if len(F) == 1:
                    nd = F[0]
                    c = np.zeros(code.shape, np.int64)
                    for i, x in enumerate(nd.sets):
                        bits = np.unpackbits(_BM[id(x)][idx[0]], axis=1, count=N5)[:, idx[1]]
                        c |= bits.astype(np.int64) << i
                    code = code * nd.ns + c
                else:
                    n0, n1 = F
                    code = (code * n0.ns + n0.code[idx[0]][:, None]) * n1.ns + n1.code[idx[1]][None, :]
        bc = np.bincount(code.ravel(), minlength=len(acc))
        acc = acc + bc.astype(object)
    return acc.reshape(shape) if shape else acc.reshape(())


def full_refine(F):
    out = []
    for nd in F:
        if nd.kind == 'G':
            out += full_refine([nd.l, nd.r])
        else:
            out.append(nd)
    return out


# ---------------- main DP ----------------
_D = {}


def dist(s, forests):
    forests = tuple(tuple(F) for F in forests)
    key = (id(s), tuple(tuple(id(n) for n in F) for F in forests))
    if key in _D:
        return _D[key]
    shape = tuple(nd.ns for F in forests for nd in F)
    if isempty(s):
        r = np.zeros(shape, dtype=object)
    elif not forests:
        r = np.array(size(s), dtype=object)
    elif isinstance(s, Uni):
        r = sum(dist(q, forests) for q in s.parts)
    elif isinstance(s, Spl):
        rn = refnode((s.r,))
        d = dist(s.s, forests + ((rn,),))
        r = d[..., 1 if s.inside else 0]
    elif s.k <= 2 and (s.k == 1 or any(nd.kind == 'L10' for F in forests for nd in full_refine(F))):
        fr = [full_refine(F) for F in forests]
        t = leaf_dist(s, fr)
        pos = 0
        for F, R in zip(forests, fr):
            t = coarsen(t, R, F, pos); pos += len(F)
        r = t
    else:
        forb = set()
        for F in forests:
            forb |= forb_of(full_refine(F))
        cands = []
        n0 = natural(s)
        if n0 is not None:
            cands.append(n0)
        cands += sorted(range(1, s.k), key=lambda x: (abs(x - (n0 or 1)), x))
        def _cost(p):
            try:
                parts = [refine(F, p) for F in forests]
            except NoSplit:
                return None
            ca = 1; cb = 1
            for a, b in parts:
                for nd in a: ca *= nd.ns
                for nd in b: cb *= nd.ns
            return ca + cb
        c0 = _cost(cands[0]) if cands[0] not in forb else None
        if c0 is None or c0 > COST_MAX:
            cc = [(c, i, p) for i, p in enumerate(cands) if p not in forb for c in [_cost(p)] if c is not None]
            cands = [p for c, i, p in sorted(cc)] + cands
        r = None
        for p in cands:
            if p in forb:
                continue
            try:
                tl = terms_at(s, p)
                parts = [refine(F, p) for F in forests]
            except NoSplit:
                continue
            FA = tuple(tuple(a) for a, _ in parts); FB = tuple(tuple(b) for _, b in parts)
            tot = None
            for L, R in tl:
                dA = dist(L, FA); dB = dist(R, FB)
                o = np.multiply.outer(dA, dB)
                tot = o if tot is None else tot + o
            # reorder axes: [A axes of all forests][B axes of all forests] -> per forest A then B
            na = [len(a) for a in FA]; nb = [len(b) for b in FB]
            order = []; oa = 0; ob = sum(na)
            for x, y in zip(na, nb):
                order += list(range(oa, oa + x)) + list(range(ob, ob + y)); oa += x; ob += y
            tot = np.transpose(tot, order)
            pos = 0
            for F, (a, b) in zip(forests, parts):
                tot = coarsen(tot, list(a) + list(b), F, pos); pos += len(F)
            r = tot
            break
        if r is None:
            raise NoSplit('no admissible split for %s k=%d' % (type(s).__name__, s.k))
    _D[key] = r
    return r


def count_out(s, ref):
    """|s minus N(ref)|"""
    rn = refnode((ref,))
    d = dist(s, ((rn,),))
    return int(d[0])


def count_in_out(s, ref):
    d = dist(s, ((refnode((ref,)),),))
    return int(d[0]), int(d[1])


# ---------------- symbolic gadgets ----------------
class SG:
    def __init__(self, m, **c):
        self.m = m; self.c = c

    def __getitem__(self, k):
        c = self.c
        if k == 'Xr':
            return uni([c['XH'], c['XV']], self.m)
        if k == 'I':
            return uni([c['B'], c['R']], self.m)
        if k == 'X':
            return uni([c['X0'], c['XH'], c['XV']], self.m)
        return c[k]

    def sigma(self):
        c = self.c
        return SG(self.m, B=c['B'], R=c['R'], PH=c['PV'], PV=c['PH'], X0=c['X0'], XH=c['XV'], XV=c['XH'])

    def aux(self):
        return {'X0': self.c['X0'], 'XH': self.c['XH'], 'XV': self.c['XV']}

    def profile(self):
        z = {k: size(v) for k, v in self.c.items()}
        return (z['B'] + z['R'], z['R'], z['X0'] + z['XH'] + z['XV'], z['X0'], z['XH'], z['XV'])


def from_phys(G):
    return SG(G.m, **{k: blk(v, G.m) for k, v in G.S.items()})


def _main(L, R):
    c = cross; m = L.m + R.m; u = lambda *a: uni(list(a), m)
    return dict(B=u(c(L['B'], R['B']), c(L['PH'], R['XH']), c(L['PV'], R['XV']), c(L['XH'], R['PV']), c(L['XV'], R['PH'])),
                R=u(c(L['R'], R['X0']), c(L['X0'], R['R'])),
                PH=u(c(L['PH'], R['X0']), c(L['X0'], R['PV'])),
                PV=u(c(L['PV'], R['X0']), c(L['X0'], R['PH'])))


def sgao(L, R):
    c = cross; m = L.m + R.m; u = lambda *a: uni(list(a), m)
    S = _main(L, R)
    S.update(X0=u(c(L['X0'], R['X0']), c(L['Xr'], R['Xr'])),
             XH=u(c(L['XH'], R['X0']), c(L['X0'], R['XV'])),
             XV=u(c(L['XV'], R['X0']), c(L['X0'], R['XH'])))
    return SG(m, **S)


def shetgao(L, R, J0, JH, JV):
    c = cross; m = L.m + R.m; u = lambda *a: uni(list(a), m)
    S = _main(L, R)
    ref = L['X0']
    JHq, JHn = spl(JH, ref, False), spl(JH, ref, True)
    JVq, JVn = spl(JV, ref, False), spl(JV, ref, True)
    S.update(X0=u(c(J0['X0'], R['X0']), c(JHq, R['XH']), c(JVq, R['XV'])),
             XH=u(c(J0['XH'], R['X0']), c(JVn, R['XV'])),
             XV=u(c(J0['XV'], R['X0']), c(JHn, R['XH'])))
    return SG(m, **S)


COMPS = [('B', 'B'), ('PH', 'XH'), ('PV', 'XV'), ('XH', 'PV'), ('XV', 'PH'), ('R', 'X0'), ('X0', 'R')]


def main_code(X, Y):
    return uni([cross(X[x], Y[y]) for x, y in COMPS], X.m + Y.m)


def jq(J, Lgad):
    """(|J|, |J minus N(X^0(L))|)"""
    return size(J), count_out(J, Lgad['X0'])


# ---------------- general per-coordinate automorphisms ----------------
from engine import dec as _dec
_AUTP = {}


def aut_perm(spec):
    """spec = ((pi, signs), c): y_j = s_j x_{pi(j)} + c_j (mod 7); returns the permutation of the 16807 codes"""
    key = repr(spec)
    if key not in _AUTP:
        (pi, sg), c = spec
        D = np.array([_dec(x) for x in range(N5)])
        Y = (D[:, list(pi)] * np.array(sg) + np.array(c)) % 7
        P = (Y * np.array([7 ** j for j in range(5)])).sum(1)
        assert len(set(P.tolist())) == N5
        _AUTP[key] = P
    return _AUTP[key]


_AA = {}


def aut_atom(a, spec):
    k = (a, repr(spec))
    if k not in _AA:
        m = np.zeros(N5, bool); m[aut_perm(spec)[_ATOMS[a]]] = True; _AA[k] = atom(m)
    return _AA[k]


_AX = {}


def Ax(s, specs):
    """apply automorphism specs[i] on unit i ('T' = Tan's T, 'I' = identity, else a spec)."""
    specs = tuple(specs)
    assert len(specs) == s.k
    key = (id(s), repr(specs))
    if key in _AX:
        return _AX[key]
    if all(x == 'I' for x in specs):
        r = s
    elif all(x == 'T' for x in specs):
        r = Tx(s)
    elif isinstance(s, Blk):
        def f(a, sp):
            return a if sp == 'I' else (aT(a) if sp == 'T' else aut_atom(a, sp))
        r = blk([tuple(f(a, sp) for a, sp in zip(b, specs)) for b in s.blocks], s.k)
    elif isinstance(s, Cross):
        r = cross(Ax(s.a, specs[:s.a.k]), Ax(s.b, specs[s.a.k:]))
    elif isinstance(s, Uni):
        r = uni([Ax(p, specs) for p in s.parts], s.k)
    else:
        r = spl(Ax(s.s, specs), Ax(s.r, specs), s.inside)
    _AX[key] = r
    return r


FAMKEY = {'B': 'B', 'N': 'X0', 'A': 'XV', 'D': 'XH', 'O': 'R', 'H': 'PH', 'V': 'PV'}


def flat_code(leaves, auts, words):
    """union over words w of prod_i aut_i(F_{w_i}(leaf_i)) as a trie of crosses (leaves: SG gadgets)"""
    memo = {}

    def rec(ws, i):
        key = (i, tuple(ws))
        if key in memo:
            return memo[key]
        g = defaultdict(list)
        for w in ws:
            g[w[i]].append(w)
        parts = []
        for l, sub in sorted(g.items()):
            G = leaves[i]
            f = Ax(G[FAMKEY[l]], auts[sum(x.m for x in leaves[:i]):sum(x.m for x in leaves[:i + 1])])
            parts.append(f if i == len(leaves) - 1 else cross(f, rec(sub, i + 1)))
        r = uni(parts, sum(x.m for x in leaves[i:]))
        memo[key] = r
        return r
    return rec(sorted(words), 0)

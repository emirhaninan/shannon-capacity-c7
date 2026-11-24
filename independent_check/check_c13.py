#!/usr/bin/env python3
"""Independent re-check of Theta(C13) >= 6.302930359067765 (re-classification claim).
Written from the definitions (BPZ Layered.lean: Realisation = independent families, Sep for sep pairs;
Subst admissible; Code pairwise separated).  Reads only the raw Lean data files."""
import re, sys, itertools, math
from collections import defaultdict
import numpy as np
sys.set_int_max_str_digits(0)
import os
HERE = os.path.dirname(os.path.abspath(__file__))
DIRS = [os.path.join(HERE, '..', 'c13', 'data', 'bpz'), os.path.join(HERE, '..', 'c13', 'data', 'long'), os.path.join(HERE, '..', 'c13')]
L = 'BNADOHV'; ix = {c: i for i, c in enumerate(L)}
# sep table copied from PortRealisation.lean (fetched from BPZ's public repo)
SEPP = ['BO','BH','BV','NA','ND','NO','NH','NV','AD','AH','DV']
sepm = np.zeros((7, 7), bool)
for p in SEPP: sepm[ix[p[0]], ix[p[1]]] = sepm[ix[p[1]], ix[p[0]]] = True
sigma = {'A': 'D', 'D': 'A', 'H': 'V', 'V': 'H', 'B': 'B', 'N': 'N', 'O': 'O'}
for a in L:
    for b in L: assert sepm[ix[a], ix[b]] == sepm[ix[sigma[a]], ix[sigma[b]]]

def readf(f): return open(next(os.path.join(d, f) for d in DIRS if os.path.exists(os.path.join(d, f)))).read()
# ---- tables ----
def words_in(s): return [''.join(re.findall(r'[BNADOHV]', w)) for w in re.findall(r'!\[([^\]]*)\]', s)]
TAB = {}
src = readf('Substitutions.lean')
for m in re.finditer(r'def T(\w+) : Letter → Finset \(Fin (\d) → Letter\)\n(.*?)\n/--', src, re.S):
    name, q, body = 'S' + m.group(1), int(m.group(2)), m.group(3)
    parts = re.split(r'\|\s*\.?([BNADOHV])\s*=>', body)
    t = {parts[i]: words_in(parts[i + 1]) for i in range(1, len(parts), 2)}
    assert set(t) == set(L) and all(len(w) == q for v in t.values() for w in v), name
    TAB[name] = t
CODE = {}
src = readf('TerminalCodes.lean')
for m in re.finditer(r'def C(\w+) : Finset \(Fin (\d) → Letter\) :=\n(.*?)\n/--', src, re.S):
    CODE['K' + m.group(1)] = words_in(m.group(3))
def wsep(u, v): return any(sepm[ix[a], ix[b]] for a, b in zip(u, v))
for nm, t in TAB.items():
    for a in L:
        assert len(set(t[a])) == len(t[a])
        for u, v in itertools.combinations(t[a], 2): assert wsep(u, v), (nm, a, u, v)
        for b in L:
            if sepm[ix[a], ix[b]]:
                for u in t[a]:
                    for v in t[b]: assert wsep(u, v), (nm, a, b)
for nm, K in CODE.items():
    for u, v in itertools.combinations(K, 2): assert wsep(u, v)
print('tables', {k: sum(len(v) for v in t.values()) for k, t in TAB.items()}, 'codes', {k: len(v) for k, v in CODE.items()})

# ---- base on C13^6 ----
src = readf('BaseC13Data.lean')
def lst(nm): return [int(x) for x in re.search(r'def %s : List Nat := \[(.*?)\]' % nm, src, re.S).group(1).replace('\n', ' ').split(',') if x.strip()]
n = 13; NW = n ** 6
idx = np.arange(NW, dtype=np.int64)
dig = [(idx // n ** (5 - j)) % n for j in range(6)]   # u = mk6 a b c d e f, a leading
a, b, c, d, e, f = dig
synv = (((b + 11 * a) % 13) * 13 + (d + 2 * c) % 13) * 2197 + (e % 13) * 13 + (f + 12 * a) % 13
# NB packS(p,q,r,s) = ((p*13+q)*13+r)*13+s
synv = ((((b + 11 * a) % 13) * 13 + (d + 2 * c) % 13) * 13 + e % 13) * 13 + (f + 12 * a) % 13
def setof(nm): return np.isin(synv, np.array(lst(nm)))
I, X, P0, P1 = setof('Sraw'), setof('SXraw'), setof('SPraw'), setof('SAraw')
print('|I|,|X|,|P0|,|P1|', I.sum(), X.sum(), P0.sum(), P1.sum())
def nbcount(m):  # number of closed-neighbours in m, for every word (strong product: each coord diff in {-1,0,1})
    A = m.reshape((n,) * 6).astype(np.int32)
    for ax in range(6): A = np.roll(A, 1, ax) + A + np.roll(A, -1, ax)
    return A.reshape(-1)
def near(m): return nbcount(m) > 0
nP0, nP1 = near(P0), near(P1)
# realisation (orientation used by the claim): O=H=parents, V=alternatives, A = X near V, D = X near H
def fams(orient):
    F = {'B': I & ~P0, 'O': P0.copy()}
    if orient == 0: F['H'], F['V'], F['A'], F['D'] = P0, P1, X & nP1, X & nP0
    else:           F['H'], F['V'], F['A'], F['D'] = P1, P0, X & nP0, X & nP1   # sigma image
    F['N'] = X & ~F['A'] & ~F['D']
    return F
def check_real(F):
    for l in L:
        assert (nbcount(F[l])[F[l]] == 1).all(), ('not independent', l)
    nr = {l: near(F[l]) for l in L}
    for p in SEPP: assert not (nr[p[0]] & F[p[1]]).any(), ('not separated', p)
    return nr
Fs = {}
for o in (0, 1):
    F = fams(o); nr = check_real(F)
    Fs[o] = (F, nr)
    print('orientation', o, 'realisation OK, sizes', tuple(int(F[l].sum()) for l in L))
# flag table: for each family, Counter over 7-bit near-masks
def base_flags(F, nr):
    fl = np.zeros(NW, np.int64)
    for l in L: fl |= nr[l].astype(np.int64) << ix[l]
    return {l: {int(k): int(v) for k, v in zip(*np.unique(fl[F[l]], return_counts=True))} for l in L}

# ---- schedules ----
def parse_sched(fname):
    s = readf(fname)
    ab = dict(re.findall(r'abbrev (\w+) : (?:Subst|Code) Letter Letter\.sep \d := (?:Substitutions|TerminalCodes)\.(\w+)', s))
    rule = {}
    for m in re.finditer(r'def R(\w+) \(R : Realisation[^\n]*\n[^\n]*:=\s*Realisation\.multiSubst e(\w+) \(ch(\w+) R\) ([\w.]+)', s, re.S):
        assert m.group(1) == m.group(2) == m.group(3)
        r = m.group(4).split('.')[-1]; rule[m.group(1)] = ab.get(r, r)
    ch = {}
    for m in re.finditer(r'def ch(\w+) \(R : Realisation[^\n]*\n[^\n]*:=\n(.*?)\n\n', s, re.S):
        ch[m.group(1)] = [t if t in ('R1', 'Rf') else t[1:] for t in re.findall(r'\(?(R\w+) R\)?', m.group(2))]
    tm = re.search(r'def terminalChildren \(R[^\n]*\n[^\n]*:=\n(.*?)\n\n', s, re.S).group(1)
    term = [t if t in ('R1', 'Rf') else t[1:] for t in re.findall(r'\(?(R\w+) R\)?', tm)]
    K = re.search(r'le_indepNum_multiCode eT \(terminalChildren [^)]*\) (\w+)', s).group(1); K = ab.get(K, K)
    M = int(re.search(r'def M : Nat :=\s*(\d+)', s).group(1))
    E = int(re.search(r'strongPower G (\d+)\)\.indepNum', s).group(1))
    for x in ch: assert len(ch[x]) == len(TAB[rule[x]]['B'][0]), x
    return rule, ch, term, K, M, E
def dims(rule, ch):
    dm = {'R1': 1, 'Rf': 1}
    def g(x):
        if x not in dm: dm[x] = sum(g(c) for c in ch[x])
        return dm[x]
    for x in ch: g(x)
    return dm

def sizes_eval(sched, w):
    rule, ch, term, K, M, E = sched
    wf = tuple(w[ix[sigma[l]]] for l in L)
    val = {'R1': w, 'Rf': wf}
    def g(x):
        if x not in val:
            vs = [g(c) for c in ch[x]]; t = TAB[rule[x]]
            val[x] = tuple(sum(math.prod(vs[i][ix[w_[i]]] for i in range(len(w_))) for w_ in t[l]) for l in L)
        return val[x]
    return sum(math.prod(g(term[i])[ix[w_[i]]] for i in range(len(w_))) for w_ in CODE[K])

def iroot_digits(M, p, digits=15):
    lo, hi = 0, 10 ** (digits + 2)
    T = M * 10 ** (digits * p)
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if mid ** p <= T: lo = mid
        else: hi = mid
    return f'{lo // 10**digits}.{lo % 10**digits:0{digits}d}'

w0 = tuple(int(Fs[0][0][l].sum()) for l in L)
bpz = parse_sched('CertC13.lean'); lng = parse_sched('CertC13b.lean')
for nm, sc in (('BPZ CertC13', bpz), ('Long CertC13b', lng)):
    dm = dims(sc[0], sc[1]); E = sum(dm[t] for t in sc[2])
    Mv = sizes_eval(sc, w0)
    print(nm, 'nodes', len(sc[1]), 'E', E, sc[5], 'M reproduced:', Mv == sc[4], 'rate', iroot_digits(Mv, 6 * E))

# ---- flag DP (own implementation) ----
HVO = (1 << ix['H']) | (1 << ix['V']) | (1 << ix['O'])
def substitute(t, kids):
    """kids: list of flag tables. returns flag table of the substituted realisation (exact relative to kids' flags)."""
    q = len(kids)
    blocks = {l: [[ix[ch_] for ch_ in w_] for w_ in t[l]] for l in L}
    memo = {}
    def flag(ftuple):
        r = memo.get(ftuple)
        if r is None:
            r = 0
            for l in L:
                for w_ in blocks[l]:
                    if all((ftuple[i] >> w_[i]) & 1 for i in range(q)):
                        r |= 1 << ix[l]; break
            memo[ftuple] = r
        return r
    out = {}
    for l in L:
        acc = defaultdict(int)
        for w_ in blocks[l]:
            lists = [list(kids[i][L[w_[i]]].items()) for i in range(q)]
            for combo in itertools.product(*lists):
                acc[flag(tuple(x[0] for x in combo))] += math.prod(x[1] for x in combo)
        out[l] = dict(acc)
    return out
def move(tab):
    """move A/D words whose flag misses H,V,O into N; return new table with widened flags, moved count"""
    new = {l: defaultdict(int) for l in L}; moved = {'A': 0, 'D': 0}
    for l in L:
        for fl, cnt in tab[l].items():
            tgt = 'N' if (l in 'AD' and not fl & HVO) else l
            if tgt != l: moved[l] += cnt
            new[tgt][fl] += cnt
    def widen(fl):
        g = fl
        if moved['A'] and fl >> ix['A'] & 1: g |= 1 << ix['N']
        if moved['D'] and fl >> ix['D'] & 1: g |= 1 << ix['N']
        return g
    out = {}
    for l in L:
        acc = defaultdict(int)
        for fl, cnt in new[l].items(): acc[widen(fl)] += cnt
        out[l] = dict(acc)
    return out, moved['A'] + moved['D']
def sz(tab): return tuple(sum(tab[l].values()) for l in L)

def run(sched, base_tab, internal, terminal_reclass=True, verbose=False):
    rule, ch, term, K, M, E = sched
    sigtab = {l: {sum(1 << ix[sigma[L[j]]] for j in range(7) if fl >> j & 1): c for fl, c in base_tab[sigma[l]].items()} for l in L}
    val = {'R1': base_tab, 'Rf': sigtab}
    def g(x):
        if x not in val:
            t = substitute(TAB[rule[x]], [g(c) for c in ch[x]])
            if x in internal:
                t, mv = move(t)
                if verbose: print('   moved at', x, mv)
            val[x] = t
        return val[x]
    vecs = []
    for tchild in term:
        t = g(tchild)
        if terminal_reclass:
            t, mv = move(t)
            if verbose: print('   moved at terminal', tchild, mv)
        vecs.append(sz(t))
    return sum(math.prod(vecs[i][ix[w_[i]]] for i in range(len(w_))) for w_ in CODE[K])

claimed = int(readf('certificate.txt').strip())
for o in (0, 1):
    bt = base_flags(*Fs[o])
    assert sz(bt) == w0
    M0 = run(lng, bt, set(), terminal_reclass=False)
    assert M0 == lng[4], 'flag DP sizes must reproduce Long'
    Mt = run(lng, bt, set(), True)
    Mn = run(lng, bt, {'n5', 'n12', 'n16', 'n20', 'n34', 'n36'}, True, verbose=(o == 0))
    print(f'orientation {o}: terminal-only {iroot_digits(Mt, 522)}; claimed node set {iroot_digits(Mn, 522)};'
          f' equals claimed M: {Mn == claimed}; > Long: {Mn > lng[4]}')
print('claimed file rate', iroot_digits(claimed, 522), 'digits', len(str(claimed)))

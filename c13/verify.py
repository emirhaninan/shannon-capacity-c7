#!/usr/bin/env python3
"""Exact verification of Theta(C13) >= M^(1/522) = 6.302930359067765...

Usage: python3 verify.py   (about 30 seconds)

Standalone exact checker:  Theta(C13) >= M^(1/522) with M from re-classified auxiliary families.

Inputs (read from the repository, nothing else):
  data/bpz/BaseC13Data.lean, Substitutions.lean, TerminalCodes.lean, CertC13.lean  (BPZ, Apache-2.0)
  data/long/CertC13b.lean                                                           (G. Long, Apache-2.0)
Steps
  1. BPZ base port system on C13^6 rebuilt from the raw syndrome lists; every RichPortSystem condition and every
     separation of the seven families checked by brute force on all 13^6 words.
  2. Substitution tables / terminal code parsed from BPZ's Lean files; admissibility re-checked independently.
  3. Controls: BPZ's CertC13 M and Long's CertC13b M reproduced digit for digit from the parsed schedules.
  4. Exact neighbourhood-flag tables propagated through Long's schedule (base realisation = sigma-relabelled BPZ
     base, which is again a port realisation); auxiliary words of families A, D whose flags show no conflict
     with H, V, O are moved to N at the listed internal nodes (flags of the parent conservatively widened) and at
     the three terminal children.  The new sizes are fed to the same terminal code K3a.
  5. Exact comparison with the previous records; decimal lower bound by exact integer root.
Python 3 + numpy.  About 30 s.
"""
import re, os, sys, itertools, math, time
from collections import defaultdict
import numpy as np
sys.set_int_max_str_digits(0)
t0 = time.time()
H_ = os.path.dirname(os.path.abspath(__file__))
BPZ = os.path.join(H_, 'data', 'bpz'); LONG = os.path.join(H_, 'data', 'long')
rd = lambda d, f: open(os.path.join(d, f)).read()
LAB = 'BNADOHV'; IX = {l: i for i, l in enumerate(LAB)}
SEP = {frozenset(p) for p in ['BO', 'BH', 'BV', 'NA', 'ND', 'NO', 'NH', 'NV', 'AD', 'AH', 'DV']}
sep = lambda a, b: frozenset((a, b)) in SEP
SIG = {'B': 'B', 'N': 'N', 'A': 'D', 'D': 'A', 'O': 'O', 'H': 'V', 'V': 'H'}
# the separation relation of PortRealisation.lean, re-read from BPZ's file when present
pr = os.path.join(BPZ, 'PortRealisation.lean')
if os.path.exists(pr):
    blk = rd(BPZ, 'PortRealisation.lean').split('def sep : Letter → Letter → Bool')[1].split('| _, _ => false')[0]
    S2 = {frozenset(p) for p in re.findall(r'\b([BNADOHV]), ([BNADOHV]) => true', blk)}
    assert S2 == SEP, 'separation relation differs from BPZ'
assert all(sep(SIG[a], SIG[b]) == sep(a, b) for a in LAB for b in LAB)       # sigma is an automorphism

# ---------------- 2. tables ----------------
def parse_tables():
    src = rd(BPZ, 'Substitutions.lean'); T = {}
    for m in re.finditer(r'def (T\d[a-z]) : Letter → Finset \(Fin \d → Letter\)(.*?)\n\n', src, re.S):
        tab = {}
        for lm in re.finditer(r'\|\s*\.?([BNADOHV])\s*=>(.*?)(?=\|\s*\.?[BNADOHV]\s*=>|$)', m.group(2), re.S):
            tab[lm.group(1)] = [''.join(re.findall(r'[BNADOHV]', w)) for w in re.findall(r'!\[(.*?)\]', lm.group(2))]
        T['S' + m.group(1)[1:]] = tab
    src = rd(BPZ, 'TerminalCodes.lean'); K = {}
    for m in re.finditer(r'def (C\d[a-z]) : Finset \(Fin \d → Letter\) :=(.*?)\n\n', src, re.S):
        K['K' + m.group(1)[1:]] = [''.join(re.findall(r'[BNADOHV]', w)) for w in re.findall(r'!\[(.*?)\]', m.group(2))]
    return T, K
RULES, CODES = parse_tables()
wsep = lambda u, v: any(sep(a, b) for a, b in zip(u, v))
for nm, R in RULES.items():
    assert all(wsep(u, v) for l in LAB for u, v in itertools.combinations(R[l], 2)), nm
    assert all(wsep(u, v) for l, m_ in itertools.combinations(LAB, 2) if sep(l, m_) for u in R[l] for v in R[m_]), nm
for nm, K in CODES.items(): assert all(wsep(u, v) for u, v in itertools.combinations(K, 2)), nm
print(f'[ok] {len(RULES)} substitution tables admissible, {len(CODES)} terminal codes pairwise separated', flush=True)

# ---------------- 1. base port system ----------------
n, k = 13, 6; N = n ** k
src = rd(BPZ, 'BaseC13Data.lean')
lst = lambda nm: [int(x) for x in re.search(r'def %s : List Nat := \[(.*?)\]' % nm, src, re.S).group(1).replace('\n', ' ').split(',') if x.strip()]
S, SX, SP, SA = lst('Sraw'), lst('SXraw'), lst('SPraw'), lst('SAraw')
u = np.arange(N); W = np.stack([(u // 13 ** (5 - j)) % 13 for j in range(6)], 1)       # w0 = leading digit (BPZ mk6)
a_, b_, c_, d_, e_, f_ = W.T
syn = ((((b_ + 11 * a_) % 13) * 13 + (d_ + 2 * c_) % 13) * 13 + e_ % 13) * 13 + (f_ + 12 * a_) % 13   # BPZ synD
I = np.isin(syn, S); X = np.isin(syn, SX); P0 = np.isin(syn, SP); P1 = np.isin(syn, SA)
assert I.sum() == X.sum() == 62530 and P0.sum() == P1.sum() == 1014
def cover(m):
    a = m.reshape((n,) * k).astype(np.int16)
    for ax in range(k): a = a + np.roll(a, 1, ax) + np.roll(a, -1, ax)
    return a.reshape(-1)
dil = lambda m: cover(m) > 0
cI = cover(I)
assert (cI[I] == 1).all() and (cover(X)[X] == 1).all(), 'I or X not independent'
assert (P0 <= I).all() and not (P1 & I).any(), 'parents must lie in I, alternatives outside'
OFF = np.array(list(itertools.product((-1, 0, 1), repeat=6))); pw = 13 ** np.arange(5, -1, -1)
par = {}
for q in np.nonzero(P1)[0]:
    nb = ((W[q] + OFF) % 13) @ pw; pi = nb[I[nb]]
    assert len(pi) == 1 and P0[pi[0]], 'alternative not private to a parent'
    par[int(q)] = int(pi[0])
assert len(set(par.values())) == 1014, 'parents not distinct'
assert (cover(P0)[P0] == 1).all() and (cover(P1)[P1] == 1).all(), 'transversals not independent'
nP0, nP1 = dil(P0), dil(P1)
assert not (X & nP0 & nP1).any(), 'an auxiliary word conflicts with both transversals'
print('[ok] BPZ C13 port system: |I| = |X| = 62530, 1014 private pairs, independent transversals, disjoint footprints', flush=True)
# realisation used here: sigma of BPZ's (H = parents P0, V = alternatives P1, A = X near V, D = X near H)
F = {'B': I & ~P0, 'O': P0, 'H': P0, 'V': P1}
F['A'] = X & nP1; F['D'] = X & nP0; F['N'] = X & ~F['A'] & ~F['D']
F['O'] = P0.copy()
for l in LAB:
    assert (cover(F[l])[F[l]] == 1).all(), l
for p in SEP:
    a, b = tuple(p); assert not (dil(F[a]) & F[b]).any(), ('families not separated', a, b)
w0 = tuple(int(F[l].sum()) for l in LAB)
print('[ok] seven families pairwise separated as required, sizes', w0, flush=True)
# NB: O = H here (ports = parents, and H is the parent transversal) - allowed: O and H are not separated.

# ---------------- 3. schedules and controls ----------------
def rule(R, vs): return tuple(sum(math.prod(v[IX[c]] for c, v in zip(w, vs)) for w in R[l]) for l in LAB)
def code(K, vs): return sum(math.prod(v[IX[c]] for c, v in zip(w, vs)) for w in K)
sigv = lambda x: tuple(x[IX[SIG[l]]] for l in LAB)
def parse_long(path):
    s = open(path).read(); doc = s.split('Schedule (')[1].split('-/')[0]; nodes = []
    for ln in doc.split('\n'):
        ln = ln.strip()
        m = re.match(r'(n\d+) = (S\w+)\((.*)\)$', ln)
        if m: nodes.append((m.group(1), m.group(2), [c.strip() for c in m.group(3).split(',')])); continue
        assert not re.match(r'n\d+ = \d+ x', ln), 'tails not used in this schedule'
        m = re.match(r'M = (K\w+)\((.*)\)$', ln)
        if m: term = (m.group(1), [c.strip() for c in m.group(2).split(',')])
    M = int(re.search(r'def M : Nat :=\s*(\d+)', s).group(1)); E = int(re.search(r'strongPower G (\d+)\)\.indepNum', s).group(1))
    return nodes, term, M, E
def parse_bpz(path):
    s = open(path).read()
    ab = dict(re.findall(r'abbrev (\w+) : (?:Subst|Code) Letter Letter\.sep \d := (?:Substitutions|TerminalCodes)\.(\w+)', s))
    ch = {m.group(1): re.findall(r'(?:\(|=> )(R1|R\w+) R\b', m.group(2)) for m in re.finditer(r'def ch(\w+) \(R : Realisation[^\n]*\n[^\n]*:=\n\s*(.*?)\n\n', s, re.S)}
    ru = {m.group(1): ab[m.group(2)] for m in re.finditer(r'def R(\w+) \(R : Realisation[^\n]*\n[^\n]*:=\n\s*Realisation\.multiSubst e\1 \(ch\1 R\) (\w+)', s)}
    term = re.findall(r'(?:\(|=> )(R1|R\w+) R\b', re.search(r'def terminalChildren.*?:=\n\s*(.*?)\n\n', s, re.S).group(1))
    K = ab[re.search(r'le_indepNum_multiCode eT \(terminalChildren [^)]*\) (\w+)', s).group(1)]
    M = int(re.search(r'def M : Nat :=\s*(\d+)', s).group(1)); E = int(re.search(r'strongPower G (\d+)\)\.indepNum', s).group(1))
    nm = lambda c: 'R1' if c == 'R1' else c[1:]
    order = []; seen = set()
    def visit(x):
        if x == 'R1' or x in seen: return
        for c in ch[x]: visit(nm(c))
        seen.add(x); order.append(x)
    for t in term: visit(nm(t))
    return [(x, ru[x], [nm(c) for c in ch[x]]) for x in order], (K, [nm(t) for t in term]), M, E
def eval_sizes(sched, base):
    nodes, (K, tch), M, E = sched; val = {'R1': base, 'Rf': sigv(base)}
    for x, r, ch in nodes: val[x] = rule(RULES[r], [val[c] for c in ch])
    return code(CODES[K], [val[c] for c in tch])
w0bpz = sigv(w0)      # BPZ's own orientation (A = X near its P_false, ...): sizes are symmetric anyway
bpz = parse_bpz(os.path.join(BPZ, 'CertC13.lean')); lng = parse_long(os.path.join(LONG, 'CertC13b.lean'))
assert eval_sizes(bpz, w0bpz) == bpz[2] and bpz[3] == 87, 'BPZ CertC13 not reproduced'
assert eval_sizes(lng, w0bpz) == lng[2] and lng[3] == 87, 'Long CertC13b not reproduced'
print('[ok] controls: BPZ CertC13 M and Long CertC13b M reproduced exactly (E = 87, dimension 522)', flush=True)

# ---------------- 4. flag tables and re-classification ----------------
def base_table(F):
    fl = np.zeros(N, np.int64)
    for l in LAB: fl |= dil(F[l]).astype(np.int64) << IX[l]
    return {a: {int(f): int(c) for f, c in enumerate(np.bincount(fl[F[a]], minlength=128)) if c} for a in LAB}
def sig_table(D):
    pf = lambda f: sum(1 << IX[SIG[l]] for l in LAB if f >> IX[l] & 1)
    return {SIG[a]: {pf(f): c for f, c in D[a].items()} for a in LAB}
def combine(R, Ds):
    m = len(Ds); tabs = {l: [tuple(IX[c] for c in w) for w in R[l]] for l in LAB}; cache = {}
    def outflag(fs):
        if fs not in cache:
            cache[fs] = sum(1 << IX[l] for l in LAB if any(all(fs[i] >> w[i] & 1 for i in range(m)) for w in tabs[l]))
        return cache[fs]
    out = {}
    for a in LAB:
        acc = defaultdict(int)
        for w in R[a]:
            for combo in itertools.product(*[list(Ds[i][w[i]].items()) for i in range(m)]):
                acc[outflag(tuple(c[0] for c in combo))] += math.prod(c[1] for c in combo)
        out[a] = dict(acc)
    return out
hvo = (1 << IX['H']) | (1 << IX['V']) | (1 << IX['O'])
def reclass_internal(D):
    new = {a: dict(D[a]) for a in LAB}; mv = {'A': 0, 'D': 0}
    for a in 'AD':
        for f, c in D[a].items():
            if not f & hvo: del new[a][f]; new['N'][f] = new['N'].get(f, 0) + c; mv[a] += c
    def tf(f):
        g = f
        if mv['A'] and f >> IX['A'] & 1: g |= 1 << IX['N']
        if mv['D'] and f >> IX['D'] & 1: g |= 1 << IX['N']
        return g
    out = {}
    for a in LAB:
        acc = defaultdict(int)
        for f, c in new[a].items(): acc[tf(f)] += c
        out[a] = dict(acc)
    return out, mv['A'] + mv['D']
def size_vec(D): return tuple(sum(D[a].values()) for a in LAB)
def reclass_terminal(D):
    s = list(size_vec(D)); mv = 0
    for a in 'AD':
        for f, c in D[a].items():
            if not f & hvo: s[IX[a]] -= c; s[IX['N']] += c; mv += c
    return tuple(s), mv
INTERNAL = ['n5', 'n12', 'n16', 'n20', 'n34', 'n36']
D0 = base_table(F); assert size_vec(D0) == w0
nodes, (K, tch), Mlong, E = lng
val = {'R1': D0, 'Rf': sig_table(D0)}; sz = {'R1': w0, 'Rf': sigv(w0)}
for x, r, ch in nodes:
    T = combine(RULES[r], [val[c] for c in ch])
    assert size_vec(T) == rule(RULES[r], [sz[c] for c in ch]), 'flag table sizes disagree with the size recursion'
    if x in INTERNAL:
        T, mv = reclass_internal(T); print(f'     node {x}: {mv} auxiliary words moved to N', flush=True)
    val[x] = T; sz[x] = size_vec(T)
vecs = []
for c in tch:
    v, mv = reclass_terminal(val[c]); vecs.append(v); print(f'     terminal child {c}: {mv} auxiliary words moved to N', flush=True)
Mnew = code(CODES[K], vecs)
print('[ok] new construction: same schedule and terminal code K3a, dimension 6 * 87 = 522', flush=True)

# ---------------- 5. comparison ----------------
def root_floor(M, p, digits=15):
    lo, hi = 0, 10 ** (digits + 3)
    T = M * 10 ** (digits * p)
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if mid ** p <= T: lo = mid
        else: hi = mid
    return lo
d = 522
aL = root_floor(Mlong, d); aN = root_floor(Mnew, d)
print(f'    Long (CertC13b) : M^(1/522) >= {aL // 10**15}.{aL % 10**15:015d}')
print(f'    new             : M^(1/522) >= {aN // 10**15}.{aN % 10**15:015d}')
assert Mnew > Mlong
PROTTI = 6302927046770772      # Theta(C13) >= 6.302927046770772 (Protti v0.5.0, dimension 522)
assert aN > aL >= PROTTI
assert open(os.path.join(H_, 'certificate.txt')).read().strip() == str(Mnew), 'certificate.txt does not match'
print(f'OK  Theta(C13) >= {aN // 10**15}.{aN % 10**15:015d}  (M has {len(str(Mnew))} digits, matches certificate.txt;'
      f' previous best 6.302927071589786)   [{time.time() - t0:.0f}s]')

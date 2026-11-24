#!/usr/bin/env python3
"""Exact verification of Theta(C_7) >= M^(1/700) = 3.2588405876641976...

Usage: python3 verify.py   (about 7 minutes)

The construction combines three changes to the Gao/BPZ/Tandon product framework:
  (a) deeper nested left patterns (stage_nesting.py);
  (b) flat label-code side codebooks over k copies of G5 with per-coordinate automorphism s* (family_codes.json),
      and new flat codes for k = 7 (35 dimensions);
  (c) a multi-word exchange list J+ (exchanges.txt).
Data: construction.json (slots, codebooks), family_codes.json, exchanges.txt.

Steps
  1. stage_exchanges.py: first re-runs itself with Tang's exchange list and reproduces all 13 published
     Tandon/Tang counts and Tang's M, then proves the new J+ and J15' independent and certifies the exchange stage;
  2. stage_nesting.py: re-derives all counts with the chunk-summary DP and certifies the nesting stage;
  3. rebuilds the base data, reproduces the exchange-stage M exactly, proves every new flat codebook independent
     from the G5 families, counts j and q exactly by two independent methods, and evaluates the integer M;
  4. checks M against certificate.txt and compares rates exactly in integers.
"""
import os, sys, subprocess, json, time, math, itertools
os.chdir(os.path.dirname(os.path.abspath(__file__)))
t0 = time.time()
for scr, tag in [('stage_exchanges.py', 'OK'), ('stage_nesting.py', 'OK nesting stage')]:
    print(f'phase: {scr}', flush=True)
    r = subprocess.run([sys.executable, scr], capture_output=True, text=True)
    print('\n'.join('   | ' + l for l in r.stdout.splitlines()), flush=True)
    assert r.returncode == 0 and any(l.startswith(tag) for l in r.stdout.splitlines()), (scr, r.stderr[-3000:])
M5 = int(open('stage_exchanges_M.txt').read()); MD = int(open('stage_nesting_M.txt').read())
os.environ['C7_JPLUS'] = 'exchanges.txt'; os.environ['C7_J15'] = 'family_codes.json'
print('phase: stacked construction (J+ = exchanges.txt, J15\')', flush=True)
import numpy as np
from collections import defaultdict
from decimal import Decimal, getcontext
getcontext().prec = 60
from engine import *
from engine import _ATOMS
from flags import dist as fdist, tree_ind
import sym, symbase, prof as PF, jqc, flatlib
from sym import size as ssize, count_out as scount
# ---- base data (symbolic) ----
B = {'GAD': {}, 'GM': {}, 'PAT': {}, 'PM': {}}
for k, g in symbase.GAD.items(): B['GAD'][k] = g.profile(); B['GM'][k] = g.m
for k, (L_, J0_, JH_, JV_) in symbase.PAT.items():
    B['PAT'][k] = (L_.profile(), (ssize(J0_['X0']) + ssize(J0_['XH']) + ssize(J0_['XV']), ssize(J0_['X0']), ssize(J0_['XH']), ssize(J0_['XV'])),
                   (ssize(JH_), scount(JH_, L_['X0'])), (ssize(JV_), scount(JV_, L_['X0'])))
    B['PM'][k] = L_.m
PF.BASEDATA = B
c1 = scount(symbase.Jp, symbase.G10['X0']); c3 = scount(symbase.G15h['X'], symbase.G15X['X0'])
assert (ssize(symbase.Jp), c1, c3) == (134753, 27512, 14047245)
assert (ssize(symbase.J15), scount(symbase.J15, symbase.G15X['X0'])) == (49496015, 12843063)
print(f'  [ok] J+_d: |J+| = 134753, C1 = {c1}, C3 = {c3};  J15\' = (49496015, 12843063)', flush=True)
# ---- reproduce v5 M with the DP and the general recursion ----
D4 = json.load(open('family_codes.json'))
JQ5 = {}
for nm, sp in D4['patterns'].items():
    JQ5[nm] = jqc.getjq(nm, flatlib.from_json(sp))
    assert JQ5[nm][0] == sp['j'] and (JQ5[nm][1] == sp['q'] or 'sG15Ah' in nm)
g1 = 'H[N<S<G15AX,G5,P15A8>,G5>](G5)'
SL5 = ['H[N<N<S<G15AX,G5,P15A8>,G5>,G5>](G5)', 's(H[N<S<G15AX,sG15AX,P15A5>,sG15AX>](s(%s)))' % g1,
       's(H[N<S<G15AX,sG15Ah,P15A8>,sG15Ah>](s(H[P10A](G5))))']
assert PF.topM(*[PF.World(JQ5).gp(s) for s in SL5]) == M5
print('  [ok] DP + recursion reproduce the exchange-stage M exactly (all seven family-stage codebooks recounted with the new J+)', flush=True)
# ---- direct independence proof of flat codes (physical G5 families; as in v5) ----
G5p, _ = load_base()
FAMKEY = {'B': 'B', 'N': 'X0', 'A': 'XV', 'D': 'XH', 'O': 'R', 'H': 'PH', 'V': 'PV'}
SC = {}
def cs(a, c):
    if (a, c) not in SC:
        ma, mc = _ATOMS[a], _ATOMS[c]; conf = bool((ma & anb(c)).any()); st = False
        if conf:
            s = mc.reshape((7,) * 5).astype(np.int16)
            for ax in range(5): s = s + np.roll(s, 1, ax) + np.roll(s, -1, ax)
            st = bool((ma & ((s.reshape(-1) - mc.astype(np.int16)) > 0)).any())
        SC[(a, c)] = (conf, st)
    return SC[(a, c)]
def flg(S, S2):
    m = len(S[0]) if S else 0; best = [False, False]
    def rec(A, Bq, i, st):
        if best[1]: return
        if i == m: best[0] = True; best[1] |= st; return
        ga = defaultdict(list); gb = defaultdict(list)
        for p in A: ga[p[i]].append(p)
        for p in Bq: gb[p[i]].append(p)
        for a, la in ga.items():
            for c, lb in gb.items():
                ci, si = cs(a, c)
                if ci:
                    rec(la, lb, i + 1, st or si)
                    if best[1]: return
    if S and S2: rec(S, S2, 0, False)
    return best[0], best[1]
def leaf_blocks(aut, lab):
    bl = G5p[FAMKEY[lab]]
    if aut == 'T': return Tset(bl)
    return [tuple(sym.aut_atom(a, aut) for a in b) for b in bl]
def prove_flat(auts, words):
    labs = sorted({c for w in words for c in w}); CF = []
    for aut in auts:
        Bl = {l: leaf_blocks(aut, l) for l in labs}
        for l in labs:
            if not Bl[l]: continue
            check_disjoint_fast(Bl[l]); c, st = flg(Bl[l], Bl[l]); assert c and not st, ('family not independent', l)
        CF.append({(x, y): (flg(Bl[x], Bl[y])[0] if Bl[x] and Bl[y] else False) for x in labs for y in labs})
    assert len(set(words)) == len(words)
    W = np.array([[labs.index(c) for c in w] for w in words], dtype=np.int64); n = len(words); k = W.shape[1]
    Mx = [np.array([[CF[i][(x, y)] for y in labs] for x in labs]) for i in range(k)]
    for s in range(0, n, 512):
        acc = np.ones((min(512, n - s), n), bool)
        for i in range(k): acc &= Mx[i][W[s:s + 512, i][:, None], W[None, :, i]]
        acc[np.arange(acc.shape[0]), np.arange(s, s + acc.shape[0])] = False
        assert not acc.any(), 'two distinct words not separated'
# ---- second count: per-coordinate flag tensors (pure-Gao references of base coordinates) ----
xr = _ATOMS[G5p['XH'][0][0]] | _ATOMS[G5p['XV'][0][0]]; NX0 = anb(G5p['X0'][0][0]); NXr = dilate(xr)
def flat_tensor(auts, words):
    vt = [{} for _ in auts]
    def v(i, l):
        if l not in vt[i]: vt[i][l] = fdist(leaf_blocks(auts[i], l), NX0, NXr, T=False)
        return vt[i][l]
    def rec(ws, i):
        if i == len(auts): return np.array(1, dtype=object)
        g = defaultdict(list)
        for w in ws: g[w[i]].append(w)
        tot = None
        for l, sub in g.items():
            t = np.multiply.outer(v(i, l), rec(sub, i + 1)); tot = t if tot is None else tot + t
        return tot
    return rec(sorted(words), 0)
b = 'b'
CT = {'G5': b, 'sG5': b, 'G10': (b, b), 'G10A': (b, b), 'G10D': (b, b), 'sG10A': (b, b), 'sG10D': (b, b),
      'G15X': ((b, b), b), 'G15AX': ((b, b), b), 'sG15AX': ((b, b), b)}
def ptree(nm):
    nm = PF.norm_pat(nm)
    if nm.startswith('P10'): return (b, b)
    if nm.startswith('P15'): return ((b, b), b)
    q, c = PF.split_top(nm[2:-1]); return (ptree(q), CT[c])
# ---- the new chains ----
SPEC = json.load(open('construction.json'))
CODES = {int(k): v for k, v in SPEC['codes'].items()}
def tau(a): return a if a == 'T' else ((tuple(a[0][0]), tuple(a[0][1])), tuple(a[1]))
JQ6 = {}
for nm, sp in SPEC['patterns'].items():
    t1 = time.time(); k = sp['k']; words = CODES[k]; auts = [tau(a) for a in sp['auts']]
    prove_flat(auts, words)
    J = flatlib.build(('flat', tuple(words), tuple(auts))); L_ = jqc.pleft(nm); assert J.k == L_.m == k
    j, q = ssize(J), scount(J, L_['X0'])
    t = flat_tensor(auts, words); j2 = int(t.sum()); q2 = int(t[~tree_ind(ptree(nm))[0]].sum())
    assert (j, q) == (j2, q2) == (sp['j'], sp['q']), (nm, j, q, j2, q2, sp['j'], sp['q'])
    JQ6[PF.norm_pat(nm)] = (j, q)
    print(f'  [ok] {nm}: J = sigma(flat label code, {len(words)} words over G5^{k}; automorphisms '
          f'{sorted(set("T" if a == "T" else "s*" for a in auts))}) independent; j = {j}, q = {q} (two methods, {time.time() - t1:.0f}s)', flush=True)
def dim(sl): return 20 * sum(PF.gdim(s) for s in sl)
def certify(sl, label):
    W = PF.World(JQ6); M = PF.topM(*[W.gp(s) for s in sl]); d = dim(sl)
    for nm in JQ6: assert W.pp(nm)[2] == JQ6[nm]
    return M, d
SL6 = SPEC['slots']
M6, d6 = certify(SL6, 'v6')
rate = lambda M, d: (Decimal(M).ln() / d).exp()
gt = lambda M1, d1, M2, d2: M1 ** d2 > M2 ** d1      # exact: M1^(1/d1) > M2^(1/d2)
assert gt(M6, d6, M5, 680) and gt(M6, d6, MD, 680)
assert open('certificate.txt').read().split() == [str(d6), str(M6)], 'certificate.txt does not match'
print(f'\nd = {d6}\nM = {M6}\n')
print(f'CERTIFIED (given Tandon\'s Theorem 1 and the Gao/BPZ lemmas)  Theta(C_7) >= M^(1/{d6}) = {str(rate(M6, d6))[:18]}...')
print(f'nesting stage (d = 680)                                 {str(rate(MD, 680))[:18]}...   exceeded (exact): True')
print(f'exchange stage (d = 680)                                {str(rate(M5, 680))[:18]}...   exceeded (exact): True')
print('OK: certificate.txt verified  (%.0fs)' % (time.time() - t0))

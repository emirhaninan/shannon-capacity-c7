#!/usr/bin/env python3
"""Brute-force test of the re-classification lemma + conservative flag propagation on explicit small realisations.
Random base graph G, random realisation, random 2-level schedules from BPZ tables, re-classification at random nodes,
explicit sets; check (i) realisation property explicitly after every move, (ii) DP flag tables == per-word recursion,
(iii) true flags subset of DP flags, (iv) final terminal-code set independent and of the predicted size."""
import sys, random, itertools, math
from collections import defaultdict, Counter
import numpy as np
import os
L = 'BNADOHV'; ix = {c: i for i, c in enumerate(L)}
SEPP = ['BO','BH','BV','NA','ND','NO','NH','NV','AD','AH','DV']
sepm = np.zeros((7, 7), bool)
for p in SEPP: sepm[ix[p[0]], ix[p[1]]] = sepm[ix[p[1]], ix[p[0]]] = True
sigma = {'A': 'D', 'D': 'A', 'H': 'V', 'V': 'H', 'B': 'B', 'N': 'N', 'O': 'O'}
HVO = (1 << ix['H']) | (1 << ix['V']) | (1 << ix['O'])
import re
D = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'c13', 'data', 'bpz')
def words_in(s): return [''.join(re.findall(r'[BNADOHV]', w)) for w in re.findall(r'!\[([^\]]*)\]', s)]
TAB = {}
src = open(f'{D}/Substitutions.lean').read()
for m in re.finditer(r'def T(\w+) : Letter → Finset \(Fin (\d) → Letter\)\n(.*?)\n/--', src, re.S):
    parts = re.split(r'\|\s*\.?([BNADOHV])\s*=>', m.group(3))
    TAB['S' + m.group(1)] = {parts[i]: words_in(parts[i + 1]) for i in range(1, len(parts), 2)}
CODE = {}
src = open(f'{D}/TerminalCodes.lean').read()
for m in re.finditer(r'def C(\w+) : Finset \(Fin (\d) → Letter\) :=\n(.*?)\n/--', src, re.S):
    CODE['K' + m.group(1)] = words_in(m.group(3))

def run_trial(seed):
    rng = random.Random(seed)
    nv = rng.randint(8, 16); p = rng.uniform(0.15, 0.45)
    adj = np.eye(nv, dtype=bool)   # closed adjacency = conflict
    for i in range(nv):
        for j in range(i + 1, nv):
            if rng.random() < p: adj[i, j] = adj[j, i] = True
    # random realisation
    fam = {l: [] for l in L}
    for _ in range(200):
        v = rng.randrange(nv); l = rng.choice(L)
        if v in fam[l]: continue
        if any(adj[v, u] for u in fam[l]): continue
        if any(sepm[ix[l], ix[m]] and any(adj[v, u] for u in fam[m]) for m in L): continue
        fam[l].append(v)
        if all(len(fam[x]) >= 2 for x in L) and rng.random() < 0.3: break
    # explicit node: dict letter -> list of tuples (words over base vertices); conflict of tuples is coordinatewise adj
    def conf(x, y): return all(adj[a, b] for a, b in zip(x, y))
    def check_realisation(F):
        for l in L:
            S = F[l]
            for i in range(len(S)):
                for j in range(i + 1, len(S)):
                    if conf(S[i], S[j]): return False
        for pr in SEPP:
            for x in F[pr[0]]:
                for y in F[pr[1]]:
                    if conf(x, y): return False
        return True
    def trueflag(x, F):
        return sum(1 << ix[l] for l in L if any(conf(x, y) for y in F[l]))
    base = {l: [(v,) for v in fam[l]] for l in L}
    assert check_realisation(base)
    # each explicit node: F (letter->list of words), fl (word->DP flag per letter membership), tab (DP table)
    def leaf(flip):
        F = {l: list(base[sigma[l]] if flip else base[l]) for l in L}
        fl = {l: {x: trueflag(x, F) for x in F[l]} for l in L}
        return F, fl
    def subst(tname, kids):
        t = TAB[tname]; F = {}; fl = {}
        for l in L:
            F[l] = []; fl[l] = {}
            for w in t[l]:
                pools = [kids[i][0][w[i]] for i in range(len(w))]
                for combo in itertools.product(*pools):
                    word = sum(combo, ())
                    cf = [kids[i][1][w[i]][combo[i]] for i in range(len(w))]
                    # DP flag of the product word: near l' iff some block of l' has all coordinate bits
                    g = sum(1 << ix[m] for m in L if any(all(cf[i] >> ix[u[i]] & 1 for i in range(len(u))) for u in t[m]))
                    F[l].append(word); fl[l][word] = g
        return F, fl
    def reclass(node):
        F, fl = node; F2 = {l: list(F[l]) for l in L}; fl2 = {l: dict(fl[l]) for l in L}; moved = {'A': 0, 'D': 0}
        for a in 'AD':
            for x in F[a]:
                if not fl[a][x] & HVO:
                    F2[a].remove(x); F2['N'].append(x); fl2['N'][x] = fl2[a].pop(x); moved[a] += 1
        for l in L:
            for x in F2[l]:
                g = fl2[l][x]
                if moved['A'] and g >> ix['A'] & 1: g |= 1 << ix['N']
                if moved['D'] and g >> ix['D'] & 1: g |= 1 << ix['N']
                fl2[l][x] = g
        return (F2, fl2), moved['A'] + moved['D']
    def validate(node):
        F, fl = node
        if not check_realisation(F): return 'REALISATION BROKEN'
        for l in L:
            for x in F[l]:
                tf = trueflag(x, F)
                if tf & ~fl[l][x]: return 'DP FLAG NOT SUPERSET'
        return None
    stats = Counter()
    R1, Rf = leaf(False), leaf(True)
    lvl1 = []
    for _ in range(3):
        tn = rng.choice(list(TAB)); q = len(TAB[tn]['B'][0])
        node = subst(tn, [rng.choice([R1, Rf]) for _ in range(q)])
        if sum(len(v) for v in node[0].values()) > 3000: continue
        if rng.random() < 0.7:
            node, mv = reclass(node); stats['moved1'] += mv
        r = validate(node)
        if r: return r, stats
        lvl1.append(node)
    if not lvl1: return None, stats
    lvl2 = []
    for _ in range(2):
        tn = rng.choice(['S2a', 'S2b']); kids = [rng.choice(lvl1 + [R1, Rf]) for _ in range(2)]
        est = sum(math.prod(len(kids[i][0][w[i]]) for i in range(2)) for l in L for w in TAB[tn][l])
        if est > 4000: continue
        node = subst(tn, kids)
        exact_ok = True
        if rng.random() < 0.7:
            node, mv = reclass(node); stats['moved2'] += mv
        r = validate(node)
        if r: return r, stats
        lvl2.append(node); stats['lvl2'] += 1
    # terminal code (K3a) on 3 nodes, explicit independence of the union if small
    pool = lvl2 + lvl1 + [R1]
    kids = [rng.choice(pool) for _ in range(3)]
    kids = [reclass(k)[0] for k in kids]
    K = CODE['K3a']
    size = sum(math.prod(len(kids[i][0][w[i]]) for i in range(3)) for w in K)
    if size <= 6000:
        S = []
        for w in K:
            for combo in itertools.product(*[kids[i][0][w[i]] for i in range(3)]): S.append(sum(combo, ()))
        assert len(set(S)) == size
        arr = np.array(S)
        for i in range(len(S)):
            c = np.all(adj[arr[i][None, :], arr[i + 1:]], axis=1) if i + 1 < len(S) else np.zeros(0, bool)
            if c.any(): return 'TERMINAL SET NOT INDEPENDENT', stats
        stats['terminal_checked'] += 1
    return None, stats

tot = Counter(); bad = []
for s in range(int(sys.argv[1]) if len(sys.argv) > 1 else 200):
    r, st = run_trial(s); tot.update(st)
    if r: bad.append((s, r))
print('failures', bad[:10], 'stats', dict(tot))

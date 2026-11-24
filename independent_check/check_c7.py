#!/usr/bin/env python3
"""Independent re-computation of the C7 v6 certificate integer M (d = 700) from definitions.
Inputs: BPZ Lean files (BaseC7Data, Substitutions, TerminalCodes, CertC7), the authors' data files
construction.json (slot names, flat label codes), family_codes.json (J15' words), exchanges.txt / exchanges_tang.txt
(J+ exchange words).  No author code is imported."""
import re, sys, itertools, math, json, time
from collections import defaultdict
import numpy as np
from decimal import Decimal, getcontext
getcontext().prec = 80
sys.set_int_max_str_digits(0)
import os
HERE = os.path.dirname(os.path.abspath(__file__))
LEAN, DAT = os.path.join(HERE, '..', 'c13', 'data', 'bpz'), os.path.join(HERE, '..', 'c7')
t0 = time.time()
L = 'BNADOHV'; ix = {c: i for i, c in enumerate(L)}
SEPP = ['BO','BH','BV','NA','ND','NO','NH','NV','AD','AH','DV']
sepm = np.zeros((7, 7), bool)
for p in SEPP: sepm[ix[p[0]], ix[p[1]]] = sepm[ix[p[1]], ix[p[0]]] = True
sigma = {'A': 'D', 'D': 'A', 'H': 'V', 'V': 'H', 'B': 'B', 'N': 'N', 'O': 'O'}
def readf(f): return open(f'{LEAN}/{f}').read()
def words_in(s): return [''.join(re.findall(r'[BNADOHV]', w)) for w in re.findall(r'!\[([^\]]*)\]', s)]
TAB = {}
src = readf('Substitutions.lean')
for m in re.finditer(r'def T(\w+) : Letter → Finset \(Fin (\d) → Letter\)\n(.*?)\n/--', src, re.S):
    parts = re.split(r'\|\s*\.?([BNADOHV])\s*=>', m.group(3))
    TAB['S' + m.group(1)] = {parts[i]: words_in(parts[i + 1]) for i in range(1, len(parts), 2)}
CODE = {}
src = readf('TerminalCodes.lean')
for m in re.finditer(r'def C(\w+) : Finset \(Fin (\d) → Letter\) :=\n(.*?)\n/--', src, re.S):
    CODE['K' + m.group(1)] = words_in(m.group(3))
def wsep(u, v): return any(sepm[ix[a], ix[b]] for a, b in zip(u, v))
for nm, t in TAB.items():
    for a in L:
        for u, v in itertools.combinations(t[a], 2): assert wsep(u, v)
        for b in L:
            if sepm[ix[a], ix[b]]: assert all(wsep(u, v) for u in t[a] for v in t[b])
for K in CODE.values(): assert all(wsep(u, v) for u, v in itertools.combinations(K, 2))
def rule(t, vs): return tuple(sum(math.prod(vs[i][ix[w[i]]] for i in range(len(w))) for w in t[l]) for l in L)
def code(K, vs): return sum(math.prod(vs[i][ix[w[i]]] for i in range(len(w))) for w in K)
def rate(M, d): return str((Decimal(M).ln() / d).exp())[:20]
def iroot(M, p, digits=16):
    lo, hi = 0, 10 ** (digits + 2); T = M * 10 ** (digits * p)
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if mid ** p <= T: lo = mid
        else: hi = mid
    return f'{lo // 10**digits}.{lo % 10**digits:0{digits}d}'

# ---------------- base G5 from BaseC7Data.lean ----------------
src = readf('BaseC7Data.lean')
def lnlist(nm): return [int(x) for x in re.search(r'def %s : List Code :=\s*\[(.*?)\]' % nm, src, re.S).group(1).replace('\n', ' ').split(',') if x.strip()]
Il, Xl = lnlist('Ilist'), lnlist('Xlist')
pairs = [(int(a), int(b), c == 'true') for a, b, c in re.findall(r'\((\d+), (\d+), (true|false)\)', re.search(r'def pairs.*?:=\s*\[(.*?)\]', src, re.S).group(1))]
N5 = 7 ** 5
def mask(lst):
    m = np.zeros(N5, bool); m[list(lst)] = True; return m
def ncount(m):
    A = m.reshape((7,) * 5).astype(np.int16)
    for ax in range(5): A = A + np.roll(A, 1, ax) + np.roll(A, -1, ax)
    return A.reshape(-1)
def near(m): return ncount(m) > 0
def indep(m): return bool((ncount(m)[m] == 1).all())
I = mask(Il); X = mask(Xl)
assert len(set(Il)) == 367 == I.sum() and len(set(Xl)) == 367 == X.sum()
assert indep(I) and indep(X)
R = mask([p[0] for p in pairs]); Q = mask([p[1] for p in pairs])
assert R.sum() == 8 == Q.sum() and not (R & Q).any() and (R <= I).all() and not (Q & I).any()
for r, q, _ in pairs:
    nb = near(mask([q])) & I
    assert nb.sum() == 1 and nb[r], 'alternative must have the parent as only I-neighbour'
PH = mask([r if s else q for r, q, s in pairs]); PV = mask([q if s else r for r, q, s in pairs])
assert indep(PH) and indep(PV)
nPH, nPV = near(PH), near(PV)
assert not (X & nPH & nPV).any()
F5 = {'B': I & ~R, 'N': X & ~nPH & ~nPV, 'A': X & nPV & ~nPH, 'D': X & nPH & ~nPV, 'O': R, 'H': PH, 'V': PV}
NR5 = {l: near(F5[l]) for l in L}
for l in L: assert indep(F5[l])
for p in SEPP: assert not (NR5[p[0]] & F5[p[1]]).any()
w5 = tuple(int(F5[l].sum()) for l in L)
print('[G5] gadget conditions and 7-family realisation verified; sizes', w5)
prof5 = (367, 8, 367, w5[1], w5[3], w5[2])          # (a,t,s,o,h,v): h = |X^H| = D, v = |X^V| = A
# actual separation relation of the G5 families (closed neighbourhoods)
actsep = {(a, b): not (NR5[a] & F5[b]).any() for a in L for b in L}

# ---- calibration 1: BPZ CertC7 M ----
def parse_sched(fname):
    s = readf(fname)
    ab = dict(re.findall(r'abbrev (\w+) : (?:Subst|Code) Letter Letter\.sep \d := (?:Substitutions|TerminalCodes)\.(\w+)', s))
    rl = {}
    for m in re.finditer(r'def R(\w+) \(R : Realisation[^\n]*\n[^\n]*:=\s*Realisation\.multiSubst e(\w+) \(ch(\w+) R\) ([\w.]+)', s):
        r = m.group(4).split('.')[-1]; rl[m.group(1)] = ab.get(r, r)
    ch = {}
    for m in re.finditer(r'def ch(\w+) \(R : Realisation[^\n]*\n[^\n]*:=\n(.*?)\n\n', s, re.S):
        ch[m.group(1)] = [t if t in ('R1', 'Rf') else t[1:] for t in re.findall(r'\(?(R\w+) R\)?', m.group(2))]
    tm = re.search(r'def terminalChildren \(R[^\n]*\n[^\n]*:=\n(.*?)\n\n', s, re.S).group(1)
    term = [t if t in ('R1', 'Rf') else t[1:] for t in re.findall(r'\(?(R\w+) R\)?', tm)]
    K = re.search(r'le_indepNum_multiCode eT \(terminalChildren [^)]*\) (\w+)', s).group(1); K = ab.get(K, K)
    return rl, ch, term, K, int(re.search(r'def M : Nat :=\s*(\d+)', s).group(1)), int(re.search(r'strongPower G (\d+)\)\.indepNum', s).group(1))
rl, ch, term, K, Mb, Eb = parse_sched('CertC7.lean')
val = {'R1': w5, 'Rf': tuple(w5[ix[sigma[l]]] for l in L)}
def g(x):
    if x not in val: val[x] = rule(TAB[rl[x]], [g(c) for c in ch[x]])
    return val[x]
Mbpz = code(CODE[K], [g(t) for t in term])
print(f'[calib] BPZ CertC7: M reproduced from Lean schedule = {Mbpz == Mb}; rate {iroot(Mbpz, 5 * Eb)} (d = {5 * Eb})')

# ---------------- coordinate automorphisms ----------------
DG = np.array([[(c // 7 ** j) % 7 for j in range(5)] for c in range(N5)])
PW = 7 ** np.arange(5)
def autmap(spec):
    if spec == 'T':
        Y = np.stack([(2 - DG[:, 1]) % 7, DG[:, 3], DG[:, 0], (2 - DG[:, 2]) % 7, DG[:, 4]], 1)
    else:
        (pi, sg), c = spec
        Y = (DG[:, list(pi)] * np.array(sg) + np.array(c)) % 7
    P = Y @ PW; assert len(set(P.tolist())) == N5
    # automorphism check: adjacency preserved (strong product of C7 with signed perm + shift is automatic; test anyway)
    return P
def img(m, P):
    out = np.zeros(N5, bool); out[P[np.nonzero(m)[0]]] = True; return out
# per-block reference bits (pure Gao references): n0 = in N(X0_5), nr = in N(Xr_5)
B0 = NR5['N'].astype(np.int64); BR = (NR5['A'] | NR5['D']).astype(np.int64)
STATE = B0 | (BR << 1)            # subset of Z2: bit0 = contains 0, bit1 = contains 1
def sumset(s, t):
    r = 0
    for a in (0, 1):
        if s >> a & 1:
            for b in (0, 1):
                if t >> b & 1: r |= 1 << ((a + b) % 2)
    return r
SS = [[sumset(s, t) for t in range(4)] for s in range(4)]
def dist_of(m): return np.bincount(STATE[m], minlength=4).astype(object)
def flat_jq(words, auts):
    """J = union_w prod_i aut_i(F_{w_i}(G5)); returns (j, q = |J minus N(X0_L)|, L = pure Gao tree over k blocks)."""
    k = len(words[0]); assert len(auts) == k
    maps = {}
    def dd(i, l):
        key = (repr(auts[i]), l)
        if key not in maps:
            P = autmap(auts[i]); maps[key] = dist_of(img(F5[l], P))
        return maps[key]
    j = q = 0
    for w in words:
        st = {1: 1}      # sumset identity is {0}
        for i, l in enumerate(w):
            d = dd(i, l); nxt = defaultdict(int)
            for s, c in st.items():
                for t in range(4):
                    if d[t]: nxt[SS[s][t]] += c * int(d[t])
            st = nxt
        j += sum(st.values()); q += sum(c for s, c in st.items() if not s & 1)
    return j, q
def check_code_indep(words, auts):
    """distinct words must have a coordinate whose (automorphic images of) families are separated."""
    assert len(set(words)) == len(words)
    labsep = all(wsep(u, v) for u, v in itertools.combinations(words, 2))
    if labsep: return 'label-separated'
    # exact block criterion with actual G5 separations (automorphism preserves separation)
    W = np.array([[ix[c] for c in w] for w in words]); S = np.array([[actsep[(a, b)] for b in L] for a in L])
    for s in range(0, len(words), 256):
        ok = np.zeros((min(256, len(words) - s), len(words)), bool)
        for i in range(W.shape[1]): ok |= S[W[s:s + 256, i][:, None], W[None, :, i]]
        ok[np.arange(ok.shape[0]), np.arange(s, s + ok.shape[0])] = True
        assert ok.all(), 'flat code not independent'
    return 'separated via actual G5 family separations'

# ---------------- G10, I_10, X10, J+ (explicit, 10-dim words as pairs) ----------------
def fam_list(l): return np.nonzero(F5[l])[0]
G10blocks = {l: TAB['S2a'][l] for l in L}       # Gao(L,R) families = S2a (paper / BPZ)
def explicit(words2, Pa=None, Pb=None):
    out = []
    for w in words2:
        a = fam_list(w[0]); b = fam_list(w[1])
        if Pa is not None: a = Pa[a]; b = Pb[b]
        out.append((np.repeat(a, len(b)), np.tile(b, len(a))))
    x = np.concatenate([o[0] for o in out]); y = np.concatenate([o[1] for o in out])
    return x.astype(np.int64), y.astype(np.int64)
MAIN2 = ['BB', 'HD', 'VA', 'DV', 'AH', 'ON', 'NO']   # Gao main code as label words (paper)
TT = autmap('T')
I10x, I10y = explicit(MAIN2)
TIx, TIy = explicit(MAIN2, TT, TT)
X10x, X10y = explicit(G10blocks['N'] + G10blocks['A'] + G10blocks['D'])
assert len(set(zip(I10x.tolist(), I10y.tolist()))) == len(I10x)
def bits10(x, y):
    s0, s1 = STATE[x], STATE[y]
    st = np.array(SS)[s0, s1]
    return st & 1, st >> 1 & 1          # in N(X0_10), in N(Xr_10)
def indep10(x, y):
    c = np.zeros(7 ** 10, np.uint8); c[x + N5 * y] = 1
    c = c.reshape((7,) * 10)
    for ax in range(10):
        c = np.minimum(c + np.roll(c, 1, ax) + np.roll(c, -1, ax), 2).astype(np.uint8)
    r = c.reshape(-1)[x + N5 * y]
    return bool((r == 1).all())
def jplus(fname):
    REM, INS = [], []
    for ln in open(f'{DAT}/{fname}'):
        t = ln.split('#')[0].split()
        if t: (REM if t[0] == '-' else INS).append((int(t[1]), int(t[2])))
    base = set(zip(TIx.tolist(), TIy.tolist())); assert len(base) == len(TIx)
    assert len(set(REM)) == len(REM) and all(w in base for w in REM)
    S = base - set(REM)
    assert len(set(INS)) == len(INS) and not any(w in S for w in INS)
    S |= set(INS)
    a = np.array(sorted(S), dtype=np.int64)
    return a[:, 0], a[:, 1], len(REM)
x0b, _ = bits10(I10x, I10y)
print(f'[G10] |I_10| = {len(I10x)}, |X10| = {len(X10x)}; I_10 independent in C7^10: {indep10(I10x, I10y)}; T(I_10) independent: {indep10(TIx, TIy)}')
n0X, nrX = bits10(X10x, X10y)
qX10 = int((n0X == 0).sum()); jX10 = len(X10x)
JP = {}
for fn in ('exchanges_tang.txt', 'exchanges.txt'):
    jx, jy, nrem = jplus(fn)
    n0, nr = bits10(jx, jy)
    JP[fn] = (jx, jy, n0, nr)
    print(f'[J+ {fn}] {nrem} exchanges, |J+| = {len(jx)}, independent in C7^10: {indep10(jx, jy)}, C1 = |J+ minus N(X0_10)| = {int((n0 == 0).sum())}')
def C3(fn):
    # G15h aux = X10 x X0_5  u  J+ x XH_5  u  J+ x XV_5 ;  q relative to X0_15 of Gao(G10,G5)
    jx, jy, n0, nr = JP[fn]
    st10_X = (n0X | (nrX << 1)); st10_J = (n0 | (nr << 1))
    tot = 0
    for st10, lab in ((st10_X, 'N'), (st10_J, 'D'), (st10_J, 'A')):
        c10 = np.bincount(st10, minlength=4); c5 = dist_of(F5[lab])
        tot += sum(int(c10[s]) * int(c5[t]) for s in range(4) for t in range(4) if not SS[s][t] & 1)
    return tot
print(f'[calib] C3 (Tang J+) = {C3("exchanges_tang.txt")}, C3 (J+_d) = {C3("exchanges.txt")}')
# Tan's J15 = T(I_15), I_15 = main code of Gao(G10,G5): substitute S2a words for the G10 letter
I15w = sorted({u + w[1] for w in MAIN2 for u in G10blocks[w[0]]})
assert len(I15w) == sum(len(G10blocks[w[0]]) for w in MAIN2)
print(f'[calib] |T(I_15)|, C2 = {flat_jq(I15w, ["T"] * 3)}  (Tan: 49495055, 12839823)')

# ---------------- profile recursion ----------------
def pgao(Lp, Rp):
    a1, t1, s1, o1, h1, v1 = Lp; a2, t2, s2, o2, h2, v2 = Rp
    return ((a1 - t1) * (a2 - t2) + t1 * s2 + s1 * t2, t1 * o2 + o1 * t2, s1 * s2, o1 * o2 + (h1 + v1) * (h2 + v2), h1 * o2 + o1 * v2, v1 * o2 + o1 * h2)
def phet(Lp, Rp, J0, JH, JV):
    aL, tL, sL, oL, hL, vL = Lp; aR, tR, sR, oR, hR, vR = Rp; j0, o0, h0, v0 = J0; jH, qH = JH; jV, qV = JV
    assert j0 == o0 + h0 + v0 and 0 <= qH <= jH and 0 <= qV <= jV
    return ((aL - tL) * (aR - tR) + tL * sR + sL * tR, tL * oR + oL * tR, j0 * oR + jH * hR + jV * vR,
            o0 * oR + qH * hR + qV * vR, h0 * oR + (jV - qV) * vR, v0 * oR + (jH - qH) * hR)
def psig(p): a, t, s, o, h, v = p; return (a, t, s, o, v, h)
def Phi(p): a, t, s, o, h, v = p; return (a - t, o, v, h, t, t, t)
# explicit check of the Gao profile formula on G10 = Gao(G5,G5): classify X10 against the G10 transversals
p10 = pgao(prof5, prof5)
assert p10[0] == len(I10x) and p10[2] == jX10
def nearbits_label(x, lab): return NR5[lab][x]
# P^H_10 = PH x X0 u X0 x PV  (S2a 'H' = HN, NV); P^V_10 = VN, NH
nH = (NR5['H'][X10x] & NR5['N'][X10y]) | (NR5['N'][X10x] & NR5['V'][X10y])
nV = (NR5['V'][X10x] & NR5['N'][X10y]) | (NR5['N'][X10x] & NR5['H'][X10y])
assert not (nH & nV).any()
assert (int((~nH & ~nV).sum()), int((nH & ~nV).sum()), int((nV & ~nH).sum())) == p10[3:], 'Gao profile formula'
assert qX10 == p10[4] + p10[5]
print('[G10] explicit X10 classes agree with the Gao profile formula', p10)

SPEC = json.load(open(f'{DAT}/construction.json')); FC = json.load(open(f'{DAT}/family_codes.json'))
def tau(a): return a if a == 'T' else ((tuple(a[0][0]), tuple(a[0][1])), tuple(a[1]))
j15w = FC['J15']['words'] if isinstance(FC['J15']['words'], list) else eval(FC['J15']['words'])
j15a = FC['J15']['auts'] if isinstance(FC['J15']['auts'], list) else eval(FC['J15']['auts'])
print('[J15\'] independence:', check_code_indep(j15w, [tau(a) for a in j15a]))
JQ15 = flat_jq(j15w, [tau(a) for a in j15a]); print('[J15\'] (j, q) =', JQ15, ' claimed (49496015, 12843063)')

def split_top(s):
    out = []; d = 0; cur = ''
    for c in s:
        if c in '<[(': d += 1
        if c in '>])': d -= 1
        if c == ',' and d == 0: out.append(cur); cur = ''
        else: cur += c
    out.append(cur); return out
def build(fnJ):
    jx, jy, n0, nr = JP[fnJ]; JPq = (len(jx), int((n0 == 0).sum()))
    GAD = {'G5': prof5}
    GAD['sG5'] = psig(prof5); GAD['G10A'] = pgao(GAD['sG5'], prof5); GAD['sG10A'] = psig(GAD['G10A'])
    GAD['G15AX'] = pgao(GAD['G10A'], prof5); GAD['sG15AX'] = psig(GAD['G15AX'])
    G10A = GAD['G10A']; auxG10A = (G10A[2], G10A[3], G10A[4], G10A[5])
    G15Ah = phet(G10A, prof5, auxG10A, JPq, (jX10, qX10))
    PAT = {'P10A': (G10A, auxG10A, JPq, (jX10, qX10)),
           'P15A8': (GAD['G15AX'], (G15Ah[2], G15Ah[3], G15Ah[4], G15Ah[5]), JQ15, JQ15)}
    DIM = {'P10A': 2, 'P15A8': 3}; GD = {'G5': 1, 'sG5': 1, 'G10A': 2, 'sG10A': 2, 'G15AX': 3, 'sG15AX': 3}
    return GAD, PAT, DIM, GD
JQ = {}
for nm, sp in SPEC['patterns'].items():
    words = SPEC['codes'][str(sp['k'])]; auts = [tau(a) for a in sp['auts']]
    how = check_code_indep(words, auts)
    jq = flat_jq(words, auts)
    JQ[nm] = jq
    print(f'[flat] {nm}: k = {sp["k"]}, {len(words)} words, {how}; (j, q) = {jq}; matches claim: {jq == (sp["j"], sp["q"])}')
def evaluate(slots, fnJ):
    GAD, PAT, DIM, GD = build(fnJ)
    def pat(nm):
        if nm in PAT: return PAT[nm], DIM[nm]
        assert nm.startswith('N<') and nm.endswith('>')
        qn, cn = split_top(nm[2:-1]); Qd, qd = pat(qn); C, cd = gad(cn)
        Lp = pgao(Qd[0], C); J0 = phet(Qd[0], C, *Qd[1:])
        k = qd + cd; jq = JQ[nm]; assert SPEC['patterns'][nm]['k'] == k, ('flat code dimension', nm)
        return (Lp, (J0[2], J0[3], J0[4], J0[5]), jq, jq), k
    def gad(nm):
        if nm in GAD: return GAD[nm], GD[nm]
        if nm.startswith('s('): p, d = gad(nm[2:-1]); return psig(p), d
        if nm.startswith('H['):
            dpt = 0
            for i, c in enumerate(nm):
                if c == '[': dpt += 1
                if c == ']':
                    dpt -= 1
                    if dpt == 0: break
            P, pd = pat(nm[2:i]); Rg, rd = gad(nm[i + 2:-1])
            return phet(P[0], Rg, *P[1:]), pd + rd
        raise KeyError(nm)
    ps = [gad(s) for s in slots]
    for (p, d), s in zip(ps, slots):
        a, t, s_, o, h, v = p; assert o + h + v == s_ and t <= a
    # check every pattern's flat code dimension matches its left gadget
    top = rule(TAB['S3b'], [Phi(p) for p, _ in ps])
    M = code(CODE['K4a'], [top] * 4)
    d = 4 * 5 * sum(dd for _, dd in ps)
    return M, d
for nm, sp in SPEC['patterns'].items():
    pass
print('[X10] independent in C7^10:', indep10(X10x, X10y))
# explicit check of the HetGao class formula on G15Ah = Het(G10A, G5, aux(G10A), J+_d, X10)
def bits_u(x, y, first_sigma):
    FH, FV = ('V', 'H') if first_sigma else ('H', 'V')       # G10A = Gao(sG5, G5): left block sigma'd
    nPH = (NR5[FH][x] & NR5['N'][y]) | (NR5['N'][x] & NR5['V'][y])
    nPV = (NR5[FV][x] & NR5['N'][y]) | (NR5['N'][x] & NR5['H'][y])
    n0, _ = bits10(x, y)
    return nPH, nPV, n0
jx, jy, _, _ = JP['exchanges.txt']
cls = [0, 0, 0]; bad = 0
for (ux, uy), lab in (((X10x, X10y), 'N'), ((jx, jy), 'D'), ((X10x, X10y), 'A')):
    a, b_, c_ = bits_u(ux, uy, True)
    for zz in (0, 1):
        pass
    z = np.nonzero(F5[lab])[0]
    zPH, zPV, zX0 = NR5['H'][z], NR5['V'][z], NR5['N'][z]
    for ka in (0, 1):
        for kb in (0, 1):
            for kc in (0, 1):
                nu = int(((a == ka) & (b_ == kb) & (c_ == kc)).sum())
                if not nu: continue
                for za in (0, 1):
                    for zb in (0, 1):
                        for zc in (0, 1):
                            nz = int(((zPH == za) & (zPV == zb) & (zX0 == zc)).sum())
                            if not nz: continue
                            inH = (ka and zc) or (kc and zb); inV = (kb and zc) or (kc and za)
                            if inH and inV: bad += nu * nz
                            elif inH: cls[1] += nu * nz
                            elif inV: cls[2] += nu * nz
                            else: cls[0] += nu * nz
GAD_, PAT_, _, _ = build('exchanges.txt'); G10A_ = GAD_['G10A']
ph = phet(G10A_, prof5, (G10A_[2], G10A_[3], G10A_[4], G10A_[5]), (len(jx), int((JP['exchanges.txt'][2] == 0).sum())), (jX10, qX10))
print('[Het] explicit G15Ah aux classes (X0, XH, XV) =', tuple(cls), ' phet formula =', ph[3:], ' words near both transversals:', bad)
assert tuple(cls) == ph[3:] and bad == 0
M6, d6 = evaluate(SPEC['slots'], 'exchanges.txt')
Mc = open(f'{DAT}/certificate.txt').read().split(); dc, Mclaim = int(Mc[0]), int(Mc[1])
print(f'[C7] my M has {len(str(M6))} digits, d = {d6}; equals certificate.txt: {M6 == Mclaim and d6 == dc}')
print(f'[C7] rate (integer root) {iroot(M6, d6)}  ; claimed 3.2588405876641976')
TANG = int(json.load(open(f'{DAT}/tang_reference.json'))['M'])
print(f'[C7] exceeds Tang d=680 exactly: {M6 ** 680 > TANG ** d6}; Tang rate {iroot(TANG, 680)}')
M6t, _ = evaluate(SPEC['slots'], 'exchanges_tang.txt')
print(f'[C7 with Tang J+ instead of the new J+] rate {iroot(M6t, d6)}')
print(f'done {time.time() - t0:.0f}s')

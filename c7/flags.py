"""Distribution method: for references that are pure Gao products of the base gadget, membership in
N(X^0(L)) depends only on per-coordinate flags (x in N(X0_5), x in N(Xr_5)).  Exact integer tensors."""
import numpy as np, itertools, functools
from engine import *
from engine import _ATOMS
_V = {}
def vec4(a, NX0, NXr):
    if a not in _V:
        m = _ATOMS[a]
        b0 = NX0[m]; b1 = NXr[m]
        _V[a] = [int((~b0 & ~b1).sum()), int((b0 & ~b1).sum()), int((~b0 & b1).sum()), int((b0 & b1).sum())]
    return _V[a]
def outer(x, y):
    return np.multiply.outer(x, y)
def dist(blocks, NX0, NXr, T=True):
    acc = None
    for b in blocks:
        t = None
        for a in b:
            v = np.array(vec4(aT(a) if T else a, NX0, NXr), dtype=object)
            t = v if t is None else outer(t, v)
        acc = t if acc is None else acc + t
    return acc
# Boolean tensors for pure-Gao reference trees
def base_ind():
    f = np.arange(4)
    return (f & 1).astype(bool), (f >> 1 & 1).astype(bool)
def gao_ind(P, Q):
    (p0, pr), (q0, qr) = P, Q
    o = np.logical_or.outer
    a = np.logical_and.outer
    return (a(p0, q0) | a(pr, qr), a(pr, q0) | a(p0, qr))
def tree_ind(t):
    """t: 'b' for a base coordinate or (t1, t2) for Gao(t1, t2)"""
    if t == 'b':
        return base_ind()
    return gao_ind(tree_ind(t[0]), tree_ind(t[1]))
def gao_main_dist(P, Q, NX0, NXr):
    """flag distribution of T(main code of Gao(P,Q)) from the class sets of the two gadgets."""
    d = lambda G, k: dist(G[k], NX0, NXr)
    comps = [('B', 'B'), ('PH', 'XH'), ('PV', 'XV'), ('XH', 'PV'), ('XV', 'PH'), ('R', 'X0'), ('X0', 'R')]
    tot = None
    for x, y in comps:
        if not P[x] or not Q[y]:
            continue
        t = outer(d(P, x), d(Q, y))
        tot = t if tot is None else tot + t
    return tot
def q_from(distT, refind):
    return int(distT[~refind[0]].sum())

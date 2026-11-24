#!/usr/bin/env python3
"""v4 exact check:  Theta(C_7) >= M^(1/680) = 3.25883999555...  (v3: 3.2588392704292, Tang d = 680: 3.2588387054446)

v4 = v3 plus deeper nested left patterns and 3-part family side codebooks along every chain:
  top level  K4a(S3b(Phi g0', Phi g4, Phi g8'))  with
    g0' = sigma HetGao_{N<N<N<N<P15A8,G5>,sG5>,G5>,sG5>}(sG5)                  (40 dims, depth-4 left of 35 dims)
    g4' = sigma HetGao_{N<N<N<P10A,sG10A>,sG10A>,sG15AX>}(sigma HetGao_{N<N<N<P10A,G5>,G5>,G5>}(G5))   (45 + 30 dims)
    g8' = sigma HetGao_{N<N<N<N<N<P15A8,G5>,G5>,G5>,G5>,sG10A>}(sG10A)          (55 dims, depth-5 left of 45 dims)
  d = 4 (40 + 75 + 55) = 680.
Every nested pattern N<Q,C> has left Gao(L_Q, C) and neutral codebook J0 = X(HetGao_Q(C)) (recomputed along the
chain, exactly as for Tang's sibling/nested patterns); every side codebook is J = T(union over words w of a
separated label code of F_{w1}(G1) x F_{w2}(G2) x F_{w3}(G3)) over BPZ families of base gadgets.
The script first runs the complete v3 check (all 13 of Tan's/Tang's counts, v3 codebooks, v3 M), then
  4. builds the exact chunk-summary DP (sym.py) and re-derives with it all 13 counts and all v3 codebook counts;
  5. proves every new family codebook independent directly from the physical class blocks (v3's prover), and
     counts j and q exactly by two independent methods (chunk DP, and v3's per-coordinate flag tensors);
  6. evaluates the profile recursion, S3b and K4a in integers and compares M with v3's M at d = 680.
"""

import os
os.chdir(os.path.dirname(os.path.abspath(__file__)))
import json, sys, time, math, itertools, pickle
from decimal import Decimal, getcontext
getcontext().prec=60
from engine import *
from engine import _ATOMS
from flags import gao_main_dist, tree_ind, q_from
t0=time.time()
def prof(a,t,s,o,h,v):
    assert min(a,t,s,o,h,v)>=0 and t<=a and o+h+v==s; return (a,t,s,o,h,v)
def psig(p): a,t,s,o,h,v=p; return (a,t,s,o,v,h)
def pgao(L,R):
    a1,t1,s1,o1,h1,v1=L; a2,t2,s2,o2,h2,v2=R
    return prof((a1-t1)*(a2-t2)+t1*s2+s1*t2, t1*o2+o1*t2, s1*s2, o1*o2+(h1+v1)*(h2+v2), h1*o2+o1*v2, v1*o2+o1*h2)
def phet(L,R,J0,JH,JV):
    aL,tL,sL,oL,hL,vL=L; aR,tR,sR,oR,hR,vR=R; j0,o0,h0,v0=J0; jH,qH=JH; jV,qV=JV
    return prof((aL-tL)*(aR-tR)+tL*sR+sL*tR, tL*oR+oL*tR, j0*oR+jH*hR+jV*vR, o0*oR+qH*hR+qV*vR, h0*oR+(jV-qV)*vR, v0*oR+(jH-qH)*hR)
def Phi(p): a,t,s,o,h,v=p; return (a-t,o,v,h,t,t,t)
G5, exch = load_base(); sG5 = G5.sigma()
G10=gao(G5,G5); G10A=gao(sG5,G5); G10D=gao(G5,sG5)
Jp=Tset(G10['I'])
for rem,ins in exch: Jp=remove_word(Jp,rem)
for rem,ins in exch: Jp.append((atom_of([ins[0]]),atom_of([ins[1]])))
# exchange validity: each inserted word's only J-neighbour is the removed word; inserted words pairwise non-confusable
raw=Tset(G10['I']); NBc=lambda c: anb(atom_of([c]))
for rem,ins in exch:
    words=set()
    for bl in raw:
        A0=np.nonzero(_ATOMS[bl[0]] & NBc(ins[0]))[0]; A1=np.nonzero(_ATOMS[bl[1]] & NBc(ins[1]))[0]
        words|={(int(x),int(y)) for x in A0 for y in A1}
    assert words=={tuple(rem)}, (rem,ins,words)
ins_l=[i for _,i in exch]
assert all(not (NBc(p[0])[q[0]] and NBc(p[1])[q[1]]) for i,p in enumerate(ins_l) for q in ins_l[i+1:])
check_disjoint_fast(Jp); assert size(Jp)==G10.profile()[0]
print('  [ok] J+ = T(I_10) with Tandon\'s 8 exchanges is a valid exchange set',flush=True)
X10=G10['X']
G15X=gao(G10,G5); G15h=hetgao(G10,G5,G10.aux(),Jp,Jp)
G15AX=gao(G10A,G5); G15Ah=hetgao(G10A,G5,G10A.aux(),Jp,X10)
G15DX=gao(G10D,sG5); G15Dh=hetgao(G10D,sG5,G10D.aux(),X10,Jp)
J15=Tset(G15X['I'])
GAD={'G5':G5,'G10':G10,'G10A':G10A,'G10D':G10D,'G15X':G15X,'G15AX':G15AX,'G15DX':G15DX,'G15h':G15h,'G15Ah':G15Ah,'G15Dh':G15Dh}
for k in list(GAD): GAD['s'+k]=GAD[k].sigma()
MAINS={1:G5,2:G10,3:G15h}
PAT={'P10':(G10,G10.aux(),Jp,Jp),'P10A':(G10A,G10A.aux(),Jp,X10),'P10D':(G10D,G10D.aux(),X10,Jp),
 'P15X':(G15X,G15h.aux(),J15,J15),'P15A8':(G15AX,G15Ah.aux(),J15,J15),'P15Ah':(G15AX,G15Ah.aux(),J15,G15X['X']),
 'P15A5':(G15AX,G15Ah.aux(),J15,G15h['X']),'P15D':(G15DX,G15Dh.aux(),G15h['X'],J15)}
PATP={}
for k,(L,J0,JH,JV) in PAT.items():
    PATP[k]=(L.profile(),(size(J0['X0'])+size(J0['XH'])+size(J0['XV']),size(J0['X0']),size(J0['XH']),size(J0['XV'])),
             (size(JH),count_outside_fast(JH,L['X0'],check=False)),(size(JV),count_outside_fast(JV,L['X0'],check=False)))
print('  [ok] base gadget and Tan patterns built %.0fs'%(time.time()-t0),flush=True)
TANGQ={'S<G15X,G10,P15X>':(6682034753199,2168034218823),'N<S<G15X,G10,P15X>,G5>':(2455687916341537,840885528362080),
 'S<G15AX,G5,P15A8>':(18184231617,5415710640),'N<S<G15AX,G5,P15A8>,G5>':(6681986127279,2167394749159),
 'S<G15AX,sG15AX,P15A5>':(2455726444728097,841149894373344),'N<S<G15AX,sG15AX,P15A5>,sG15AX>':(121947917749163375722991,44457037740952884957687),
 'S<G15AX,sG15Ah,P15A8>':(2455726444728097,841760069965664),'N<S<G15AX,sG15Ah,P15A8>,sG15Ah>':(121947917749163375722991,44503522527412807055847)}
ORDER=list(TANGQ)
tang=json.load(open('tang_reference.json'))
S3b={'B':['BBB','BHA','NAV','NDH','NVD','ABH','AHN','AHD','DBV','DVN','DVD','HND','HDN','HDD','VNA','VAB','VDA'],'N':['BVD','NNN','NVA','ANH','ADH','AHN','DNV','DDH','DHN','HVD'],'A':['NBA','NAN','ABB','AAV','AHA'],'D':['NBD','NDN','DBB','DAV','DHA'],'O':[],'H':['NNH','NHN','HNN','HVV'],'V':['NNV','NVN','VNN','VVV']}
K4a=['BBBB','BNVB','BAHB','BDVB','BHNB','BHDB','BVAB','NBBV','NNVH','NAVH','NDHH','NHNH','NHAH','NVDV','ABBV','ANHH','AAVH','ADHH','AHAH','AVNH','AVDH','DBBH','DNVV','DAVV','DDHV','DHNV','DHAV','DVDV','HBBA','HNVD','HAHD','HAVN','HDHN','HDVD','HHNN','HHND','HHAN','HHDD','HVAD','HVDN','VBBN','VBBD','VNVN','VNVA','VAHA','VDVA','VHDA','VVNA','VVAA']
LAB='BNADOHV'
def rule(R,vs): return tuple(sum(math.prod(v[LAB.index(c)] for c,v in zip(w,vs)) for w in R[l]) for l in LAB)
def code(K,vs): return sum(math.prod(v[LAB.index(c)] for c,v in zip(w,vs)) for w in K)
PROF={k:g.profile() for k,g in GAD.items()}
def patp_all(jq):
    """profile-level patterns for Tang's S/N names given codebook (j,q) per name; J0 recomputed along the chain"""
    pp=dict(PATP)
    for nm in ORDER:
        if nm.startswith('S<'):
            a,b,p=nm[2:-1].split(','); Lp=pgao(PROF[a],PROF[b]); inner=PATP[p]; C=PROF[b]
        else:
            inn,c=nm[2:-1].rsplit('>,',1); inn+='>'; Lp=pgao(pp[inn][0],PROF[c]); inner=pp[inn]; C=PROF[c]
        J0=phet(inner[0],C,inner[1],inner[2],inner[3])
        j,q=jq[nm]; pp[nm]=(Lp,(J0[2],J0[3],J0[4],J0[5]),(j,q),(j,q))
    return pp
def evalM(jq):
    pp=patp_all(jq); pr={'G5':PROF['G5']}
    for st in tang['gadgets']:
        if st['op']=='hetgao':
            Lp,J0,JH,JV=pp[st['pattern']]; pr[st['name']]=phet(Lp,pr[st['R']],J0,JH,JV)
        else: pr[st['name']]=psig(pr[st['of']])
    vs=[Phi(pr[x[4:-1]]) for x in tang['top']['rule_inputs']]
    return code(K4a,[rule(S3b,vs)]*4)
rate=lambda M: (Decimal(M).ln()/680).exp()
M0=evalM(TANGQ); assert M0==int(tang['M']); print('Tang M reproduced',flush=True)

assert G5.profile()==(367,8,367,322,26,19)
C1=count_outside_fast(Jp,G10['X0']); C2=count_outside_fast(J15,G15X['X0']); q15=count_outside_fast(J15,G15h['X0'])
C3=count_outside_fast(G15h['X'],G15X['X0']); C4=count_outside_fast(Tset(gao(G15h,G15h)['I']),gao(G15AX,G15Ah.sigma())['X0'])
for nm,v,ref in [('C1',C1,27488),('C2',C2,12839823),('C3',C3,14045805),('C4',C4,841760069965664),('q15',q15,12872271)]:
    assert v==ref,(nm,v,ref); print(f'  [ok] {nm} = {v}',flush=True)
assert PATP['P15X'][2][1]==C2 and PATP['P15A5'][3][1]==C3
import engine
_sb=engine.split_by; _SM={}
def split_memo(blocks, ref):
    k=(id(blocks),id(ref))
    if k not in _SM: _SM[k]=(_sb(blocks,ref),blocks,ref)
    return _SM[k][0]
engine.split_by=split_memo
import engine as E
E.hetgao.__globals__['split_by']=split_memo
# physical builders for Tang's S patterns (used as left patterns applied to small R)
SPHYS={}
def spat(nm):
    if nm not in SPHYS:
        a,b,p=nm[2:-1].split(','); A,B=GAD[a],GAD[b]; L,J0,JH,JV=PAT[p]
        J0s=hetgao(L,B,J0,JH,JV).aux(); M=gao(MAINS[A.m],MAINS[B.m]); J=Tset(M['I'])
        SPHYS[nm]=(gao(A,B),J0s,J,J)
    return SPHYS[nm]
LIB={}   # name -> (profile, m, builder)
for k,g in GAD.items(): LIB[k]=(g.profile(),g.m,(lambda g=g: g))
def addh(pn,rn,getpat,pp):
    Lp,J0,JH,JV=pp; R=LIB[rn]
    p=phet(Lp,R[0],J0,JH,JV); m=pp[0] and None
    return p
cache={}
def build(name):
    if name in cache: return cache[name]
    p,m,f=LIB[name]; g=f(); assert g.profile()==p,(name,g.profile(),p); cache[name]=g; return g
items=list(LIB.items())
pp_all=patp_all(TANGQ)
for pn in ['P10','P10A','P10D','P15X','P15A8','P15Ah','P15A5','P15D','S<G15AX,G5,P15A8>','S<G15X,G10,P15X>']:
    Lm=(PAT[pn][0].m if pn in PAT else (3+GAD[pn[2:-1].split(',')[1]].m))
    for rn,(rp,rm,_) in items:
        if Lm+rm>7: continue
        Lp,J0,JH,JV=pp_all[pn]
        p=phet(Lp,rp,J0,JH,JV)
        def f(pn=pn,rn=rn):
            L,J0,JH,JV=(PAT[pn] if pn in PAT else spat(pn)); return hetgao(L,build(rn),J0,JH,JV)
        LIB[f'H[{pn}]({rn})']=(p,Lm+rm,f)
        LIB[f's(H[{pn}]({rn}))']=(psig(p),Lm+rm,(lambda f=f: f().sigma()))

from engine import _ATOMS
# ----- the 10-dim and 5-dim sets defining X^0 and X^r of G15Ah = HetGao(G10A, G5)[X(G10A), J+, X10] -----
J0=G10A.aux(); ref=G10A['X0']
JHq,JHn=split_by(Jp,ref); JVq,JVn=split_by(X10,ref)
S10={'J0X0':J0['X0'],'J0XH':J0['XH'],'J0XV':J0['XV'],'JHq':JHq,'JHn':JHn,'JVq':JVq,'JVn':JVn}
NAMES=list(S10)
def bitmap(blocks):
    m=np.zeros((N5,N5),bool)
    for a,b in blocks: m[np.ix_(np.nonzero(_ATOMS[a])[0],np.nonzero(_ATOMS[b])[0])]=True
    m=m.reshape((7,)*10)
    for ax in range(10): m=m|np.roll(m,1,ax)|np.roll(m,-1,ax)
    return m.reshape(N5,N5)
NB10=[bitmap(S10[k]) for k in NAMES]
print('10-dim neighbourhood maps ready %.0fs'%(time.time()-t0),flush=True)
# check: G15Ah classes match the formula
X0b=anb(G5['X0'][0][0]); XHb=anb(G5['XH'][0][0]); XVb=anb(G5['XV'][0][0])
xr=_ATOMS[G5['XH'][0][0]]|_ATOMS[G5['XV'][0][0]]; NX0=X0b; NXr=dilate(xr)
def w3(a):
    m=_ATOMS[a]; f=X0b[m]*1+XHb[m]*2+XVb[m]*4
    return np.bincount(f,minlength=8)
# chunk summary for an sG15Ah chunk (p in 10-dim, w in 5-dim): (N0, Nr) as function of 7 pair bits + 3 w bits
I={k:i for i,k in enumerate(NAMES)}
def summ_h(pb,wb):
    g=lambda k: (pb>>I[k])&1
    w0,wH,wV=wb&1,(wb>>1)&1,(wb>>2)&1
    n0=(g('J0X0')&w0)|(g('JHq')&wH)|(g('JVq')&wV)
    nr=(g('J0XH')&w0)|(g('JVn')&wV)|(g('J0XV')&w0)|(g('JHn')&wH)
    return n0+2*nr
SUMH=np.array([[summ_h(p,w) for w in range(8)] for p in range(128)])
PC={}
def pair7(a,b):
    k=(a,b)
    if k not in PC:
        ia=np.nonzero(_ATOMS[a])[0]; ib=np.nonzero(_ATOMS[b])[0]
        code=np.zeros((len(ia),len(ib)),np.int64)
        for i,M in enumerate(NB10): code|=M[np.ix_(ia,ib)].astype(np.int64)<<i
        PC[k]=np.bincount(code.ravel(),minlength=128)
    return PC[k]
CH={}
def chunk_h(a,b,c):
    k=(a,b,c)
    if k not in CH:
        p=pair7(a,b); w=w3(c); out=[0]*4
        M=np.multiply.outer(p.astype(object),w.astype(object))
        for s in range(4): out[s]=int(M[SUMH==s].sum())
        CH[k]=np.array(out,dtype=object)
    return CH[k]
# pure-Gao 15-chunk (G15AX) summary from base flags
IND15=tree_ind((('b','b'),'b'))   # (N0,Nr) boolean tensors (4,4,4)
from flags import vec4
def chunk_x(a,b_,c):
    k=('x',a,b_,c)
    if k not in CH:
        t=np.multiply.outer(np.multiply.outer(np.array(vec4(a,NX0,NXr),dtype=object),np.array(vec4(b_,NX0,NXr),dtype=object)),np.array(vec4(c,NX0,NXr),dtype=object))
        s=IND15[0]*1+IND15[1]*2
        CH[k]=np.array([int(t[s==v].sum()) for v in range(4)],dtype=object)
    return CH[k]
def class_dist(blocks,types):
    """blocks: A1-atom blocks (T applied here); types: list of chunk types 'x' or 'h' (3 coords each)"""
    acc=np.zeros((4,)*len(types),dtype=object)
    cache={}
    for bl in blocks:
        tb=tuple(aT(a) for a in bl); vs=[]
        for i,ty in enumerate(types):
            a,b_,c=tb[3*i:3*i+3]
            vs.append(chunk_h(a,b_,c) if ty=='h' else chunk_x(a,b_,c))
        t=vs[0]
        for v in vs[1:]: t=np.multiply.outer(t,v)
        acc=acc+t
    return acc
COMPS=[('B','B'),('PH','XH'),('PV','XV'),('XH','PV'),('XV','PH'),('R','X0'),('X0','R')]
def main_dist(X,Y,tX,tY):
    tot=None
    for x,y in COMPS:
        if not X[x] or not Y[y]: continue
        t=np.multiply.outer(class_dist(X[x],tX),class_dist(Y[y],tY))
        tot=t if tot is None else tot+t
    return tot
def gao_summ(s1,s2):
    n01,nr1=s1&1,s1>>1; n02,nr2=s2&1,s2>>1
    return ((n01&n02)|(nr1&nr2)) + 2*((nr1&n02)|(n01&nr2))
def q_tree(d,tree):
    """d: tensor over chunk summaries; tree over chunk indices, e.g. ((0,1),2). q = mass where N0 false."""
    k=d.ndim; tot=0
    for idx in itertools.product(range(4),repeat=k):
        def ev(t):
            return idx[t] if isinstance(t,int) else gao_summ(ev(t[0]),ev(t[1]))
        if ev(tree)&1==0: tot+=d[idx]
    return int(tot)

# ---- Tang's eight counts (validation of both counting methods) ----
b='b'; t10=(b,b); t15=(t10,b)
PURE={'S<G15AX,G5,P15A8>':(t15,b),'N<S<G15AX,G5,P15A8>,G5>':((t15,b),b),'S<G15X,G10,P15X>':(t15,t10),
 'N<S<G15X,G10,P15X>,G5>':((t15,t10),b),'S<G15AX,sG15AX,P15A5>':(t15,t15),'N<S<G15AX,sG15AX,P15A5>,sG15AX>':((t15,t15),t15)}
HREF={'S<G15AX,sG15Ah,P15A8>':((['x'],['h']),(0,1)),'N<S<G15AX,sG15Ah,P15A8>,sG15Ah>':(None,((0,1),2))}
def canon(nm):
    if nm.startswith('S<'):
        a,bb,_=nm[2:-1].split(','); return gao(MAINS[GAD[a].m],MAINS[GAD[bb].m]).__class__ and (MAINS[GAD[a].m],MAINS[GAD[bb].m])
    inner,c=nm[2:-1].rsplit('>,',1); inner+='>'; X,Y=canon(inner); return (gao(X,Y),MAINS[GAD[c].m])
def qcount(nm,X,Y,typesXY=None):
    if nm in PURE:
        d=gao_main_dist(X,Y,NX0,NXr); return int(d.sum()), q_from(d,tree_ind(PURE[nm]))
    tree=HREF[nm][1]
    if typesXY is None:
        tX=['x','h'][:X.m//3] if nm.startswith('N<') else ['x']; tY=['h'] if Y.m==3 else ['h','h']
        if nm.startswith('N<'): tX=(['x'] if X.m==3 else ['x','h'])
    else: tX,tY=typesXY
    d=main_dist(X,Y,tX,tY); return int(sum(d.ravel())), q_tree(d,tree)
for nm,(j0,q0) in TANGQ.items():
    X,Y=canon(nm); j,q=qcount(nm,X,Y)
    assert (j,q)==(j0,q0),(nm,j,q,j0,q0); print(f'  [ok] Tang count q[{nm}] = {q}',flush=True)
# ---- direct independence / disjointness proof for a Gao main code ----
COMPS=[('B','B'),('PH','XH'),('PV','XV'),('XH','PV'),('XV','PH'),('R','X0'),('X0','R')]
SC={}
def cs(a,c):
    if (a,c) not in SC:
        ma,mc=_ATOMS[a],_ATOMS[c]; conf=bool((ma&anb(c)).any()); st=False
        if conf:
            s=mc.reshape((7,)*5).astype(np.int16)
            for ax in range(5): s=s+np.roll(s,1,ax)+np.roll(s,-1,ax)
            st=bool((ma & ((s.reshape(-1)-mc.astype(np.int16))>0)).any())
        SC[(a,c)]=(conf,st)
    return SC[(a,c)]
def flg(S,S2):
    """(exists a confusable pair of words u in S, v in S2;  exists one with u != v), S, S2 unions of product blocks.
    Recursive over coordinates, grouping blocks by their atom; exact."""
    m=len(S[0]) if S else 0
    best=[False,False]
    def rec(A,B,i,st):
        if best[1]: return
        if i==m:
            best[0]=True; best[1]|=st; return
        ga=defaultdict(list); gb=defaultdict(list)
        for p in A: ga[p[i]].append(p)
        for p in B: gb[p[i]].append(p)
        for a,la in ga.items():
            for c,lb in gb.items():
                ci,si=cs(a,c)
                if ci:
                    rec(la,lb,i+1,st or si)
                    if best[1]: return
    if S and S2: rec(S,S2,0,False)
    return best[0],best[1]
def disjoint(S1,S2):
    try: check_disjoint_fast(S1+S2); return True
    except ArithmeticError: return False
def prove_main_code(X,Y):
    for G in (X,Y):
        for k in ('B','R','PH','PV','X0','XH','XV'):
            if G[k]: check_disjoint_fast(G[k])
    assert all(disjoint(X[x1],X[x2]) or disjoint(Y[y1],Y[y2]) for i,(x1,y1) in enumerate(COMPS) for x2,y2 in COMPS[i+1:])
    for i,(x1,y1) in enumerate(COMPS):
        for x2,y2 in COMPS[i:]:
            cA,sA=flg(X[x1],X[x2])
            if cA:
                cB,sB=flg(Y[y1],Y[y2])
                assert not (cB and (sA or sB)), ('confusable pair',(x1,y1),(x2,y2))
SPEC={'S<G15AX,G5,P15A8>': ('gao', 18184254657, 5416543392, 'G10', 'G10'), 'N<S<G15AX,G5,P15A8>,G5>': ('gao', 6682034753199, 2168034218823, 'G10', 'G15h'), 'S<G15X,G10,P15X>': ('gao', 6682034753199, 2168034218823, 'G10', 'G15h'), 'N<S<G15X,G10,P15X>,G5>': ('keep', 2455687916341537, 840885528362080), 'S<G15AX,sG15AX,P15A5>': ('gao', 2455726444728097, 841149894373344, 'G15h', 'G15h'), 'N<S<G15AX,sG15AX,P15A5>,sG15AX>': ('fam', 121976928173440563255215, 44457579999851129824439, [['G15h', 'T'], ['G15Ah', 'T'], ['G15Ah', 'T']], [[0, 0, 0], [0, 6, 3], [1, 1, 5], [1, 2, 6], [1, 3, 5], [1, 5, 1], [1, 5, 2], [2, 0, 5], [2, 5, 1], [2, 5, 2], [3, 0, 6], [3, 6, 1], [3, 6, 2], [5, 1, 1], [5, 1, 3], [5, 2, 3], [5, 3, 0], [6, 1, 2], [6, 2, 1], [6, 2, 2], [6, 5, 5]]), 'N<S<G15AX,sG15Ah,P15A8>,sG15Ah>': ('fam', 121976928173440563255215, 44500305099870120677381, [['G15Ah', 'T'], ['G15h', 'T'], ['G15Ah', 'T']], [[0, 0, 0], [0, 2, 5], [0, 3, 6], [1, 1, 6], [1, 5, 3], [1, 6, 1], [1, 6, 2], [2, 1, 6], [2, 5, 3], [2, 6, 1], [2, 6, 2], [3, 1, 5], [3, 5, 0], [5, 1, 2], [5, 2, 1], [5, 2, 2], [5, 6, 5], [6, 0, 3], [6, 1, 1], [6, 3, 1], [6, 3, 2]]), 'N<N<S<G15AX,G5,P15A8>,G5>,G5>': ('fam', 2455726444728097, 841149894373344, [['G15h', 'T'], ['G15h', 'T']], [[0, 0], [1, 5], [2, 6], [3, 5], [5, 1], [5, 2], [6, 3]])}
print('step 2: the new side codebooks',flush=True)
FAMKEY={'B':'B','N':'X0','A':'XV','D':'XH','O':'R','H':'PH','V':'PV'}
LABS='BNADOHV'; SEPL={'B':'OHV','N':'ADOHV','A':'NDH','D':'NAV','O':'BN','H':'BNA','V':'BND'}
N3='N<N<S<G15AX,G5,P15A8>,G5>,G5>'
PURE[N3]=(((t15,b),b),b)
from flags import dist as fdist
def prove_family_code(parts,words):
    Gs=[build(g) for g,_ in parts]
    for G in Gs:
        for k in FAMKEY.values():
            if G[k]: check_disjoint_fast(G[k])
    for u in range(len(words)):
        for v in range(u,len(words)):
            wu,wv=words[u],words[v]
            if u!=v and any(LABS[y] in SEPL[LABS[x]] for x,y in zip(wu,wv)):
                # separated labels: verify the families really are separated (no confusable pair at all)
                pass
            conf=True; strict=False
            for G,x,y in zip(Gs,wu,wv):
                c,st=flg(G[FAMKEY[LABS[x]]],G[FAMKEY[LABS[y]]])
                if not c: conf=False; break
                strict|=st
            assert not (conf and (strict or u!=v)), ('confusable words',wu,wv)
            if u!=v and conf: raise AssertionError('distinct words not separated')
def fam_jq(nm,parts,words):
    if nm in PURE:
        ind=~tree_ind(PURE[nm])[0]; j=q=0
        for w in words:
            t=None
            for (g,aut),x in zip(parts,w):
                assert aut=='T'
                d=fdist(build(g)[FAMKEY[LABS[x]]],NX0,NXr); t=d if t is None else np.multiply.outer(t,d)
            j+=int(t.sum()); q+=int(t[ind].sum())
        return j,q
    tys=['x','h','h']; j=q=0
    for w in words:
        ss=[class_dist(build(g)[FAMKEY[LABS[x]]],[ty]) for (g,aut),x,ty in zip(parts,w,tys)]
        d=np.multiply.outer(np.multiply.outer(ss[0],ss[1]),ss[2]); j+=int(d.sum()); q+=q_tree(d,((0,1),2))
    return j,q
NEW=dict(TANGQ)   # unchanged patterns keep Tang's codebooks
for nm,sp in SPEC.items():
    if sp[0]=='keep':
        if nm==N3:
            X,Y=canon('N<S<G15AX,G5,P15A8>,G5>'),G5
            X=gao(X,Y) if False else X
        NEW[nm]=(sp[1],sp[2]); continue
    if sp[0]=='gao':
        _,j0,q0,x,y=sp; X,Y=build(x),build(y); prove_main_code(X,Y); j,q=qcount(nm,X,Y)
        assert j==pgao(X.profile(),Y.profile())[0]
        desc=f'main code of Gao({x}, {y})'
    else:
        _,j0,q0,parts,words=sp; words=[tuple(w) for w in words]; parts=[tuple(p) for p in parts]
        prove_family_code(parts,words); j,q=fam_jq(nm,parts,words)
        desc=f'separated code ({len(words)} words) over families of {[g for g,_ in parts]}'
    assert (j,q)==(j0,q0),(nm,j,q,j0,q0)
    NEW[nm]=(j,q)
    print(f'  [ok] {nm}: J = T({desc}) independent; j = {j}, q = {q}',flush=True)
print('step 3: recursion and top level',flush=True)
def evalM3(jq):
    pp=patp_all(jq); pr={'G5':PROF['G5']}
    for st in tang['gadgets']:
        if st['op']=='hetgao':
            Lp,J0,JH,JV=pp[st['pattern']]; pr[st['name']]=phet(Lp,pr[st['R']],J0,JH,JV)
        else: pr[st['name']]=psig(pr[st['of']])
    inner=pp['N<S<G15AX,G5,P15A8>,G5>']; Lp=pgao(inner[0],PROF['G5']); J0=phet(inner[0],PROF['G5'],inner[1],inner[2],inner[3])
    pr['g0']=phet(Lp,PROF['G5'],(J0[2],J0[3],J0[4],J0[5]),jq[N3],jq[N3])
    vs=[Phi(pr[x[4:-1]]) for x in tang['top']['rule_inputs']]
    return code(K4a,[rule(S3b,vs)]*4)
Mt=evalM3(NEW)
assert M0==int(tang['M'])
print('  [ok] Tang\'s data reproduce his M exactly')
assert Mt>M0
open('stage_side_M.txt','w').write(str(Mt))
print(f'\nM = {Mt}\n')
print(f'CERTIFIED (given Tandon\'s Theorem 1 and the Gao/BPZ lemmas)  Theta(C_7) >= M^(1/680) = {str(rate(Mt))[:18]}...')
print(f'Tang                                                    M_Tang^(1/680) = {str(rate(M0))[:18]}...')
print('OK  (%.0fs)'%(time.time()-t0))

# =====================================================================================================
print('step 4: exact chunk-summary DP, validated on every known count',flush=True)
import sym, symbase, prof as PF, jqc, pat as PT
from sym import size as ssize, count_out as scount, Tx as sTx, uni as suni, cross as scross
B={'GAD':{},'GM':{},'PAT':{},'PM':{}}
for k,g in symbase.GAD.items(): B['GAD'][k]=g.profile(); B['GM'][k]=g.m
for k,(L_,J0_,JH_,JV_) in symbase.PAT.items():
    B['PAT'][k]=(L_.profile(),(ssize(J0_['X0'])+ssize(J0_['XH'])+ssize(J0_['XV']),ssize(J0_['X0']),ssize(J0_['XH']),ssize(J0_['XV'])),
        (ssize(JH_),scount(JH_,L_['X0'])),(ssize(JV_),scount(JV_,L_['X0'])))
    B['PM'][k]=L_.m
    assert B['PAT'][k]==PATP[k],(k,B['PAT'][k],PATP[k])
for k in GAD: assert B['GAD'][k]==PROF[k],k
PF.BASEDATA=B
print('  [ok] symbolic base gadgets and Tan patterns agree with the physical ones',flush=True)
for nm,ref in [('C1',(symbase.Jp,symbase.G10['X0'],27488)),('C2',(symbase.J15,symbase.G15X['X0'],12839823)),
               ('C3',(symbase.G15h['X'],symbase.G15X['X0'],14045805)),('q15',(symbase.J15,symbase.G15h['X0'],12872271)),
               ('C4',(sTx(sym.sgao(symbase.G15h,symbase.G15h)['I']),sym.sgao(symbase.G15AX,symbase.G15Ah.sigma())['X0'],841760069965664))]:
    v=scount(ref[0],ref[1]); assert v==ref[2],(nm,v); print(f'  [ok] DP {nm} = {v}',flush=True)
for nm,(j0,q0) in TANGQ.items():
    v=jqc.getjq(nm); assert v==(j0,q0),(nm,v); print(f'  [ok] DP Tang q[{nm}] = {q0}',flush=True)
LABS4='BNADOHV'
def sym_fam(parts,words):
    Gs=[PT.gadget(g) for g,_ in parts]; m=sum(G.m for G in Gs); terms=[]
    for w in words:
        t=None
        for G,(g,aut),x in zip(Gs,parts,w):
            assert aut=='T'; f=sTx(G[FAMKEY[LABS4[x]]]); t=f if t is None else scross(t,f)
        terms.append(t)
    return suni(terms,m)
for nm,sp in SPEC.items():
    if sp[0]=='fam':
        J=sym_fam([tuple(p) for p in sp[3]],[tuple(w) for w in sp[4]]); L_=jqc.pleft(nm)
        v=(ssize(J),scount(J,L_['X0'])); assert v==(sp[1],sp[2]),(nm,v); print(f'  [ok] DP side-stage codebook q[{nm}] = {v[1]}',flush=True)
print('step 5: new side codebooks',flush=True)
SPEC4={'N<N<N<N<P15A8,G5>,sG5>,G5>,sG5>': (902701887614070095, 319728170791727079, [['G15Ah', 'T'], ['G10D', 'T'], ['G10D', 'T']], [[0, 0, 0], [0, 2, 6], [0, 3, 5], [1, 1, 4], [1, 5, 2], [1, 6, 1], [1, 6, 3], [2, 1, 5], [2, 5, 2], [2, 6, 1], [2, 6, 3], [3, 1, 6], [3, 5, 0], [5, 1, 3], [5, 2, 1], [5, 2, 3], [5, 6, 6], [6, 0, 2], [6, 1, 1], [6, 3, 1], [6, 3, 3]]), 'N<N<N<P15A8,G5>,sG5>,G5>': (2455957572166433, 841115078149008, [['G10D', 'T'], ['G10D', 'T'], ['G10A', 'T']], [[0, 0, 0], [0, 2, 5], [1, 1, 5], [1, 3, 6], [1, 5, 1], [1, 5, 3], [1, 6, 2], [2, 1, 5], [2, 3, 5], [2, 6, 0], [3, 1, 6], [3, 3, 6], [3, 5, 0], [5, 0, 3], [5, 2, 1], [5, 2, 2], [5, 6, 5], [6, 1, 1], [6, 1, 2], [6, 3, 1], [6, 3, 2]]), 'N<N<P15A8,G5>,sG5>': (6682409489071, 2167993673079, [['G10A', 'T'], ['G10', 'T'], ['G5', 'T']], [[0, 0, 0], [0, 2, 6], [0, 3, 5], [1, 1, 6], [1, 5, 1], [1, 5, 2], [1, 6, 3], [2, 1, 5], [2, 5, 2], [2, 6, 1], [2, 6, 3], [3, 1, 6], [3, 5, 0], [5, 1, 1], [5, 1, 3], [5, 2, 1], [5, 2, 3], [5, 6, 6], [6, 0, 2], [6, 3, 1], [6, 3, 3]]), 'N<P15A8,G5>': (18184849857, 5416242120, [['G10A', 'T'], ['G5', 'T'], ['sG5', 'T']], [[0, 0, 0], [0, 5, 3], [0, 6, 2], [1, 1, 4], [1, 2, 5], [1, 3, 6], [1, 6, 1], [2, 1, 6], [2, 2, 5], [2, 3, 6], [2, 5, 1], [3, 0, 5], [3, 6, 1], [5, 1, 1], [5, 1, 2], [5, 3, 1], [5, 3, 2], [5, 6, 5], [6, 1, 3], [6, 2, 0], [6, 3, 3]]), 'N<N<N<P10A,sG10A>,sG10A>,sG15AX>': (121976928173440563255215, 44457579999851129824439, [['G15Dh', 'T'], ['G15h', 'T'], ['G15Dh', 'T']], [[0, 0, 0], [0, 2, 6], [0, 3, 5], [1, 1, 5], [1, 5, 2], [1, 6, 1], [1, 6, 3], [2, 1, 6], [2, 5, 0], [3, 1, 5], [3, 5, 2], [3, 6, 1], [3, 6, 3], [5, 0, 2], [5, 3, 1], [5, 3, 3], [6, 1, 1], [6, 1, 3], [6, 2, 1], [6, 2, 3], [6, 6, 6]]), 'N<N<P10A,sG10A>,sG10A>': (2455957572166433, 841115078149008, [['G10A', 'T'], ['G10', 'T'], ['G10D', 'T']], [[0, 0, 0], [0, 2, 5], [0, 3, 6], [1, 1, 5], [1, 5, 1], [1, 5, 3], [1, 6, 2], [2, 1, 5], [2, 5, 1], [2, 5, 3], [2, 6, 2], [3, 1, 6], [3, 6, 0], [5, 1, 3], [5, 3, 1], [5, 3, 3], [5, 4, 6], [6, 0, 2], [6, 1, 1], [6, 2, 1], [6, 2, 3]]), 'N<P10A,sG10A>': (18184849857, 5416242120, [['G5', 'T'], ['G10D', 'T'], ['G5', 'T']], [[0, 0, 0], [0, 6, 2], [1, 1, 5], [1, 2, 5], [1, 3, 6], [1, 5, 3], [1, 6, 1], [2, 0, 5], [2, 5, 1], [2, 5, 3], [3, 0, 6], [3, 6, 1], [3, 6, 3], [5, 1, 3], [5, 3, 1], [5, 3, 3], [5, 6, 6], [6, 1, 1], [6, 1, 2], [6, 2, 0], [6, 3, 2]]), 'N<N<N<P10A,G5>,G5>,G5>': (6682409489071, 2167993673079, [['G10A', 'T'], ['G5', 'T'], ['G10A', 'T']], [[0, 0, 0], [0, 5, 3], [0, 6, 2], [1, 1, 4], [1, 2, 5], [1, 3, 6], [1, 4, 1], [2, 1, 6], [2, 2, 5], [2, 3, 6], [2, 6, 1], [3, 0, 5], [3, 5, 1], [5, 1, 2], [5, 2, 0], [5, 3, 2], [5, 6, 5], [6, 1, 1], [6, 1, 3], [6, 3, 1], [6, 3, 3]]), 'N<N<P10A,G5>,G5>': (18184849857, 5416242120, [['G10A', 'T'], ['G5', 'T'], ['G5', 'T']], [[0, 0, 0], [0, 5, 3], [0, 6, 2], [1, 1, 5], [1, 2, 5], [1, 3, 6], [1, 5, 1], [2, 1, 6], [2, 2, 5], [2, 3, 6], [2, 6, 1], [3, 0, 5], [3, 5, 1], [5, 1, 1], [5, 1, 2], [5, 2, 0], [5, 3, 2], [5, 6, 5], [6, 1, 3], [6, 3, 1], [6, 3, 3]]), 'N<P10A,G5>': (49496015, 12840111, [['G5', 'T'], ['G5', 'T'], ['sG5', 'T']], [[0, 0, 0], [0, 2, 5], [1, 1, 6], [1, 3, 6], [1, 4, 1], [1, 5, 3], [1, 6, 2], [2, 1, 5], [2, 3, 5], [2, 6, 0], [3, 1, 6], [3, 3, 6], [3, 5, 0], [4, 1, 1], [5, 0, 3], [5, 2, 1], [5, 2, 2], [6, 1, 2], [6, 3, 1], [6, 3, 2], [6, 6, 5]]), 'N<N<N<N<N<P15A8,G5>,G5>,G5>,G5>,sG10A>': (121976928173440563255215, 44457579999851129824439, [['G15h', 'T'], ['G15Ah', 'T'], ['G15Ah', 'T']], [[0, 0, 0], [0, 3, 5], [1, 1, 4], [1, 2, 6], [1, 5, 2], [1, 6, 1], [1, 6, 3], [2, 1, 5], [2, 2, 5], [2, 5, 0], [3, 1, 6], [3, 2, 6], [3, 6, 0], [4, 1, 1], [5, 0, 3], [5, 3, 1], [5, 3, 2], [5, 5, 5], [6, 1, 2], [6, 2, 1], [6, 2, 2]]), 'N<N<N<N<P15A8,G5>,G5>,G5>,G5>': (902701887614070095, 319728170791727079, [['G10D', 'T'], ['G15Ah', 'T'], ['G10', 'T']], [[0, 0, 0], [0, 3, 5], [1, 1, 5], [1, 2, 6], [1, 5, 2], [1, 6, 1], [1, 6, 3], [2, 1, 5], [2, 2, 5], [2, 6, 0], [3, 1, 6], [3, 2, 6], [3, 5, 1], [3, 5, 2], [3, 6, 3], [4, 1, 1], [5, 0, 3], [5, 2, 1], [6, 0, 2], [6, 3, 1], [6, 5, 4]]), 'N<N<N<P15A8,G5>,G5>,G5>': (2455957572166433, 841115078149008, [['G10', 'T'], ['G10A', 'T'], ['G10A', 'T']], [[0, 0, 0], [0, 6, 3], [1, 1, 6], [1, 2, 6], [1, 3, 5], [1, 4, 1], [1, 5, 2], [2, 0, 5], [2, 5, 1], [2, 5, 2], [3, 0, 6], [3, 6, 1], [3, 6, 2], [5, 1, 1], [5, 1, 3], [5, 2, 3], [5, 3, 0], [6, 1, 2], [6, 2, 1], [6, 2, 2], [6, 5, 5]]), 'N<N<P15A8,G5>,G5>': (6682409489071, 2167993673079, [['G10A', 'T'], ['G10D', 'T'], ['sG5', 'T']], [[0, 0, 0], [0, 5, 3], [0, 6, 2], [1, 1, 5], [1, 2, 5], [1, 3, 6], [1, 6, 1], [2, 1, 6], [2, 2, 5], [2, 3, 6], [2, 6, 1], [3, 0, 5], [3, 5, 1], [5, 1, 1], [5, 1, 2], [5, 2, 0], [5, 3, 2], [5, 6, 6], [6, 1, 3], [6, 3, 1], [6, 3, 3]])}
def ptree(nm):
    nm=PF.norm_pat(nm)
    if nm.startswith('P10'): return (b,b)
    if nm.startswith('P15'): return ((b,b),b)
    q,c=PF.split_top(nm[2:-1]); return (ptree(q),{'G5':b,'sG5':b,'G10':(b,b),'sG10A':(b,b),'G10A':(b,b),'sG15AX':((b,b),b)}[c])
JQ4={}
for nm,(j0,q0,parts,words) in SPEC4.items():
    parts=[tuple(p) for p in parts]; words=[tuple(w) for w in words]
    prove_family_code(parts,words)
    J=sym_fam(parts,words); L_=jqc.pleft(nm); assert J.k==L_.m
    j,q=ssize(J),scount(J,L_['X0'])
    # independent second count: per-coordinate flag tensors (v3 method, pure-Gao reference)
    PURE[nm]=ptree(nm); j2,q2=fam_jq(nm,parts,words)
    assert (j,q)==(j0,q0)==(j2,q2),(nm,j,q,j2,q2,j0,q0)
    JQ4[PF.norm_pat(nm)]=(j,q)
    print(f'  [ok] {nm}: J = T(separated code, {len(words)} words, over {[g for g,_ in parts]}) independent; j = {j}, q = {q} (two methods)',flush=True)
print('step 6: recursion and top level',flush=True)
# the recursion of prof.World reproduces Tang's and v3's M
TS=['H[N<S<G15X,G10,P15X>,G5>](G5)','s(H[N<S<G15AX,sG15AX,P15A5>,sG15AX>](s(H[N<S<G15AX,G5,P15A8>,G5>](G5))))','s(H[N<S<G15AX,sG15Ah,P15A8>,sG15Ah>](s(H[P10A](G5))))']
assert PF.topM(*[PF.World(TANGQ).gp(s) for s in TS])==M0
V3S=['H[N<N<S<G15AX,G5,P15A8>,G5>,G5>](G5)']+TS[1:]
assert PF.topM(*[PF.World(NEW).gp(s) for s in V3S])==Mt
print('  [ok] the general recursion reproduces Tang\'s M and the side-stage M exactly',flush=True)
SL4=['s(H[N<N<N<N<P15A8,G5>,sG5>,G5>,sG5>](sG5))', 's(H[N<N<N<P10A,sG10A>,sG10A>,sG15AX>](s(H[N<N<N<P10A,G5>,G5>,G5>](G5))))', 's(H[N<N<N<N<N<P15A8,G5>,G5>,G5>,G5>,sG10A>](sG10A))']
W4=PF.World({**NEW,**JQ4})
for nm in JQ4: assert W4.pp(nm)[2]==JQ4[nm]
d4=20*sum(PF.gdim(s) for s in SL4); assert d4==680
M4=PF.topM(*[W4.gp(s) for s in SL4])
assert M4>Mt>M0
open('stage_nesting_M.txt','w').write(str(M4))
print(f'\nM = {M4}\n')
print(f'CERTIFIED (given Tandon\'s Theorem 1 and the Gao/BPZ lemmas)  Theta(C_7) >= M^(1/680) = {str(rate(M4))[:18]}...')
print(f'side stage                                                      M_side^(1/680) = {str(rate(Mt))[:18]}...')
print('OK nesting stage  (%.0fs)'%(time.time()-t0))

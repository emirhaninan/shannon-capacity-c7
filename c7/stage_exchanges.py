#!/usr/bin/env python3
"""v5 exact check = v4 (flat label-code side codebooks over copies of G5, J15', s*) with the 10-dim side codebook J+
read from an exchange file (default exchanges.txt: C1 = 27512, C3 = 14047245).  Usage:
    python3 stage_exchanges.py [jplus.txt [M_out.txt [codes.json]]] [--no-validate]
With a J+ other than Tang's it first re-runs itself with Tang's J+ (exchanges_tang.txt), which must reproduce all 13
Tan/Tang counts, every stored v4 codebook count and the v4 M exactly; then it rebuilds everything with the given J+
(G15h, G15Ah, G15Dh, Tan's pattern data, C1..C4, q15, the 10-dim maps of the sG15Ah references, all q's of the
sG15Ah-reference codebooks) and proves J+ independent directly (I_10 by its blocks; every inserted word against the
explicit words of T(I_10) in its neighbourhood).

v4 docstring:
v4 exact check:  Theta(C_7) >= M^(1/680)   (v3: 3.2588392704292..., Tang d = 680: 3.2588387054446...)

v4 = v3 with (a) the side codebooks of all seven used sibling/nested left patterns replaced by FLAT LABEL CODES:
J = T(union over words w in K of F_{w_1}(G5) x ... x F_{w_k}(G5)), F = the BPZ families (B, X^0, X^V, X^H, P^H, P^V) of
the base gadget, K a set of k-letter words (k = 4, 5, 6, 9) such that any two distinct words have, at some
coordinate, two families with no confusable-or-equal pair (K found by coordinate ascent over trees of 'rule gadgets');
and (b) Tan's base codebook J15 = T(I(G15X)) replaced by the 3-letter label code of the same kind with
|J15'| = 49496015 > 49495055 and a larger q.
The checker
  1. (as v3) rebuilds all block sets from the BPZ base data and re-derives all 13 of Tan's / Tang's counts exactly;
  2. proves directly that J15' and every new side codebook is independent: exact confusability matrix of the
     (transformed) base families, every family independent, every pair of distinct words separated at some
     coordinate (vectorised over all pairs); counts j exactly and q = |J minus N(X^0(L))| exactly (flag-tensor
     method for pure-Gao references, chunk method with exact 10-dimensional maps for sG15Ah references);
  3. rebuilds Tan's pattern data with J15' (q counted directly with count_outside_fast) and evaluates the
     profile recursion, S3b and K4a in integers; compares M with Tang's M and v3's M at d = 680.
Data: family_codes.json.  No code of Tan or Tang is imported.
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
if len(sys.argv)>1 and sys.argv[1]!='exchanges_tang.txt' and '--no-validate' not in sys.argv:
    import subprocess
    print('validation run with Tang\'s J+ (all 13 Tan/Tang counts, every family-stage codebook count, the family-stage M):',flush=True)
    r=subprocess.run([sys.executable,os.path.abspath(__file__),'exchanges_tang.txt','/dev/null'],capture_output=True,text=True)
    print('\n'.join('   | '+l for l in r.stdout.splitlines()),flush=True)
    assert r.returncode==0 and 'reproduces the family-stage M exactly' in r.stdout, r.stderr[-2000:]
    print('validation run OK; now the given J+:',sys.argv[1],flush=True)
sys.argv=[a for a in sys.argv if a!='--no-validate']
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
# ---- J+ from an exchange file: J+ = T(I_10) minus the '-' words plus the '+' words ----
JFILE=sys.argv[1] if len(sys.argv)>1 else 'exchanges.txt'
REM=[];INS=[]
for ln in open(JFILE):
    ln=ln.split('#')[0].split()
    if not ln: continue
    (REM if ln[0]=='-' else INS).append((int(ln[1]),int(ln[2])))
assert ln is not None and len(set(REM))==len(REM) and len(set(INS))==len(INS)
VALIDATE = sorted(REM)==sorted(tuple(r) for r,_ in exch) and sorted(INS)==sorted(tuple(i) for _,i in exch)
raw=Tset(G10['I']); check_disjoint_fast(raw)
prove_gao_main_independent_later=True
def raw_words_near(w):
    """all words of T(I_10) in the closed neighbourhood of w (exact, from the product blocks)"""
    out=set(); A=anb(atom_of([w[0]])); B=anb(atom_of([w[1]]))
    for bl in raw:
        A0=np.nonzero(_ATOMS[bl[0]] & A)[0]; A1=np.nonzero(_ATOMS[bl[1]] & B)[0]
        out|={(int(x),int(y)) for x in A0 for y in A1}
    return out
in_raw=lambda w: any(_ATOMS[a][w[0]] and _ATOMS[b][w[1]] for a,b in raw)
assert all(in_raw(w) for w in REM), 'a removed word is not in T(I_10)'
REMS=set(REM)
for w in INS:
    assert raw_words_near(w) <= REMS, ('inserted word confusable with a kept word', w)
NB1={}
def conf(p,q):
    return all(min((a-b)%7,(b-a)%7)<=1 for a,b in zip(dec(p[0])+dec(p[1]),dec(q[0])+dec(q[1])))
assert not any(conf(INS[i],INS[k]) for i in range(len(INS)) for k in range(i+1,len(INS))), 'inserted words not independent'
Jp=raw
for w in REM: Jp=remove_word(Jp,w)
for w in INS: Jp.append((atom_of([w[0]]),atom_of([w[1]])))
check_disjoint_fast(Jp); JSIZE=size(Jp); assert JSIZE==G10.profile()[0]-len(REM)+len(INS)
print(f'  [ok] J+ from {JFILE}: |J+| = {JSIZE} ({len(REM)} removed, {len(INS)} inserted); '
      'inserted words independent and non-confusable with the kept words of T(I_10)'+(' [Tang\'s J+: validation mode]' if VALIDATE else ''),flush=True)
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
M0=int(tang['M'])
if VALIDATE: assert evalM(TANGQ)==M0; print('Tang M reproduced',flush=True)

assert G5.profile()==(367,8,367,322,26,19)
C1=count_outside_fast(Jp,G10['X0']); C2=count_outside_fast(J15,G15X['X0']); q15=count_outside_fast(J15,G15h['X0'])
C3=count_outside_fast(G15h['X'],G15X['X0']); C4=count_outside_fast(Tset(gao(G15h,G15h)['I']),gao(G15AX,G15Ah.sigma())['X0'])
for nm,v,ref in [('C1',C1,27488),('C2',C2,12839823),('C3',C3,14045805),('C4',C4,841760069965664),('q15',q15,12872271)]:
    if VALIDATE: assert v==ref,(nm,v,ref)
    print(f'  [{"ok" if VALIDATE else "new"}] {nm} = {v}   (Tan/Tang: {ref}, diff {v-ref:+d})',flush=True)
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
CANONQ={}
for nm,(j0,q0) in TANGQ.items():
    X,Y=canon(nm); j,q=qcount(nm,X,Y); CANONQ[nm]=(j,q)
    if VALIDATE: assert (j,q)==(j0,q0),(nm,j,q,j0,q0)
    print(f'  [{"ok" if VALIDATE else "new"}] Tang count (j,q)[{nm}] = {j}, {q}'+('' if VALIDATE else f'   (Tang: {j0}, {q0})'),flush=True)
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
prove_main_code(G5,G5)
print('  [ok] I_10 = main code of Gao(G5, G5) proved independent directly from its blocks (so T(I_10) is; T is an automorphism); with the exchange check above, J+ is independent',flush=True)
# ======================= v4 =======================
from flags import dist as fdist
FAMKEY={'B':'B','N':'X0','A':'XV','D':'XH','O':'R','H':'PH','V':'PV'}
LABS='BNADOHV'
N3='N<N<S<G15AX,G5,P15A8>,G5>,G5>'
PURE[N3]=(((t15,b),b),b)
HTYPES={'S<G15AX,sG15Ah,P15A8>':(['x','h'],(0,1)),'N<S<G15AX,sG15Ah,P15A8>,sG15Ah>':(['x','h','h'],((0,1),2))}
DATA4=json.load(open(sys.argv[3] if len(sys.argv)>3 else 'family_codes.json'))
_AUTMAP={}
def aut_map(spec):
    """automorphism of C_7^5: y_j = s_j x_{pi(j)} + c_j (mod 7) as a permutation of the 16807 codes"""
    key=json.dumps(spec)
    if key not in _AUTMAP:
        (pi,sg),c=spec
        assert sorted(pi)==list(range(5)) and all(x in (1,-1) for x in sg)
        D=np.array([dec(x) for x in range(N5)])
        Y=(D[:,list(pi)]*np.array(sg)+np.array(c))%7
        P=(Y*np.array([7**j for j in range(5)])).sum(1)
        assert len(set(P.tolist()))==N5
        _AUTMAP[key]=P
    return _AUTMAP[key]
_AA={}
def aut_atom_c(a,spec):
    k=(a,json.dumps(spec))
    if k not in _AA:
        m=np.zeros(N5,bool); m[aut_map(spec)[_ATOMS[a]]]=True; _AA[k]=atom(m)
    return _AA[k]
def leaf_blocks(name,aut,lab):
    bl=build(name)[FAMKEY[lab]]
    if aut=='T': return Tset(bl)
    if aut=='I': return list(bl)
    assert build(name).m==1
    return [tuple(aut_atom_c(a,aut) for a in b) for b in bl]
def prove_flat(leaves,auts,words):
    """direct proof that union_w prod_i aut_i(F_{w_i}(leaf_i)) is an independent set (blocks pairwise disjoint)"""
    labs=sorted({c for w in words for c in w})
    CF=[]
    for name,aut in zip(leaves,auts):
        Bl={l:leaf_blocks(name,aut,l) for l in labs}
        for l in labs:
            if not Bl[l]: continue
            check_disjoint_fast(Bl[l]); c,st=flg(Bl[l],Bl[l]); assert c and not st,('family not independent',name,l)
        CF.append({(x,y):(flg(Bl[x],Bl[y])[0] if Bl[x] and Bl[y] else False) for x in labs for y in labs})
    assert len(set(words))==len(words)
    W=np.array([[labs.index(c) for c in w] for w in words],dtype=np.int64); n=len(words); k=W.shape[1]
    M=[np.array([[CF[i][(x,y)] for y in labs] for x in labs]) for i in range(k)]
    for s in range(0,n,512):
        acc=np.ones((min(512,n-s),n),bool)
        for i in range(k): acc&=M[i][W[s:s+512,i][:,None],W[None,:,i]]
        acc[np.arange(acc.shape[0]),np.arange(s,s+acc.shape[0])]=False
        assert not acc.any(), 'two distinct words not separated'
    return True
def flat_tensor(leaves,auts,words):
    """exact flag tensor sum_w prod_i dist(aut_i F_{w_i}) (trie recursion, Python integers)"""
    vt=[{} for _ in leaves]
    def v(i,l):
        if l not in vt[i]: vt[i][l]=fdist(leaf_blocks(leaves[i],auts[i],l),NX0,NXr,T=False)
        return vt[i][l]
    def rec(ws,i):
        if i==len(leaves): return np.array(1,dtype=object)
        g=defaultdict(list)
        for w in ws: g[w[i]].append(w)
        tot=None
        for l,sub in g.items():
            t=np.multiply.outer(v(i,l),rec(sub,i+1)); tot=t if tot is None else tot+t
        return tot
    return rec(sorted(words),0)
def class_dist_raw(blocks,types):
    """flag/chunk distribution of blocks that are already transformed (class_dist applies T itself)"""
    acc=np.zeros((4,)*len(types),dtype=object)
    for bl in blocks:
        vs=[(chunk_h if ty=='h' else chunk_x)(*bl[3*i:3*i+3]) for i,ty in enumerate(types)]
        t=vs[0]
        for v in vs[1:]: t=np.multiply.outer(t,v)
        acc=acc+t
    return acc
def flat_jq(nm,leaves,auts,words):
    j=sum(math.prod(size(build(g)[FAMKEY[c]]) for g,c in zip(leaves,w)) for w in words)
    if nm in HTYPES:
        types,tree=HTYPES[nm]
        blocks=[]
        for w in words:
            for combo in itertools.product(*[leaf_blocks(g,a,c) for g,a,c in zip(leaves,auts,w)]):
                blocks.append(tuple(a for bl in combo for a in bl))
        d=class_dist_raw(blocks,types); assert int(sum(d.ravel()))==j
        return j,q_tree(d,tree)
    t=flat_tensor(leaves,auts,words); assert int(t.sum())==j
    return j,int(t[~tree_ind(PURE[nm])[0]].sum())
print('step 2a: base codebook J15\'',flush=True)
d15=DATA4['J15']; W15=d15['words']
prove_flat(d15['leaves'],d15['auts'],W15)
J15n=[tuple(a for bl in combo for a in bl) for w in W15
      for combo in itertools.product(*[leaf_blocks(g,a,c) for g,a,c in zip(d15['leaves'],d15['auts'],w)])]
check_disjoint_fast(J15n)
j15n=size(J15n); q15n={k:count_outside_fast(J15n,PAT[k][0]['X0']) for k in ('P15X','P15A8','P15D')}
assert j15n==d15['j'] and all(v==d15['q'] for v in q15n.values()),(j15n,q15n)
print(f'  [ok] J15\' = s*(label code, {len(W15)} words over G5^3) independent; |J15\'| = {j15n} (Tan: {size(J15)}), '
      f'q vs X0(G15X/G15AX/G15DX) = {q15n["P15X"]} (Tan: {C2})',flush=True)
PAT2={}
for k,(L,J0_,JH,JV) in PAT.items():
    PAT2[k]=(L,J0_,J15n if JH is J15 else JH,J15n if JV is J15 else JV)
PATP2={}
for k,(L,J0_,JH,JV) in PAT2.items():
    PATP2[k]=(L.profile(),(size(J0_['X0'])+size(J0_['XH'])+size(J0_['XV']),size(J0_['X0']),size(J0_['XH']),size(J0_['XV'])),
             (size(JH),count_outside_fast(JH,L['X0'],check=False)),(size(JV),count_outside_fast(JV,L['X0'],check=False)))
print('  [ok] Tan pattern data rebuilt with J15\'',flush=True)
print('step 2b: the new side codebooks',flush=True)
NEW=dict(CANONQ)
for nm,sp in DATA4['patterns'].items():
    leaves,auts,words=sp['leaves'],sp['auts'],sp['words']
    t1=time.time()
    prove_flat(leaves,auts,words); j,q=flat_jq(nm,leaves,auts,words)
    assert j==sp['j'],(nm,j,sp['j'])
    if VALIDATE or nm not in HTYPES: assert q==sp['q'],(nm,q,sp['q'])   # pure-reference q's do not depend on J+
    NEW[nm]=(j,q)
    print(f'  [ok] {nm}: J = sigma(label code, {len(words)} words over {"x".join(leaves)}; per-coordinate automorphisms {sorted(set("T" if a=="T" else "s*" for a in auts))}) independent; j = {j}, q = {q}  ({time.time()-t1:.0f}s)',flush=True)
NEW.setdefault(N3,None); assert NEW[N3] is not None
print('step 3: recursion and top level',flush=True)
def patp_all2(PP,jq):
    pp=dict(PP)
    for nm in ORDER:
        if nm.startswith('S<'):
            a,b_,p=nm[2:-1].split(','); Lp=pgao(PROF[a],PROF[b_]); inner=PP[p]; C=PROF[b_]
        else:
            inn,c=nm[2:-1].rsplit('>,',1); inn+='>'; Lp=pgao(pp[inn][0],PROF[c]); inner=pp[inn]; C=PROF[c]
        J0_=phet(inner[0],C,inner[1],inner[2],inner[3])
        j,q=jq[nm]; pp[nm]=(Lp,(J0_[2],J0_[3],J0_[4],J0_[5]),(j,q),(j,q))
    return pp
def evalM4(PP,jq):
    pp=patp_all2(PP,jq); pr={'G5':PROF['G5']}
    for st in tang['gadgets']:
        if st['op']=='hetgao':
            Lp,J0_,JH,JV=pp[st['pattern']]; pr[st['name']]=phet(Lp,pr[st['R']],J0_,JH,JV)
        else: pr[st['name']]=psig(pr[st['of']])
    inner=pp['N<S<G15AX,G5,P15A8>,G5>']; Lp=pgao(inner[0],PROF['G5']); J0_=phet(inner[0],PROF['G5'],inner[1],inner[2],inner[3])
    pr['g0']=phet(Lp,PROF['G5'],(J0_[2],J0_[3],J0_[4],J0_[5]),jq[N3],jq[N3])
    vs=[Phi(pr[x[4:-1]]) for x in tang['top']['rule_inputs']]
    return code(K4a,[rule(S3b,vs)]*4)
if VALIDATE: assert evalM(TANGQ)==int(tang['M']); print('  [ok] Tang\'s data reproduce his M exactly')
M3=int(open('stage_side_M.txt').read()); M4=int(open('stage_family_M.txt').read())
Mt=evalM4(PATP2,NEW)
if VALIDATE: assert Mt==M4; print('  [ok] Tang\'s J+ reproduces the family-stage M exactly')
assert Mt>M3>M0
MOUT=sys.argv[2] if len(sys.argv)>2 else 'stage_exchanges_M.txt'
open(MOUT,'w').write(str(Mt))
print(f'\nM = {Mt}\n')
print(f'CERTIFIED (given Tandon\'s Theorem 1 and the Gao/BPZ lemmas)  Theta(C_7) >= M^(1/680) = {str(rate(Mt))[:18]}...')
print(f'family stage (Tang\'s J+)                                M_family^(1/680)   = {str(rate(M4))[:18]}...   M > M_family: {Mt>M4}')
print(f'side stage                                                      M_side^(1/680)   = {str(rate(M3))[:18]}...')
print(f'Tang                                                    M_Tang^(1/680) = {str(rate(M0))[:18]}...')
print('OK  (%.0fs)'%(time.time()-t0))

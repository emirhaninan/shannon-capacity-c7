"""Pattern parsing / building (symbolic).  name grammar:  base names in PAT,  S<A,B,P>,  N<Q,C>."""
from symbase import *
def split_top(s):
    """split 'X,Y,Z' at top-level commas"""
    out=[];d=0;cur=''
    for ch in s:
        if ch in '<[(': d+=1
        if ch in '>])': d-=1
        if ch==',' and d==0: out.append(cur); cur=''
        else: cur+=ch
    out.append(cur); return out
def parse(nm):
    if nm in PAT: return ('base',nm)
    if nm.startswith('S<'):
        a,b,p=split_top(nm[2:-1]); return ('S',a,b,p)
    if nm.startswith('N<'):
        q,c=split_top(nm[2:-1]); return ('N',q,c)
    raise KeyError(nm)
CODEBOOK={}     # pattern name -> symbolic J (default canonical)
_P={}
def gadget(nm):
    """library gadget names: GAD names, or H[pattern](R), s(...)"""
    if nm in GAD: return GAD[nm]
    if nm.startswith('s(') and nm.endswith(')'): return gadget(nm[2:-1]).sigma()
    if nm.startswith('H['):
        d=0
        for i,ch in enumerate(nm):
            if ch=='[': d+=1
            if ch==']':
                d-=1
                if d==0: break
        pn=nm[2:i]; rn=nm[i+2:-1]
        L,J0,JH,JV=pattern(pn); return shetgao(L,gadget(rn),J0,JH,JV)
    if nm.startswith('Gao(') :
        import prof as _pf
        a,b=_pf.split_top(nm[4:-1]); return sgao(gadget(a),gadget(b))
    raise KeyError(nm)
def leftgad(nm):
    t=parse(nm)
    if t[0]=='base': return PAT[nm][0]
    if t[0]=='S': return sgao(gadget(t[1]),gadget(t[2]))
    return sgao(leftgad(t[1]),gadget(t[2]))
def canon_xy(nm):
    t=parse(nm)
    if t[0]=='S': return MAINS[gadget(t[1]).m],MAINS[gadget(t[2]).m]
    X,Y=canon_xy(t[1]); return sgao(X,Y),MAINS[gadget(t[2]).m]
def canon_J(nm):
    X,Y=canon_xy(nm); return Tx(main_code(X,Y))
def pattern(nm):
    """(L, J0, JH, JV) symbolic"""
    import prof as _pf
    nm=_pf.norm_pat(nm)
    if nm in PAT: return PAT[nm]
    key=(nm,id(CODEBOOK.get(nm)))
    if key in _P: return _P[key]
    t=parse(nm)
    if True:
        Lq,J0q,JHq,JVq=pattern(t[1]); C=gadget(t[2])
        L=sgao(Lq,C); J0=shetgao(Lq,C,J0q,JHq,JVq).aux()
    if nm not in CODEBOOK:
        import jqc; J=Tx(main_code(*jqc.canon_xy(nm)))
    else: J=CODEBOOK[nm]
    _P[key]=(L,J0,J,J); return _P[key]

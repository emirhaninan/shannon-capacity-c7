"""exact (j,q) for (pattern, codebook) pairs, cached on disk.  codebook spec: ('canon',) or ('gao',X,Y) or ('fam',parts,words)"""
import pickle, os, time
import pat as P
from pat import *
from prof import norm_pat, split_top
FN=os.environ.get('C7_JQCACHE','jq_cache.pkl')
CACHE={}   # no disk cache in the checker
def save(): pickle.dump(CACHE,open(FN+'.tmp','wb')); os.replace(FN+'.tmp',FN)
LABS='BNADOHV'; FAMKEY={'B':'B','N':'X0','A':'XV','D':'XH','O':'R','H':'PH','V':'PV'}
def Mg(n):
    if n in MAINS: return MAINS[n]
    return sgao(Mg(n-3),G15h)
def pleft(nm):
    nm=norm_pat(nm)
    if nm in PAT: return PAT[nm][0]
    q,c=split_top(nm[2:-1]); return sgao(pleft(q),P.gadget(c))
def canon_xy(nm):
    q,c=split_top(nm[2:-1]); C=P.gadget(c)
    if q in PAT: return MAINS[PAT[q][0].m],Mg(C.m)
    X,Y=canon_xy(q); return sgao(X,Y),Mg(C.m)
def codebook(spec):
    if spec[0]=='flat':
        import flatlib; return flatlib.build(spec)
    if spec[0]=='gao': return Tx(main_code(P.gadget(spec[1]),P.gadget(spec[2])))
    if spec[0]=='fam':
        parts,words=spec[1],spec[2]; Gs=[P.gadget(g) for g,_ in parts]; m=sum(G.m for G in Gs)
        terms=[]
        for w in words:
            t=None
            for G,(g,aut),x in zip(Gs,parts,w):
                f=G[FAMKEY[LABS[x]]]; f=Tx(f) if aut=='T' else f
                t=f if t is None else cross(t,f)
            terms.append(t)
        return uni(terms,m)
    raise KeyError(spec)
def getjq(pn,spec=('canon',)):
    pn=norm_pat(pn); key=(pn,spec)
    if key not in CACHE:
        L=pleft(pn)
        J=Tx(main_code(*canon_xy(pn))) if spec==('canon',) else codebook(spec)
        assert J.k==L.m,(pn,spec,J.k,L.m)
        CACHE[key]=(size(J),count_out(J,L['X0']))
    return CACHE[key]

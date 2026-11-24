"""Symbolic versions of the base gadgets and Tan's / Tang's patterns."""
import time
from engine import load_base, gao, Tset, remove_word, atom_of
import sym
from sym import *
t0=time.time()
_G5p, exch = load_base()
G5=from_phys(_G5p); sG5=G5.sigma()
_G10p=gao(_G5p,_G5p)
import os as _os, json as _json
_JFILE=_os.environ.get('C7_JPLUS')      # exchange file (- / + words); default: Tandon's 8 exchanges
if _JFILE:
    REM=[];INS=[]
    for ln in open(_JFILE):
        ln=ln.split('#')[0].split()
        if ln: (REM if ln[0]=='-' else INS).append((int(ln[1]),int(ln[2])))
else:
    REM=[tuple(r) for r,_ in exch]; INS=[tuple(i) for _,i in exch]
_Jp=Tset(_G10p['I'])
for w in REM: _Jp=remove_word(_Jp,w)
for w in INS: _Jp.append((atom_of([w[0]]),atom_of([w[1]])))
Jp=blk(_Jp,2)
G10=sgao(G5,G5); G10A=sgao(sG5,G5); G10D=sgao(G5,sG5)
X10=G10['X']
G15X=sgao(G10,G5); G15h=shetgao(G10,G5,G10.aux(),Jp,Jp)
G15AX=sgao(G10A,G5); G15Ah=shetgao(G10A,G5,G10A.aux(),Jp,X10)
G15DX=sgao(G10D,sG5); G15Dh=shetgao(G10D,sG5,G10D.aux(),X10,Jp)
J15=Tx(G15X['I'])
J15TAN=J15
_J15F=_os.environ.get('C7_J15')       # json file with a flat J15' entry (family_codes.json)
if _J15F:
    _d=_json.load(open(_J15F))['J15']
    _au=[a if a=='T' else ((tuple(a[0][0]),tuple(a[0][1])),tuple(a[1])) for a in _d['auts']]
    J15=flat_code([G5]*3,_au,_d['words'])
GAD={'G5':G5,'G10':G10,'G10A':G10A,'G10D':G10D,'G15X':G15X,'G15AX':G15AX,'G15DX':G15DX,'G15h':G15h,'G15Ah':G15Ah,'G15Dh':G15Dh}
for k in list(GAD): GAD['s'+k]=GAD[k].sigma()
MAINS={1:G5,2:G10,3:G15h}
PAT={'P10':(G10,G10.aux(),Jp,Jp),'P10A':(G10A,G10A.aux(),Jp,X10),'P10D':(G10D,G10D.aux(),X10,Jp),
 'P15X':(G15X,G15h.aux(),J15,J15),'P15A8':(G15AX,G15Ah.aux(),J15,J15),'P15Ah':(G15AX,G15Ah.aux(),J15,G15X['X']),
 'P15A5':(G15AX,G15Ah.aux(),J15,G15h['X']),'P15D':(G15DX,G15Dh.aux(),G15h['X'],J15)}

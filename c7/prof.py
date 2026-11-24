"""Profile-level recursion for arbitrary nested patterns and gadgets; top level S3b + K4a."""
import math, json, pickle, os
from decimal import Decimal, getcontext
getcontext().prec=60
def prof(a,t,s,o,h,v):
    assert min(a,t,s,o,h,v)>=0 and t<=a and o+h+v==s, (a,t,s,o,h,v); return (a,t,s,o,h,v)
def psig(p): a,t,s,o,h,v=p; return (a,t,s,o,v,h)
def pgao(L,R):
    a1,t1,s1,o1,h1,v1=L; a2,t2,s2,o2,h2,v2=R
    return prof((a1-t1)*(a2-t2)+t1*s2+s1*t2, t1*o2+o1*t2, s1*s2, o1*o2+(h1+v1)*(h2+v2), h1*o2+o1*v2, v1*o2+o1*h2)
def phet(L,R,J0,JH,JV):
    aL,tL,sL,oL,hL,vL=L; aR,tR,sR,oR,hR,vR=R; j0,o0,h0,v0=J0; jH,qH=JH; jV,qV=JV
    return prof((aL-tL)*(aR-tR)+tL*sR+sL*tR, tL*oR+oL*tR, j0*oR+jH*hR+jV*vR, o0*oR+qH*hR+qV*vR, h0*oR+(jV-qV)*vR, v0*oR+(jH-qH)*hR)
def Phi(p): a,t,s,o,h,v=p; return (a-t,o,v,h,t,t,t)
S3b={'B':['BBB','BHA','NAV','NDH','NVD','ABH','AHN','AHD','DBV','DVN','DVD','HND','HDN','HDD','VNA','VAB','VDA'],'N':['BVD','NNN','NVA','ANH','ADH','AHN','DNV','DDH','DHN','HVD'],'A':['NBA','NAN','ABB','AAV','AHA'],'D':['NBD','NDN','DBB','DAV','DHA'],'O':[],'H':['NNH','NHN','HNN','HVV'],'V':['NNV','NVN','VNN','VVV']}
K4a=['BBBB','BNVB','BAHB','BDVB','BHNB','BHDB','BVAB','NBBV','NNVH','NAVH','NDHH','NHNH','NHAH','NVDV','ABBV','ANHH','AAVH','ADHH','AHAH','AVNH','AVDH','DBBH','DNVV','DAVV','DDHV','DHNV','DHAV','DVDV','HBBA','HNVD','HAHD','HAVN','HDHN','HDVD','HHNN','HHND','HHAN','HHDD','HVAD','HVDN','VBBN','VBBD','VNVN','VNVA','VAHA','VDVA','VHDA','VVNA','VVAA']
LAB='BNADOHV'
def rule(R,vs): return tuple(sum(math.prod(v[LAB.index(c)] for c,v in zip(w,vs)) for w in R[l]) for l in LAB)
def code(K,vs): return sum(math.prod(v[LAB.index(c)] for c,v in zip(w,vs)) for w in K)
def topM(p0,p1,p2): return code(K4a,[rule(S3b,[Phi(p0),Phi(p1),Phi(p2)])]*4)
def rate(M,d): return float((Decimal(M).ln()/d).exp())
def rateD(M,d): return (Decimal(M).ln()/d).exp()
def split_top(s):
    out=[];d=0;cur=''
    for ch in s:
        if ch in '<[(': d+=1
        if ch in '>])': d-=1
        if ch==',' and d==0: out.append(cur); cur=''
        else: cur+=ch
    out.append(cur); return out
BASEPAT=['P10','P10A','P10D','P15X','P15A8','P15Ah','P15A5','P15D']
def norm_pat(nm):
    """S<A,B,P> == N<P,B>"""
    if nm.startswith('S<'):
        a,b,p=split_top(nm[2:-1]); return 'N<%s,%s>'%(norm_pat(p),b)
    if nm.startswith('N<'):
        q,c=split_top(nm[2:-1]); return 'N<%s,%s>'%(norm_pat(q),c)
    return nm
_here=os.path.dirname(os.path.abspath(__file__))
BASEDATA=None   # set by the caller (computed live from the BPZ data)
class World:
    """profiles given codebook choice JQ[pattern]=(j,q) (normalized names)."""
    def __init__(self,JQ):
        self.JQ={norm_pat(k):v for k,v in JQ.items()}; self.pc={}; self.gc={}
    def gp(self,nm):
        if nm in self.gc: return self.gc[nm]
        if nm in BASEDATA['GAD']: r=BASEDATA['GAD'][nm]
        elif nm.startswith('s('): r=psig(self.gp(nm[2:-1]))
        elif nm.startswith('Gao('):
            a,b=split_top(nm[4:-1]); r=pgao(self.gp(a),self.gp(b))
        elif nm.startswith('H['):
            d=0
            for i,ch in enumerate(nm):
                if ch=='[': d+=1
                if ch==']':
                    d-=1
                    if d==0: break
            Lp,J0,JH,JV=self.pp(nm[2:i]); r=phet(Lp,self.gp(nm[i+2:-1]),J0,JH,JV)
        else: raise KeyError(nm)
        self.gc[nm]=r; return r
    def pp(self,nm):
        nm=norm_pat(nm)
        if nm in self.pc: return self.pc[nm]
        if nm in BASEDATA['PAT']: r=BASEDATA['PAT'][nm]
        else:
            q,c=split_top(nm[2:-1]); Q=self.pp(q); C=self.gp(c)
            Lp=pgao(Q[0],C); J0=phet(Q[0],C,Q[1],Q[2],Q[3]); jq=self.JQ[nm]
            r=(Lp,(J0[2],J0[3],J0[4],J0[5]),jq,jq)
        self.pc[nm]=r; return r
def gdim(nm):
    """units (5-dim) of a gadget name"""
    if nm in BASEDATA['GM']: return BASEDATA['GM'][nm]
    if nm.startswith('s('): return gdim(nm[2:-1])
    if nm.startswith('Gao('): a,b=split_top(nm[4:-1]); return gdim(a)+gdim(b)
    d=0
    for i,ch in enumerate(nm):
        if ch=='[': d+=1
        if ch==']':
            d-=1
            if d==0: break
    return pdim(nm[2:i])+gdim(nm[i+2:-1])
def pdim(nm):
    nm=norm_pat(nm)
    if nm in BASEDATA['PM']: return BASEDATA['PM'][nm]
    q,c=split_top(nm[2:-1]); return pdim(q)+gdim(c)

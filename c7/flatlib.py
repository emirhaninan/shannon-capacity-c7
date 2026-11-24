"""flat label codes (k copies of G5) as codebook specs: ('flat', words_tuple, auts_tuple)"""
import json, pickle, os
import sym
SSTAR=(((0,2,4,1,3),(1,-1,1,1,-1)),(0,2,0,0,2))
def from_json(sp):
    au=tuple(a if a=='T' else ((tuple(a[0][0]),tuple(a[0][1])),tuple(a[1])) for a in sp['auts'])
    return ('flat',tuple(sp['words']),au)
def build(spec):
    import symbase
    _,words,au=spec; k=len(words[0])
    return sym.flat_code([symbase.G5]*k,list(au),list(words))

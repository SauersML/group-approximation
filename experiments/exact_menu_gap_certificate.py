#!/usr/bin/env python3
"""Check primal/dual certificates for the finite exact-relator profile game.

Instance JSON:
  {"profiles":[...], "relators":[...], "rejects":{"r":[profiles...]}}
Certificate JSON may contain rational/decimal weights `mu` on relators and/or
`lambda` on profiles.  The checker reports the certified primal lower bound and
dual upper bound; equality certifies the optimum by finite minimax.
"""
import argparse, json, sys
from fractions import Fraction


def q(x):
    if isinstance(x, int): return Fraction(x)
    if isinstance(x, float): return Fraction(str(x))
    if isinstance(x, str): return Fraction(x)
    raise ValueError(f"bad weight {x!r}")


def weights(raw, keys, name):
    if raw is None: return None
    if not isinstance(raw, dict): raise ValueError(f"{name} must be an object")
    extra=set(raw)-set(keys)
    if extra: raise ValueError(f"{name} has unknown keys: {sorted(extra)}")
    w={k:q(raw.get(k,0)) for k in keys}
    if any(v<0 for v in w.values()): raise ValueError(f"{name} has negative weight")
    if sum(w.values(),Fraction()) != 1: raise ValueError(f"{name} weights must sum to 1")
    return w


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('instance'); ap.add_argument('certificate'); a=ap.parse_args()
    try:
        I=json.load(open(a.instance,encoding='utf-8')); C=json.load(open(a.certificate,encoding='utf-8'))
        P=list(dict.fromkeys(I['profiles'])); E=list(dict.fromkeys(I['relators']))
        rej={r:set(I.get('rejects',{}).get(r,[])) for r in E}
        unknown={p for r in E for p in rej[r]}-set(P)
        if unknown: raise ValueError(f"unknown rejected profiles: {sorted(unknown)}")
        mu=weights(C.get('mu'),E,'mu'); lam=weights(C.get('lambda'),P,'lambda')
        out={'status':'ok'}
        if mu is not None:
            vals={p:sum((mu[r] for r in E if p in rej[r]),Fraction()) for p in P}
            lo=min(vals.values(),default=Fraction(0)); out['primal_lower_bound']=str(lo); out['profile_payoffs']={p:str(v) for p,v in vals.items()}
        if lam is not None:
            vals={r:sum((lam[p] for p in P if p in rej[r]),Fraction()) for r in E}
            hi=max(vals.values(),default=Fraction(0)); out['dual_upper_bound']=str(hi); out['relator_payoffs']={r:str(v) for r,v in vals.items()}
        if mu is not None and lam is not None:
            out['optimality_certified']=out['primal_lower_bound']==out['dual_upper_bound']
        print(json.dumps(out,indent=2,sort_keys=True)); return 0
    except (OSError,KeyError,ValueError,json.JSONDecodeError) as e:
        print(f'error: {e}',file=sys.stderr); return 64
if __name__=='__main__': raise SystemExit(main())

#!/usr/bin/env python3
"""Exact finite algebra checks and deterministic numerical tables.

These checks do NOT verify the infinite-volume proofs or either conjecture.
The script uses only the Python standard library.
"""
from __future__ import annotations
import argparse
import json
import math
from fractions import Fraction as F
from pathlib import Path


def mul(a: list[F], b: list[F], cap: int) -> list[F]:
    out = [F(0)] * (cap + 1)
    for i, x in enumerate(a[:cap+1]):
        if not x:
            continue
        for j, y in enumerate(b[:cap+1-i]):
            if y:
                out[i+j] += x*y
    return out


def power(a: list[F], exponent: int, cap: int) -> list[F]:
    out = [F(1)] + [F(0)] * cap
    while exponent:
        if exponent & 1:
            out = mul(out, a, cap)
        exponent >>= 1
        if exponent:
            a = mul(a, a, cap)
    return out


def conditional_size_probability(b: int, ell: int, n: int) -> F:
    if n < ell + 1:
        return F(0)
    m = (b-1)*ell + b + 1
    B = b*n - ell + 1
    s = n - ell - 1
    p = F(1,b)
    return F(m*math.comb(B,s),B) * p**s * (1-p)**(B-s)


def check_branching_coefficients() -> int:
    count = 0
    cap = 24
    for b in (2,3,4):
        p = F(1,b)
        offspring = [F(0)] * (cap+1)
        for _ in range(cap+1):
            Bpoly = [p*x for x in offspring]
            Bpoly[0] += 1-p
            zfree = power(Bpoly,b,cap-1)
            offspring = [F(0)] + zfree
        Bpoly = [p*x for x in offspring]
        Bpoly[0] += 1-p
        for ell in range(13):
            m = (b-1)*ell+b+1
            coeffs = power(Bpoly,m,cap-ell-1)
            for n in range(ell+1,cap+1):
                expected = conditional_size_probability(b,ell,n)
                assert coeffs[n-ell-1] == expected, (b,ell,n)
                count += 1
    return count


def check_radial_endpoint() -> int:
    count=0
    for b in range(2,8):
        r_prev, r = F(2), F(3)-F(1,b)
        assert r_prev == F(2)
        count += 1
        assert r == F(3)-F(1,b)
        count += 1
        for ell in range(3,21):
            r_prev,r = r,2*r-r_prev
            assert r == F(ell+1)-F(ell-1,b)
            count += 1
    return count


def check_thinning() -> int:
    count=0
    for r in range(1,7):
        for den in range(2,52):
            eps=F(1,den)
            alpha=2*r*eps
            q=1/(1+2*alpha)
            chi=(1+q)/(1-q)
            assert alpha*q*chi < 1
            assert 1-q-alpha*q*(1+q) == 2*alpha*alpha/(1+2*alpha)**2
            count+=1
    return count


def check_tree_walk() -> int:
    count=0
    for b in (4,9,16):
        rho=(F(1)+F(2*math.isqrt(b),b+1))/2
        pc=F(1,b)
        weights=[F(1)]
        for n in range(1,41):
            new=[F(0)]*(len(weights)+1)
            for k,w in enumerate(weights):
                new[k]+=w/2
                if k==0:
                    new[1]+=w/2
                else:
                    new[k-1]+=w/F(2*(b+1))
                    new[k+1]+=w*F(b,2*(b+1))
            weights=new
            assert sum(weights)==1
            a=sum(w*pc**k for k,w in enumerate(weights))
            pivot_numer=sum(k*w*pc**k for k,w in enumerate(weights))
            assert weights[0] <= a <= rho**n
            assert 0 <= pivot_numer <= n*a
            count+=1
    return count


def check_interval_law() -> dict[str,int]:
    total=F(3,4)
    tail_checks=0
    for m in range(1,201):
        total += F(1,4*m*m)-F(1,4*(m+1)*(m+1))
        assert total == 1-F(1,4*(m+1)*(m+1))
        tail_checks+=1
    prod=F(1)
    product_checks=0
    for M in range(1,41):
        prod*=1-F(1,4*M*M)
        expected=F(math.factorial(2*M)*math.factorial(2*M+1),
                   2**(4*M)*math.factorial(M)**4)
        assert prod==expected
        product_checks+=1
    return {'radius_probability_telescoping':tail_checks,
            'finite_Wallis_product_identities':product_checks}


def shell_norm_numeric(b: int, N: int) -> tuple[float,float]:
    """Finite radial sum evaluated with log-gamma; no Monte Carlo."""
    p=1.0/b
    out=0.0
    diagonal=0.0
    for ell in range(2*N-1):
        m=(b-1)*ell+b+1
        conditional_terms=[]
        for n in range(max(N,ell+1),2*N):
            B=b*n-ell+1
            s=n-ell-1
            logprob=(math.log(m/B)+math.lgamma(B+1)-math.lgamma(s+1)
                     -math.lgamma(B-s+1)+s*math.log(p)+(B-s)*math.log1p(-p))
            conditional_terms.append(math.exp(logprob)/n)
        value=math.fsum(conditional_terms)
        if ell==0:
            diagonal=value
            out+=value
        else:
            phi=(1+(b-1)*ell/(b+1))*b**(-ell/2)
            out+=(b+1)/b*phi*value
    return out,diagonal


def limiting_constant(b: int) -> float:
    t=b**-0.5
    A=b+1
    B=b-1
    shell=(2/3)*(1-2**-1.5)/math.sqrt(2*math.pi*b*(b-1))
    weighted=A+(A*A*t/(1-t)+2*A*B*t/(1-t)**2+B*B*t*(1+t)/(1-t)**3)/b
    return shell*weighted


def main() -> None:
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    checks={
      'branching_coefficients_against_independent_PGF_recursion':check_branching_coefficients(),
      'radial_spectral_endpoint_recurrence':check_radial_endpoint(),
      'strict_subcritical_thinning_inequalities':check_thinning(),
      'lazy_tree_walk_critical_and_pivotal_inequalities':check_tree_walk(),
      **check_interval_law(),
    }
    table=[]
    for b in (2,3,4):
        for N in (1,2,4,8,16,32,64,128,256):
            norm,diag=shell_norm_numeric(b,N)
            table.append({'b':b,'degree':b+1,'N':N,'operator_norm':norm,
                          'N_power_3_over_2_times_norm':N**1.5*norm,
                          'diagonal':diag})
    thin=[]
    for eps in (.1,.03,.01,.003,.001):
        r=2
        alpha=2*r*eps
        lower=2/(1+alpha+math.sqrt((1+alpha)**2+4*alpha))
        thin.append({'r':r,'epsilon':eps,'quenched_pc_lower_bound':lower})
    result={
      'status':'PASS',
      'scope':'Finite exact algebra and deterministic floating-point evaluation, not verification of infinite theorems.',
      'exact_check_counts':checks,
      'total_exact_checks':sum(checks.values()),
      'tree_projection_numerical_table':table,
      'tree_scaled_norm_limits':{str(b):limiting_constant(b) for b in (2,3,4)},
      'thinning_lower_bounds':thin,
      'universal_fixed_price':'OPEN',
      'universal_benjamini_schramm':'OPEN',
    }
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'exact_checks':checks,
                      'total_exact_checks':result['total_exact_checks'],'output':str(args.output)},indent=2))

if __name__=='__main__':
    main()

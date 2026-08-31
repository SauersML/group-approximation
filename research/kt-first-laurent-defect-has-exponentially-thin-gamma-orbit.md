---
rg: 2
id: kt-first-laurent-defect-has-exponentially-thin-gamma-orbit
kind: claim
title: The first Laurent defect has an exponentially thin Gamma orbit
artifacts:
  - research/kt-congruence-stabilizer-traps-the-pointed-inverse-orbit-proof.md
distinct_from:
  kt-nilpotent-inverse-is-hs-cheap-only-before-canonical-amplification: That compares coefficient-linear and additive-root inverse ranks; this computes the actual Gamma coset orbit of the named return and constructs the corresponding exact Reynolds/Clifford multiplicity countermodel.
  kt-tensor-mask-isometry-and-positive-density-multiplicity-proof: That proves an abstract tensor-mask firewall for arbitrary multiplicity microstates; this identifies the arithmetic multiplicity factor left untouched by the complete Gamma orbit of the named Laurent defect.
  predicate-rank-jump-forces-adjoint-reynolds-gap: That obtains positive adjoint density from extensive forbidden packet mass; this proves that the Gamma orbit of the single KT seed has vanishing site and adjoint density, so the required extensive hypothesis is absent.
---

**ESTABLISHED EXACT REYNOLDS FIREWALL; THE GLOBAL ROOT REMAINS OPEN.**

Use the intermediate-ring quotients

~~~text
T_N=F_2[x_1,y,x_3]/(x_1,y,x_3)^(N+1),
P_N=image(F_2[x_1,x_1y,x_3]),
Q_N=EL_3(T_N),
Gamma_N=EL_3(P_N),
Omega_N=Q_N/Gamma_N,
h_N=e_12(y).
~~~

Let `O_N=Gamma_N h_N Gamma_N/Gamma_N` be the full `Gamma_N` orbit of the
named site. If `N=2m` or `N=2m+1`, put

~~~text
b_(2m)=(m+1)(2m+1),
b_(2m+1)=(m+1)(2m+3),                                    (PAG1)

v_(2m)=m(m+1)(4m+5)/6,
v_(2m+1)=(m+1)(m+2)(4m+3)/6.                             (PAG2)
~~~

Then

~~~text
|O_N| <= 2^(9b_N),
|Omega_N| >= 2^(v_N),
|O_N|/|Omega_N| <= 2^(9b_N-v_N)
                    =2^(-N^3/12+O(N^2)) ->0.             (PAG3)
~~~

The stabilizer behind (PAG3) is explicit. The principal congruence
subgroup

~~~text
C_N={gamma in Gamma_N:gamma=I mod x_1^2 P_N}
~~~

fixes `h_N Gamma_N`. Indeed, conjugating `gamma=I+x_1^2 A` by
`h_N=I+yE_12` produces only the coefficient multipliers

~~~text
x_1^2,   x_1^2y=x_1x_2,   x_1^2y^2=x_2^2,
~~~

all of which lie in `P_N`. The quotient `P_N/x_1^2P_N` has dimension
`b_N`, giving the orbit bound.

This thinness persists for every fixed finite packet of intermediate-ring
words. If `F subset EL_3(F_2[x_1,y,x_3])` is fixed, there is an integer
`M_F` such that the principal congruence subgroup modulo `x_1^(M_F)` fixes
every coset `gGamma_N`, `g in F`, for all `N`. Hence the union of their
`Gamma_N` orbits has size

~~~text
at most |F| 2^(O_F(N^2)).                                 (PAG4)
~~~

More sharply, if packets `F_N` have maximum denominator deficit
`M_N=o(N)` and `log_2|F_N|=o(N^3)`, their complete `Gamma_N`-saturation
still has zero density in `Omega_N`. Thus a packet-density proof must use
Laurent denominator depth linear in the truncation scale, or an
exponentially cubic number of words.

There is an exact canonical multiplicity countermodel. On

~~~text
H_N=ell^2(Q_N) tensor (C^2)^(tensor Omega_N)
~~~

let `Q_N` act by its left regular representation on the first factor and by
permutation of qubit sites on the second; let the Boolean lamp at a site be
the Pauli `Z` on that qubit. This is an exact representation of

~~~text
W_N=(direct_sum_(Omega_N) C_2) rtimes Q_N
~~~

with exactly the regular character. If `o_N=Gamma_N`,

~~~text
p_N=(1+Z_(o_N))/2,
U_(h,N)=rho_N(h_N),
~~~

then `p_N` commutes with all of `Gamma_N` and

~~~text
||[p_N,U_(h,N)]||_2=1/sqrt(2).                            (PAG5)
~~~

Nevertheless every Pauli or Clifford packet generated from the base site,
the named site, and all of their `Gamma_N` conjugates is supported on the
`Gamma_N`-invariant tensor factor indexed by `{o_N} union O_N`. Even
granting the full actor matrix algebra, its normalized adjoint-rank fraction
inside `End(H_N)` is only

~~~text
4^(1+|O_N|-|Omega_N|) ->0.                                (PAG6)
~~~

Thus neither a finite Kazhdan packet nor Reynolds averaging over the entire
finite `Gamma_N` image converts the pointed inverse failure into
positive normalized adjoint density. The complement is an exact
multiplicity reservoir, while the distinguished operator remains an
operator-norm-one, positive-`L^2` wall.

The representations above pull back to the coherent wreath over
`H/Gamma` and converge to its canonical character. Therefore canonical
mixed moments, full Gamma covariance, and a finite Clifford rigidifier do
not repair (PAG6). A successful amplification must use Laurent words whose
denominator depth grows linearly with `N` and connects a positive fraction
of the missing Gamma orbits. That is precisely the still-open moving-window
coherence step.

DERIVATION
kt-congruence-stabilizer-traps-the-pointed-inverse-orbit-proof

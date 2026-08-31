---
rg: 2
id: amenable-lamp-hyperlinear-to-sofic-does-not-spatialize-the-kt-actor
kind: claim
title: Amenable lamp rounding does not spatialize the Kun--Thom actor
artifacts:
  - research/bcjm-lamp-rounding-leaves-the-external-normalizer-cocycle-proof.md
sources:
  - https://arxiv.org/abs/2110.03076
  - https://arxiv.org/abs/2311.09202
distinct_from:
  alekseev-thom-ulam-stability-does-not-close-the-kt-moving-window: That audits uniform algebra maps and amplification; this applies the quantitative amenable-group hyperlinear-to-sofic theorem directly to the lamp subgroup and computes the precise external-equivariance remainder.
  finite-packet-basis-rigidifiers-leave-a-multiplicity-cocycle: That analyzes a selected nonabelian packet; this shows the same cocycle survives even when the entire amenable lamp restriction has been replaced by a sofic-induced approximation.
---

**ESTABLISHED APPLICABILITY FENCE; THE NAMED RETURN REMAINS OPEN.**

Let

~~~text
L=direct_sum_(G/Gamma) C_2
~~~

be the amenable binary lamp subgroup. Burton--Chaudkhari--Juschenko--
Muliarchyk's quantitative theorem says that, on any prescribed finite set,
a sufficiently accurate trace-separating hyperlinear approximation of `L`
is close on the same Hilbert space to a sofic-induced permutation
approximation.

Apply this to the restriction of a hypothetical Kun--Thom wreath
microstate. If `beta_n(l)` is the resulting permutation approximation and
`u_n(g)` is an external actor unitary, then for every fixed covariance row

~~~text
g l g^(-1)=l'
~~~

one obtains

~~~text
||u_n(g) beta_n(l) u_n(g)^*-beta_n(l')||_2
 <=2 max_(a in {l,l'})||alpha_n(a)-beta_n(a)||_2
   +covariance_defect_n(g,l).                            (BLS1)
~~~

This is genuine useful equivariance. It says that the actor approximately
normalizes the rounded lamp representation. It does **not** say that
`u_n(g)` is close to a permutation or that it permutes the underlying
coset sites.

The omission is unavoidable from the amenable restriction alone. For a
finite abelian lamp group `K`, let `lambda_K` be its regular permutation
representation, let an external generator act on `K` by an automorphism
`theta` with permutation implementer `P_theta`, and put

~~~text
beta(k)=lambda_K(k) tensor I_r,
U=P_theta tensor V,              V in U(r).              (BLS2)
~~~

Then (BLS2) has exact lamp multiplication, exact regular traces, and exact
external covariance for every choice of `V`. For a cyclic external actor,
`U` defines an exact representation with no further restriction on the
chosen generator `V`.

The freedom can be macroscopically nonspatial in the permutation basis. If
`V=F_r` is the normalized Fourier matrix, then every monomial matrix
`M` on `l^2(K) tensor C^r` satisfies

~~~text
|tr_norm(U^* M)|<=1/sqrt(r),
dist_2(U,M)^2>=2-2/sqrt(r).                              (BLS3)
~~~

The same lower bound survives arbitrary `o(dim)` padding. Thus even an
**exact** sofic-induced lamp model plus exact covariance does not control
the external unitary normalizer.

For several actor generators the invisible factors form a unitary
multiplicity cocycle. They may be chosen as an exact finite-dimensional
actor representation, so property (T) does not eliminate them. The
Burton--Chaudkhari--Juschenko--Muliarchyk theorem controls only the amenable
restriction and supplies no simultaneous conjugacy which makes this cocycle
permutational.

Three further data are still missing:

1. a common choice of lamp rounding for all actor translates;
2. coherence of those choices as the finite lamp window grows; and
3. control of the block/commutant normalizers so that configuration
   permutations descend to permutations of the coset sites.

These are exactly the GKP converse/moving-window conditions. The theorem
does not force the named
`h=e_12(x_2/x_1)` return to commute with the cyclic parity, and the global
root remains **OPEN**.

DERIVATION
bcjm-lamp-rounding-leaves-the-external-normalizer-cocycle-proof

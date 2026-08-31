# Audit: a nuclear type I counterexample to STW Problem XXII

## Verdict

**Green as an internal proof audit; not a substitute for external refereeing.**

The construction below gives a separable, unital, nuclear, type I C*-algebra
`A` with compact Bauer trace simplex for which

```text
T(A) proper_subset T(overline(A)^{T(A)}).
```

The proof has two standard external inputs: the elementary Chern-class
obstruction to a nowhere-zero section, and Cuntz--Pedersen duality between
bounded traces and the self-adjoint quotient by the trace-zero subspace.  The
commutator mechanism is close in spirit to Pedersen--Petersen and Bice--Farah;
the extra ingredient here is the rank/dimension scaling that makes the
obstructing elements tend to zero in the *uniform tracial 2-norm* while their
finite self-commutator width tends to infinity.

A literature check through 2026-08-31 found the positive results recorded in
the STW problem list, Evington's Z-stable theorem, the Bice--Farah asymptotic
commutator construction, and Toms' quadratic-dimension topological
obstructions, but not this exact counterexample to Problem XXII.  Novelty is
therefore a search result, not a priority claim.

## 1. Homogeneous blocks

For `s>=1`, set

```text
N_s = s^2,
X_s = CP^(N_s),
E_s = 1 + L_s^{+s},
D_s = Gamma(End(E_s)),
```

where `L_s -> X_s` is the tautological complex line bundle.  Every fibre of
`D_s` is `M_(s+1)`.

Let `p_s` be the projection onto the trivial line and `q_s` the projection
onto the first tautological summand.  Put

```text
h_s = p_s-q_s.
```

The two projections are orthogonal and rank one in every fibre, so every
tracial state on `D_s` vanishes on `h_s`, while

```text
||h_s|| = 1,
h_s^2 = p_s+q_s,
||h_s||_(2,T(D_s))^2 = 2/(s+1).                       (A1)
```

Thus the operator norm stays one but the uniform fibre 2-norm tends to zero.

## 2. Chern obstruction to bounded self-commutator width

### Lemma

If `ell<=s`, then for arbitrary `z_1,...,z_ell in D_s`,

```text
||h_s - sum_(j=1)^ell [z_j^*,z_j]|| >= 1.             (A2)
```

### Proof

Relative to `E_s=1+L_s^{+s}`, write

```text
z_j = [ a_j  b_j ]
      [ c_j  d_j ].
```

Each lower-left block `c_j` is a section of `L_s^{+s}`.  Therefore
`c=(c_1,...,c_ell)` is a section of `L_s^{+(s ell)}`.  If `u` generates
`H^2(CP^(s^2);Z)`, then

```text
c_(s ell)(L_s^{+(s ell)}) = (+/-u)^(s ell) != 0
```

because `s ell<=s^2`.  A nowhere-zero section would split off a trivial line
and force the top Chern class to vanish.  Hence there is `x in X_s` with

```text
c_1(x)=...=c_ell(x)=0.                                 (A3)
```

At that point, compress a self-commutator to the trivial rank-one summand:

```text
p_s [z_j^*,z_j](x) p_s
 = c_j(x)^*c_j(x)-b_j(x)b_j(x)^*
 = -b_j(x)b_j(x)^* <= 0.                               (A4)
```

Since `p_s h_s(x) p_s=p_s(x)`, the corresponding compression of
`h_s-sum_j[z_j^*,z_j]` is at least the identity on that one-dimensional
corner.  Compression is contractive, proving (A2).

The quantifiers are load-bearing: for each *fixed* finite `ell`, (A2) holds
for every tail index `s>=ell`.  No modulus uniform in `ell` is asserted.

## 3. The separable nuclear algebra and its trace simplex

Let

```text
B = direct_sum_(s=1)^infinity D_s
```

be the c0-direct sum and let

```text
A = unitization(B).
```

Each `D_s` is separable, nuclear and type I; these properties pass through a
countable c0-sum and unitization.  Hence `A` is separable, unital, nuclear and
type I.

Its center is the unitization of `direct_sum_s C(X_s)`, namely `C(K)` for

```text
K = (disjoint_union_s X_s) union {infinity},           (A5)
```

the one-point compactification.  Every tracial state on a homogeneous block
is integration of normalized fibre trace against a probability measure, and
the scalar quotient gives the point at infinity.  Consequently

```text
T(A) = Prob(K),
partial_e T(A) = K.                                    (A6)
```

Thus `T(A)` is Bauer and `K` is compact metrizable.  It has infinite covering
dimension because every `CP^(s^2)` is clopen in `K`.

## 4. Exact uniform tracial completion

For `x in D_s`, write

```text
||x||_(2,s)=sup_(y in X_s) tr_(s+1)(x(y)^*x(y))^(1/2).
```

Define

```text
J = {(x_s) in product_s D_s :
       sup_s ||x_s|| < infinity and ||x_s||_(2,s) -> 0}. (A7)
```

Then

```text
M := overline(A)^{T(A)} = C1 + J.                      (A8)
```

For the forward inclusion, truncate a tail: if `x=lambda1+(x_s)` with
`(x_s) in J`, then

```text
x^(n)=lambda1+(x_1,...,x_n,0,0,...)
```

lies in `A` and

```text
||x-x^(n)||_(2,T(A)) = sup_(s>n)||x_s||_(2,s) -> 0.   (A9)
```

Conversely, a uniformly operator-norm bounded uniform-2 Cauchy sequence from
`A` has a scalar limit at infinity.  At each fixed coordinate `s`, finite
matrix rank gives

```text
||a|| <= sqrt(s+1) ||a||_(2,s),
```

so that coordinate converges in operator norm to an element of `D_s`.
Uniform boundedness passes to the coordinatewise limit.  Approximation by one
member of `A`, whose non-scalar part is norm-null and hence 2-null in the
tail, shows that the limiting non-scalar coordinates satisfy (A7).  This
proves (A8).

The set `J` is a norm-closed two-sided ideal in `product_s D_s`, using

```text
||xy||_(2,s) <= ||x|| ||y||_(2,s)
```

and its right-handed analogue.

## 5. The tail corona has a trace-visible class

Regard `B=direct_sum_s D_s` as an ideal of `J` and put

```text
H = M/B.                                               (A10)
```

By (A1), `h=(h_s)` belongs to `J`; since `||h_s||=1` for every `s`, `h` does
not belong to `B`.  Let `hbar=h+B`, a nonzero self-adjoint element of `H`.

For any bounded sequence `(w_s)`, quotienting by the c0-sum gives

```text
||(w_s)+B|| = limsup_s ||w_s||.                        (A11)
```

Take arbitrary `y_1,...,y_ell in H` and lift them to
`lambda_j 1+z_j in M`, where `z_j in J`.  Scalar parts cancel in
self-commutators.  Combining (A11) with the fact that (A2) holds for every
`s>=ell` gives

```text
||hbar - sum_(j=1)^ell [y_j^*,y_j]||
 = limsup_s ||h_s-sum_(j=1)^ell[z_(j,s)^*,z_(j,s)]||
 >= 1.                                                 (A12)
```

Thus `hbar` stays distance at least one from every finite sum of
self-commutators.

## 6. Cuntz--Pedersen separation

For a C*-algebra `C`, let `C_0` be the self-adjoint trace-zero subspace.  The
Cuntz--Pedersen theorem identifies `C_0` with the norm closure of finite sums
of self-commutators, equivalently the dual of `C_sa/C_0` is the space of
bounded self-adjoint tracial functionals.

By (A12),

```text
hbar notin H_0.                                        (A13)
```

Hence there is a bounded self-adjoint tracial functional `phi` on `H` with
`phi(hbar)!=0`.  The Jordan decomposition of a bounded self-adjoint trace has
positive tracial parts.  At least one part detects `hbar`; normalizing it
produces

```text
sigma in T(H),       sigma(hbar) != 0.                 (A14)
```

There is no circular assumption that `H` already had a trace: (A13) and the
Cuntz--Pedersen duality produce the nonzero tracial functional.

## 7. Pullback and explicit discontinuity

Let `pi:M->H` be the quotient and set

```text
sigma_tilde = sigma o pi in T(M).
```

Since `sigma_tilde` kills `B`, its restriction to
`A=C1+B` is exactly the extreme trace `tau_infinity` coming from the scalar
quotient.  But

```text
sigma_tilde(h)=sigma(hbar)!=0,                         (A15)
```

whereas the uniform-2-continuous extension of `tau_infinity` vanishes on
`J`.

The discontinuity can be seen without invoking uniqueness.  Let

```text
h^(n)=(0,...,0,h_n,h_(n+1),...).
```

Then `h-h^(n) in B`, so every `h^(n)` has image `hbar` in `H`, and

```text
sigma_tilde(h^(n)) = sigma(hbar) != 0                  (A16)
```

for every `n`.  On the other hand

```text
||h^(n)||_(2,T(A))
 = sup_(s>=n) sqrt(2/(s+1))
 = sqrt(2/(n+1)) -> 0.                                 (A17)
```

Therefore `sigma_tilde` is not uniform-2-norm continuous and

```text
T(A) proper_subset T(M).                               (A18)
```

This is exactly a negative answer to STW Problem XXII.  Since the uniform
tracial completion with its designated compact trace face is factorial in
the tracially-complete sense (and here the extreme designated fibres are the
matrix factors `M_(s+1)` and the scalar fibre at infinity), the example also
refutes the equivalent factorial-tracially-complete formulation.

## 8. Compatibility with the positive theory

There is no conflict with the finite-dimensional theorem in this repository:
`K` has unbounded covering dimension.  The construction is designed so that
topological complexity available to the Chern class defeats every fixed
finite commutator width while the normalized rank fraction tends to zero.

There is no conflict with Evington's Z-stable theorem: `A` is type I with
finite-dimensional irreducible fibres and is not Z-stable.  There is no
conflict with the one-dimensional Farah--Vaccaro theorem or the existing
finite-dimensional factorial-bundle results for the same dimension reason.

The earlier Cairn node
`stw22-fixed-replication-blocks-infinite-dimensional-selection` was therefore
pointing at a genuine obstruction, but did not itself prove the trace problem
false: failure of one Michael-selection route is not a trace.  The present
argument moves the topology into the Cuntz--Pedersen quotient, where failure
of finite self-commutator approximation is dual to an actual additional
trace.

## 9. Prior-art firewall

The closest checked prior mechanism is Bice--Farah, *Traces, Ultrapowers and
the Pedersen-Petersen C*-Algebras*, Houston J. Math. 41 (2015), 1175--1190,
arXiv:1307.0111.  Their Theorem 2.1 gives projective-space homogeneous blocks
with trace-zero elements at distance one from a prescribed finite number of
self-commutators, and their Corollary 2.2 converts unbounded commutator width
into additional traces on an ultrapower/asymptotic quotient.

The point that must not be blurred is the metric required by Problem XXII.
The present blocks simultaneously satisfy

```text
operator norm = 1,
uniform tracial 2-norm = sqrt(2/(s+1)) -> 0,
finite commutator width defeated >= s.
```

That simultaneous scaling is what turns the Pedersen--Petersen phenomenon
into failure of uniform-2 continuity.

## 10. Hostile checks performed

1. **Compact trace space:** (A6) gives a concrete Bauer simplex.
2. **Supremum over all traces:** for positive `a^*a`, the supremum over
   `Prob(K)` is attained on point masses, so the uniform 2-norm is exactly the
   fibre supremum used above.
3. **Completion:** both inclusions in (A8) are proved; the reverse direction
   uses fixed-coordinate finite-rank norm/2-norm equivalence.
4. **Chern degree:** `rank(L_s^{+(s ell)})=s ell` and `s ell<=s^2`, so its top
   Chern class survives in the cohomology ring of `CP^(s^2)`.
5. **Compression sign:** with `c_j(x)=0`, the trivial-line corner of
   `[z_j^*,z_j]` is `-b_jb_j^*`, giving the correct sign in (A2).
6. **Growing approximant length:** (A12) handles each finite `ell` by choosing
   the tail `s>=ell`; closure cannot evade the obstruction by using more
   commutators at later approximation stages.
7. **Positive trace:** Cuntz--Pedersen yields a bounded self-adjoint trace and
   Jordan decomposition yields a positive tracial component before
   normalization.
8. **Discontinuity:** (A16)--(A17) is an explicit 2-null sequence on which the
   rogue trace is constant nonzero.
9. **Nuclearity/type I:** inherited from homogeneous blocks through countable
   c0-sum and unitization.
10. **Scope:** the counterexample refutes the unrestricted problem while
    leaving every positive finite-dimensional theorem intact.

## References checked

- J. Cuntz and G. K. Pedersen, *Equivalence and traces on C*-algebras*, J.
  Funct. Anal. 33 (1979), 135--164.
- T. Bice and I. Farah, *Traces, Ultrapowers and the Pedersen-Petersen
  C*-Algebras*, Houston J. Math. 41 (2015), 1175--1190; arXiv:1307.0111.
- S. Evington, *Traces on the uniform tracial completion of Z-stable
  C*-algebras*, J. Lond. Math. Soc. (2025), DOI 10.1112/jlms.70207.
- C. Schafhauser, A. Tikuisis, S. White, *Nuclear C*-algebras: 99 problems*,
  arXiv:2506.10902v2, Problem XXII.
- A. S. Toms, *Schubert Calculus and uniform property Gamma*,
  arXiv:2606.12188 (2026).

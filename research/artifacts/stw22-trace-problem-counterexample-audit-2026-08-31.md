# Audit: a nuclear type I counterexample to STW Problem XXII

## Verdict

**Green as an internal proof audit; not a substitute for external refereeing.**

The construction below gives a separable, unital, nuclear, type I C*-algebra
`A` with compact Bauer trace simplex for which

```text
T(A) proper_subset T(overline(A)^{T(A)}).
```

The proof has one standard topological input: the elementary Chern-class
obstruction to a nowhere-zero section.  Applied simultaneously to the two
off-diagonal blocks of a finite packet, it gives late-coordinate vector
states that are multiplicative on every prescribed pair.  Weak-star
compactness then produces a character of the product corona.  The
rank/dimension scaling makes its detecting element tend to zero in the
*uniform tracial 2-norm*.

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

## 2. Simultaneous Chern zeros give finite multiplicativity packets

### Lemma

If `2 ell<=s`, then for arbitrary `z_1,...,z_ell in D_s` there is
`x in X_s` such that the trivial line reduces every `z_j(x)`.  Consequently
its fibre vector state satisfies

```text
omega_(s,x)(h_s)=1,
omega_(s,x)(z_j z_k)
  =omega_(s,x)(z_j) omega_(s,x)(z_k)       for all j,k. (A2)
```

### Proof

Relative to `E_s=1+L_s^{+s}`, write

```text
z_j = [ a_j  b_j ]
      [ c_j  d_j ].
```

The lower-left blocks of `z_j` and `z_j^*` are respectively `c_j` and
`b_j^*`, each a section of `L_s^{+s}`.  Their simultaneous join is a section
of `L_s^{+(2s ell)}`.  If `u` generates `H^2(CP^(s^2);Z)`, then

```text
c_(2s ell)(L_s^{+(2s ell)}) = (+/-u)^(2s ell) != 0
```

because `2s ell<=s^2`.  A nowhere-zero section would split off a trivial line
and force the top Chern class to vanish.  Hence there is `x in X_s` with

```text
b_1(x)=c_1(x)=...=b_ell(x)=c_ell(x)=0.                 (A3)
```

At this point each `z_j(x)` is block diagonal relative to the trivial line,
so that line is reducing.  Its vector state is therefore multiplicative on
every pair from the packet, and it takes value one on `h_s`.  This proves
(A2).

The quantifiers are load-bearing: for each *fixed* finite packet, (A2) holds
for every tail index `s>=2 ell`.  No bound uniform in packet size is asserted.

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

## 5. State compactness produces a corona character

Regard `B=direct_sum_s D_s` as an ideal of the bounded product

```text
P = product_s D_s.                                    (A10)
```

By (A1), `h=(h_s)` belongs to `J`.  Given a finite packet
`z_1,...,z_ell in P` and a lower bound `S`, choose
`s>=max(S,2 ell)` and apply (A2) to their `s`-coordinates.  Pulling the fibre
vector state back through coordinate evaluation gives a state `omega` on
`P` such that

```text
omega(h)=1,
omega(z_j z_k)=omega(z_j)omega(z_k)       for all j,k. (A11)
```

By taking `s` farther out, the same state is arbitrarily small on any
prescribed finite family from `B`.

For finite sets of pairs `(x,y)`, elements `a in B`, and integers `r>=1`,
impose on the state space of `P` the conditions

```text
rho(h)=1,
rho(xy)=rho(x)rho(y),
|rho(a)|<=1/r.                                         (A12)
```

Each is weak-star closed.  Include every left and right factor in the Chern
packet and choose one sufficiently late coordinate; (A11) proves the finite
intersection property.  Compactness of the state space gives a state `rho`
satisfying all pair constraints and all annihilation constraints.  Therefore
`rho` is multiplicative on `P`, `rho|_B=0`, and `rho(h)=1`.  It descends to a
character of `P/B`.  Restriction to `M=C1+J` gives a character, hence a
tracial state, `sigma_tilde` satisfying

```text
sigma_tilde(h)=1,
sigma_tilde(lambda 1+b)=lambda             (b in B).   (A13)
```

Thus `sigma_tilde|_A` is exactly the extreme trace `tau_infinity` from the
scalar quotient, whereas the uniform-2-continuous extension of
`tau_infinity` vanishes on `J`.

## 6. Explicit discontinuity

The discontinuity can be seen without invoking uniqueness.  Let

```text
h^(n)=(0,...,0,h_n,h_(n+1),...).
```

Then `h-h^(n) in B`, and `sigma_tilde|_B=0`, so

```text
sigma_tilde(h^(n)) = 1                                 (A14)
```

for every `n`.  On the other hand

```text
||h^(n)||_(2,T(A))
 = sup_(s>=n) sqrt(2/(s+1))
 = sqrt(2/(n+1)) -> 0.                                 (A15)
```

Therefore `sigma_tilde` is not uniform-2-norm continuous and

```text
T(A) proper_subset T(M).                               (A16)
```

This is exactly a negative answer to STW Problem XXII.  Since the uniform
tracial completion with its designated compact trace face is factorial in
the tracially-complete sense (and here the extreme designated fibres are the
matrix factors `M_(s+1)` and the scalar fibre at infinity), the example also
refutes the equivalent factorial-tracially-complete formulation.

## 7. Compatibility with the positive theory

There is no conflict with the finite-dimensional theorem in this repository:
`K` has unbounded covering dimension.  The construction is designed so that
topological complexity available to the Chern class produces simultaneous
zeros for every fixed finite multiplicativity packet while the normalized
rank fraction tends to zero.

There is no conflict with Evington's Z-stable theorem: `A` is type I with
finite-dimensional irreducible fibres and is not Z-stable.  There is no
conflict with the one-dimensional Farah--Vaccaro theorem or the existing
finite-dimensional factorial-bundle results for the same dimension reason.

The earlier Cairn node
`stw22-fixed-replication-blocks-infinite-dimensional-selection` was therefore
pointing at a genuine obstruction, but did not itself prove the trace problem
false: failure of one Michael-selection route is not a trace.  The present
argument uses the topology to construct finite restrictions of a character;
state-space compactness then assembles them into an actual character of the
product corona.

## 8. Prior-art firewall

The closest checked topological mechanism is Bice--Farah, *Traces,
Ultrapowers and the Pedersen-Petersen C*-Algebras*, Houston J. Math. 41
(2015), 1175--1190, arXiv:1307.0111.  They use projective-space homogeneous
blocks to create additional traces in an asymptotic setting.  That result
does not supply the character constructed here, and it does not by itself
address the uniform-tracial-2 completion in Problem XXII.

The point that must not be blurred is the metric required by Problem XXII.
The present blocks simultaneously satisfy

```text
operator norm = 1,
uniform tracial 2-norm = sqrt(2/(s+1)) -> 0,
simultaneous multiplicativity packets of size <= s/2.
```

That simultaneous scaling is what lets compactness produce a character which
fails uniform-2 continuity.

## 9. Hostile checks performed

1. **Compact trace space:** (A6) gives a concrete Bauer simplex.
2. **Supremum over all traces:** for positive `a^*a`, the supremum over
   `Prob(K)` is attained on point masses, so the uniform 2-norm is exactly the
   fibre supremum used above.
3. **Completion:** both inclusions in (A8) are proved; the reverse direction
   uses fixed-coordinate finite-rank norm/2-norm equivalence.
4. **Chern degree:** `rank(L_s^{+(2s ell)})=2s ell` and `2s ell<=s^2`, so its
   top Chern class survives in the cohomology ring of `CP^(s^2)`.
5. **Reducing, not merely invariant:** simultaneous vanishing of both
   `c_j(x)` and `b_j(x)` makes the trivial line reducing for every packet
   element, hence gives multiplicativity on every prescribed pair.
6. **Finite intersection property:** every finite family of product
   constraints is realized after putting all its left and right factors into
   one Chern packet; every finite family from `B` is small at the same late
   coordinate.
7. **Character:** the constraints range over all pairs in `P`, so their
   compactness limit is multiplicative on all of `P`; the constraints for all
   `r` annihilate `B` exactly.
8. **Discontinuity:** (A14)--(A15) is an explicit 2-null sequence on which the
   rogue character is constantly one.
9. **Nuclearity/type I:** inherited from homogeneous blocks through countable
   c0-sum and unitization.
10. **Scope:** the counterexample refutes the unrestricted problem while
    leaving every positive finite-dimensional theorem intact.

## References checked

- T. Bice and I. Farah, *Traces, Ultrapowers and the Pedersen-Petersen
  C*-Algebras*, Houston J. Math. 41 (2015), 1175--1190; arXiv:1307.0111.
- S. Evington, *Traces on the uniform tracial completion of Z-stable
  C*-algebras*, J. Lond. Math. Soc. (2025), DOI 10.1112/jlms.70207.
- C. Schafhauser, A. Tikuisis, S. White, *Nuclear C*-algebras: 99 problems*,
  arXiv:2506.10902v2, Problem XXII.
- A. S. Toms, *Schubert Calculus and uniform property Gamma*,
  arXiv:2606.12188 (2026).

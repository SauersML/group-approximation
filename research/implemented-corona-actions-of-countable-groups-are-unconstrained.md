---
rg: 2
id: implemented-corona-actions-of-countable-groups-are-unconstrained
kind: claim
title: Every measure-preserving Cantor action of a countable group is implemented on a commutative subalgebra of a matrix corona
distinct_from:
  crossed-product-by-corona-inner-automorphism-is-mf: that assumes an automorphism is implemented in a corona embedding and concludes MF for the crossed product by Z or F_m; this constructs the implementation for an arbitrary countable group action and draws a no-go for rigidity arguments, with no MF conclusion about any crossed product.
  conjugation-image-of-a-torsion-free-mf-group-is-arbitrary: that realizes any group as the conjugation image of an MF group on an abelian normal subgroup; this realizes any measure-preserving Cantor action as an implemented corona action modulo the relative commutant, which is the analytic analogue.
  abelianized-cover-injective-corona-model-carries-nonzero-twist: that proves an injective model of the cover of a full-radical base acts nontrivially on its commutative subalgebra; this shows such actions exist for every group, so the action alone never obstructs.
---

**ESTABLISHED.**

## Statement

Let:
- `G` be a countable group;
- `X` be a Cantor set;
- `alpha` be an action of `G` on `X` by homeomorphisms;
- `mu` be an `alpha`-invariant Borel probability measure of full support.

Then there are integers `k_n`, an injective unital *-homomorphism
`pi : C(X) -> Q = prod M_(k_n) / (+) M_(k_n)`, and unitaries `u_g in U(Q)`
with

```text
u_g pi(f) u_g^* = pi(f o alpha_g^-1)        (f in C(X), g in G).        (IA1)
```

Consequently the relators satisfy `u_g u_h u_(gh)^* in U(pi(C(X))' cap Q)`,
and `g -> [u_g]` is a homomorphism

```text
G -> N_(U(Q))(pi(C(X))) / U(pi(C(X))' cap Q)
```

which induces `alpha`.

**No-go.**  Consider the following principle:

> (P) If `Rad_MF(G) = G`, then every action of `G` on a commutative
> C*-subalgebra of a matrix corona, implemented by normalizing unitaries up to
> the relative commutant, is trivial.

(P) is false for every nontrivial countable `G`.  Take the Bernoulli shift on
`X = ({0,1}^N)^G`, which is a Cantor set, with the product of uniform
measures.  That measure has full support and is invariant, and the action is
nontrivial.

So no proof of `full-mf-radical-abelianized-cover-is-not-mf`, or of
`free-abelianized-cover-reflects-mf`, can pass through the implemented action
alone.  Every such proof must use that the cocycle lies in `U(C*(rho(M)))`
and is the image of the relation module.  An actual corona model of the
abelianized cover carries that information and this construction does not.  The step where every
member of the class dies is the passage from the action to `rho([E,M]) = 1`.

More precisely, the conclusion of (P) fails for every nontrivial countable
`G`.  Full-MF-radical groups are among these, for example
`fp-simple-full-mf-radical-group`, so (P) itself is false.

## Proof

**Partitions.**
- Enumerate `G = {g_1, g_2, ...}`.
- Choose clopen partitions `P_1 <= P_2 <= ...` of `X`, each refining the last,
  that generate the topology.
- Every clopen set is a finite union of pieces of some `P_m`.  Since the
  `alpha_g` are homeomorphisms, for every `m` there is `n(m) >= m` such that
  each `alpha_(g_i)(A)` with `i <= m` and `A in P_m` is a union of pieces of
  `P_(n(m))`.
- Put `m(n) = max{m <= n : n(m') <= n for all m' <= m}`, taking
  `m(n) = 0` if the set is empty.  Then `m(n)` is non-decreasing and
  unbounded, and each `alpha_(g_i) A` with `i <= m(n)` and `A in P_(m(n))`
  is a union of pieces of `P_n`.

**Integer ranks at level `n`.**  Consider real unknowns `r_C`, one for each
`C in P_n`, subject to:
- `sum_C r_C = 1`;
- `sum_(C <= alpha_(g_i) A) r_C = sum_(C <= A) r_C` for all `i <= m(n)` and
  `A in P_(m(n))`.

These are finitely many linear equations with integer coefficients.
- The vector `r_C = mu(C)` solves them, by invariance.
- It is strictly positive, because `mu` has full support.
- The solution space `V` is defined over `Q`, so rational points are dense in
  `V`.  Hence there is a rational strictly positive solution.
- Clearing denominators gives positive integers `r_C`, all at least `1`, that
  satisfy the homogeneous equations.  Put `k_n = sum_C r_C`.

**The embedding.**
- Split `C^(k_n)` into coordinate blocks `H_C` of dimension `r_C`, and let
  `p_C` be the diagonal projection onto `H_C`.
- For `f in LC(X)` constant on the pieces of `P_n`, set
  `pi_n(f) = sum_C f(C) p_C`.  This is a unital *-homomorphism with
  `||pi_n(f)|| = sup |f|`, because every `r_C >= 1`.
- A fixed locally constant `f` is constant on the pieces of `P_n` for all
  large `n`, so `pi(f) = [(pi_n(f))_n]` is well defined in `Q`.  It is a
  *-homomorphism on `LC(X)`, and it is isometric.
- `LC(X)` is dense in `C(X)`, so `pi` extends to an injective unital
  *-homomorphism of `C(X)`.

**The implementing unitaries.**
- For `i <= m(n)`, the blocks `H_A = (+)_(C <= A) H_C` with `A in P_(m(n))`
  decompose `C^(k_n)`.  So do the blocks `H_(alpha_(g_i) A)`.
- The rank equations give `dim H_A = dim H_(alpha_(g_i) A)`.  So there is a
  permutation unitary `u_n^(i)` carrying `H_A` onto `H_(alpha_(g_i) A)` for
  every `A`, that is,
  `u_n^(i) pi_n(1_A) u_n^(i)* = pi_n(1_(alpha_(g_i) A))`.
- For `i > m(n)`, put `u_n^(i) = 1`, and let `u_(g_i) = [(u_n^(i))_n]`.
- Fix `i` and a clopen `D`.  For all large `n`, `D` is a union of pieces of
  `P_(m(n))`, so `u_n^(i) pi_n(1_D) u_n^(i)* = pi_n(1_(alpha_(g_i) D))`
  exactly.
- Since `1_(alpha_g D) = 1_D o alpha_g^-1`, this gives `(IA1)` on indicator
  functions, hence on `LC(X)`, hence on `C(X)` by continuity.

**The homomorphism.**  By `(IA1)`, `u_g u_h u_(gh)^*` fixes `pi(C(X))`
pointwise, so it lies in the relative commutant.  Normalizers modulo the
commutant then compose correctly.

## What the construction does not give

The holonomy `u_g u_h u_(gh)^*` is a permutation-type unitary.  It commutes
with `pi(C(X))`, but nothing forces it to lie in `pi(C(X))`.

A corona model of the abelianized cover over `G = F/R` needs more.  The
relator words evaluated on the `u` must lie in the commutative algebra they
generate together with all their conjugates, and they must be
equivariant images of the relation module.

- Achieving exactly that with a nontrivial action and the base relators
  would give a candidate MF model, and hence evidence against
  `full-mf-radical-abelianized-cover-is-not-mf`.
- Forbidding it is the remaining content of that hole, per
  `abelianized-cover-injective-corona-model-carries-nonzero-twist`.

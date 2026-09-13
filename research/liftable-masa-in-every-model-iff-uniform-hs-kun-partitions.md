---
rg: 2
id: liftable-masa-in-every-model-iff-uniform-hs-kun-partitions
kind: claim
title: A Kazhdan group has a liftable masa in the relative commutant of every matrix-ultraproduct model iff it has dimension-uniform bounded HS Kun partitions
distinct_from:
  hs-block-gap-iff-liftable-masa-of-actor-commutant: that is the equivalence for one fixed partition sequence of one model; this quantifies over all models and all dimensions, turns the existence of a liftable masa into a Pi^0_3 matrix inequality, and shows any positive gap constant forces the Kazhdan constant.
  hs-one-level-expander-block-decomposition: that asks for a per-block scalar gap on every block, which spiky vectors violate; this is the bounded summed form, which that claim implies, and which is exactly equivalent to liftable masas in every model.
  actor-commutant-has-liftable-masa-in-every-model: that is the open existence statement at the Kun--Thom pair for models with vertex rounding; this is the established equivalence for every model of any Kazhdan group, with no rounding hypothesis.
artifacts:
  - research/artifacts/hs-masa-lift-positive-2026-09-13.md
---

**ESTABLISHED.** Let `G` be a countable group with a finite symmetric generating set `S` and
Kazhdan constant `kappa`. For a partition `P = {q_A}` of unity by projections of `M_n` and a map
`u : B_R -> U(n)` put

```text
b(P)          = max_(s in S) sum_A ||[u_s, q_A]||_2^2,
gamma(P, k')  = sup_x ( k'^2 sum_A ||x_A - tau_A(x_A) q_A||_2^2 - sum_s sum_A ||[q_A u_s q_A, x_A]||_2^2 )_+ ,
```

with the sup over self-adjoint block-diagonal contractions `x`. Let `DEC_(k')` say: for every
`beta > 0` there are `eps > 0` and `R` such that every `(eps, R)`-model `u` in every `U(n)` admits a
partition with `b(P) <= beta` and `gamma(P, k') <= beta`. Then the following are equivalent:

1. for every sequence `n_k`, every free ultrafilter `U` and every homomorphism
   `sigma : G -> U(prod_U M_(n_k))`, the algebra `sigma(G)' cap prod_U M_(n_k)` has a maximal abelian
   subalgebra of the form `prod_U C_k`, where each `C_k` is spanned by a finite partition of unity;
2. `DEC_kappa`;
3. `DEC_(k')` for some `k' > 0`.

For one model, the existence of such a masa is equivalent to:
- partitions `P_k` along `U` with `b -> 0` and `gamma(., kappa) -> 0`; and
- an internal block algebra `D = prod_U (direct_sum_A q_A M_(n_k) q_A)` containing `sigma(G)` with
  `sigma(G)' cap D = Z(D)`.

The per-block one-level decomposition `hs-one-level-expander-block-decomposition` for `G` implies
item 1. If `G` has solvable word problem, `DEC_kappa` is a `Pi^0_3` sentence (Tarski--Seidenberg
for the inner statement), so item 1 is absolute: it does not depend on the ultrafilter or on set
theory.

**Trace scope.** Item 1 ranges over every homomorphism, with any trace. The input
`hs-block-gap-iff-liftable-masa-of-actor-commutant` is stated for trace-preserving asymptotic
representations. Its derivation, `hs-block-gap-liftable-masa-proof`, uses only three facts:
- random-sign identities;
- property (T) for the genuine representation `Ad sigma` on `L^2(M)`;
- bimodularity of `E_Q`.

None uses the trace of `sigma`, so items 1-4 there hold for every homomorphism.

**Reading.** In the Hilbert--Schmidt row the localization face (L) is exactly a dimension-uniform
partition inequality. It is the bounded, block-summed HS form of Kun's decomposition. Property (T)
fixes the gap constant for free. What is open is only whether partitions with vanishing boundary
exist. Coordinate capture (Alekseev--Thom OP 6.2 for the model) implies it.

**Model tests.** Genuine representations (irreducible summands) and the trivial model (rank-one
blocks) satisfy `DEC` with `b = gamma = 0`. No Kazhdan model violating it is known.

Derivation: `liftable-masa-iff-uniform-hs-kun-partitions-proof`.

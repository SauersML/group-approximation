---
rg: 2
id: low-degree-view-collapse-survives-non-affine-sigma
kind: claim
title: Unique verifiers over a linear outer game whose views have degree below (1-gamma) log_p(1/eps) collapse to the branch-blind partition coarsening even when the constraint permutations sigma are not affine
distinct_from:
  low-degree-view-unique-verifiers-collapse: that bounds the exact weight by 1 - eps p^D with D the degree of the view differences after applying sigma, which is small only for affine sigma; this asks for the collapse when only the views have small degree and sigma is an arbitrary bijection, where soft non-exact triples of large degree can carry Omega(1) weight.
  linear-view-unique-verifiers-collapse-to-quotient-coarsening: that treats affine views with the threshold c > 1/p; this allows bounded-degree views and arbitrary bijections sigma.
refuted_by:
  - puncture-triples-defeat-partition-coarsening
---

**OPEN.** Use the model and notation of `low-degree-view-unique-verifiers-collapse`.
Fix `gamma > 0`. Let `V` be a unique verifier over a linear outer game `Phi` with
oblivious completeness `1 - eps`, whose views `rho_w` all have reduced degree at most
`d <= (1 - gamma) log_p(1/eps)`, and whose triples carry **arbitrary** bijections
`sigma` of `F_p^k`. Then, for every input `Phi`,
```text
val(V(Phi)) >= (1 - o(1)) * val(Can_part(Phi, V)) - o(1),
```
with `o(1) -> 0` as `eps -> 0` at fixed `p` and `gamma`.

**Why it is the gap.** The rigidity step of `low-degree-view-unique-verifiers-collapse`
uses the degree `D` of `sigma o rho_w - rho_(w')`. That degree is at most `d` for
affine `sigma` but only at most `k(p-1)d` in general. With Grassmann views on
`F_2^k` and `sigma` a transposition of two points, a non-exact triple rejects
honest labels on exactly a `2^(1-k)` fraction of `H_e` and has degree `k - 1`. At
`k >= log_2(1/eps) + 2` such triples can carry `Omega(1)` weight without entering
`w_ex` (referee counterexample, 2026-09-17). The class-killing consequence for
Hadamard, Grassmann, quadratic and Reed--Muller views therefore needs this claim,
or a replacement coarsening that also absorbs such soft triples.

## Attempts

- **Rigidity through the degree of `Q_t` (2026-09-17).** The density lemma gives
  rejection at least `p^(-deg t)`, but `deg t` is only bounded by `k(p-1)d` for
  arbitrary `sigma`, and the transposition example above attains degree `k - 1`
  with rejection `2^(1-k)`. So the `w_ex >= 1 - eps p^D` route dies here. A proof
  must either treat soft triples directly (show that a table of honest labels
  that satisfies most soft triples still induces a good labeling of `Can_part`),
  or enlarge `Can_part` with the soft triples' near-bijections.
- **Refuted by puncture triples; corrected with pointwise completeness (swarm-0917-w4-pull-ugc-1, 2026-09-17).**
  Two vertices over `F_(p^l)`, `r` multiplier edges `x_b = lambda_i x_a`, identity
  views (degree 1), cross triples of weight `1 - alpha`, and same-owner triples
  `(w_z, w_z, (0 1))` of weight `alpha/2` each, with `alpha = (r-1)/(2r-1)`. The
  oblivious `eps` is `2 alpha p^(-l) -> 0`, but `val(V) = r/(2r-1)` while
  `val(Can_part) = 1`, and the twin with `sigma = id` has value `1`. So no
  functional of `(Phi, views, supports, weights, beta)` works under oblivious
  completeness (`puncture-triples-defeat-partition-coarsening`). The obstruction
  is the puncture cost `kappa`: punctures sit on the labels that the coarsening
  forces. For affine views, `affine-view-verifiers-collapse-up-to-puncture-cost`
  proves `val(V) >= (1 - p eps/(p-1)) val(Can_comp) - r eps` under pointwise
  completeness. Still open: `r eps >~ 1` (many punctured views per edge), and views of
  degree `>= 2`, where the `1/p` rigidity step has no proof (almost-injective views
  of degree `>= 3` may give incompatible triples that are soft).

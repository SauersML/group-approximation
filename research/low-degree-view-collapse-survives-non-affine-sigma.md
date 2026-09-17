---
rg: 2
id: low-degree-view-collapse-survives-non-affine-sigma
kind: claim
refuted_by:
  - non-affine-sigma-deletions-defeat-low-degree-collapse
title: Unique verifiers over a linear outer game whose views have degree below (1-gamma) log_p(1/eps) collapse to the branch-blind partition coarsening even when the constraint permutations sigma are not affine
distinct_from:
  low-degree-view-unique-verifiers-collapse: that bounds the exact weight by 1 - eps p^D with D the degree of the view differences after applying sigma, which is small only for affine sigma; this asks for the collapse when only the views have small degree and sigma is an arbitrary bijection, where soft non-exact triples of large degree can carry Omega(1) weight.
  linear-view-unique-verifiers-collapse-to-quotient-coarsening: that treats affine views with the threshold c > 1/p; this allows bounded-degree views and arbitrary bijections sigma.
---

**REFUTED (2026-09-17).** `non-affine-sigma-deletions-defeat-low-degree-collapse`
takes identity views (degree 1) over outer edges `H_e = { (x, M_e x) }` with random
invertible `M_e`, and mixes the exact triple `M_e` with `M_e o swap(0, u_e)`. The
completeness is `1 - 2^(-k)` and `Can_part` is the outer game itself, with value 1.
A first-moment bound over all labellings gives value at most `1/2 + s` once
`2^k >= 64 e^3/s^3` and there are `3n/s` edges. The replacement is the deletion
coarsening `Can_del` (the rounded coarsening with the sparse label sets where
`sigma` disagrees with the induced bijection removed), with
`val(V) >= w_r val(Can_del)`. The deletions can matter only when the outer game's
homogeneous symmetries have large index in the view quotients. UGC remains open.

The original statement and earlier attempts are retained below as history.

**Statement as proposed.** Use the model and notation of `low-degree-view-unique-verifiers-collapse`.
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
- **Refuted by a sparse swap (2026-09-17).** Enlarging `Can_part` with the soft
  triples' near-bijections does not help. In the counterexample every soft
  triple rounds to `M_e`, the rounded coarsening has value 1 through the zero
  labelling, and each swap removes exactly the label `0`. That removal alone
  drives the value of the perturbed verifier to `o(1)`. See
  `non-affine-sigma-deletions-defeat-low-degree-collapse`, item 3, for when the
  removals are harmless: when the symmetries of the outer game surject onto the view
  quotients.

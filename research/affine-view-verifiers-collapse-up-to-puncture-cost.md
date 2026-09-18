---
rg: 2
id: affine-view-verifiers-collapse-up-to-puncture-cost
kind: claim
title: Unique verifiers with affine views and arbitrary bijections sigma collapse to the compatible-bijection coarsening up to the puncture cost kappa, and pointwise completeness bounds kappa by r eps
distinct_from:
  linear-view-unique-verifiers-collapse-to-quotient-coarsening: that needs affine sigma, where compatible and exact triples coincide; this allows arbitrary bijections sigma, keeps compatible non-exact triples in the coarsening and pays the puncture cost.
  low-degree-view-unique-verifiers-collapse: that bounds the exact weight through the degree of sigma o rho_w - rho_w', which is large for non-affine sigma; this uses the degree-one image relation only and needs no degree bound on sigma.
  puncture-triples-defeat-partition-coarsening: that is the counterexample showing kappa can be a constant under oblivious completeness; this is the positive transfer theorem with the pointwise hypothesis that removes it.
  low-degree-view-collapse-survives-non-affine-sigma: that refuted statement asks for a collapse to Can_part under oblivious completeness; this collapses to Can_comp and needs pointwise completeness together with r eps -> 0.
artifacts:
  - experiments/puncture-triples-2026-09-17/check_puncture_triples.py
---

**ESTABLISHED.** Use the model of `low-degree-view-unique-verifiers-collapse`
(outer linear game `(Z, E, mu)` with affine `H_e`, output vertices `w` with owners
`o(w)`, distributions `tau_e` on triples `t = (w, w', sigma)`). Assume every view
`rho_w : A_(o(w)) -> F_p^k` is **affine**, and let every `sigma` be an arbitrary
bijection of `F_p^k`. Put `I_w = Im rho_w`.

**Definitions.** For `t = (w, w', sigma)` on `e`, let
`U_t = { (rho_w(h), rho_(w')(h)) : h in H_e }`, an affine subspace of
`F_p^k x F_p^k` with projections `I_w` and `I_(w')`. Call `t` **compatible** if
`U_t` is the graph of a bijection `beta_t : I_w -> I_(w')` (then `beta_t` is
affine). Its **puncture set** is `S_t = { u in I_w : sigma(u) != beta_t(u) }`.
Exact triples are compatible with `S_t` empty. Let `w_comp` be the weight
`sum_e mu_e tau_e(compatible)`.
`Can_comp(Phi, V)` is the unique game on vertices `(z, ker)`, one per
kernel of a view owned by `z`, with labels the cosets `A_z / ker` and an edge of
weight `mu_e tau_e(t) / w_comp` for every compatible `t`, carrying the bijection
of cosets induced by `beta_t` (through `A_z/ker rho_w = I_w`). It depends only on
`(Phi, views, supports, weights, beta)`, not on `sigma`. Let the **puncture cost**
be
```text
kappa = sum_e mu_e max_(u_w in I_w) sum_(compatible t on e) tau_e(t) [u_(w_t) in S_t],
```
where `w_t` is the first view of `t`.

**Statement.**

1. **Rigidity.** If `t` accepts honest labels on more than a `1/p` fraction of
   `H_e`, then `t` is compatible. So, with oblivious completeness `1 - eps`,
   `1 - w_comp <= p eps / (p - 1)`.
2. **Transfer.** For every input `Phi`,
   `val(V(Phi)) >= w_comp val(Can_comp(Phi, V)) - kappa`.
3. **Pointwise bound.** If every `h in H_e` is rejected with probability at most
   `eps` over `t ~ tau_e` (pointwise completeness `1 - eps`), then
   `kappa <= r eps`, where `r` is the largest number, over edges, of distinct first
   views of compatible non-exact triples on that edge. Hence
   ```text
   val(V(Phi)) >= (1 - p eps/(p-1)) val(Can_comp(Phi, V)) - r eps.
   ```
4. **Sharpness of the hypothesis.** Under oblivious completeness alone, `kappa`
   can be a constant with `eps -> 0` and `r = 2`, and no functional of
   `(Phi, views, supports, weights, beta)` bounds `val(V)` from below
   (`puncture-triples-defeat-partition-coarsening`).

**Consequence.** For affine views (Hadamard, Grassmann and all linear encodings)
with arbitrary `sigma`, every pointwise-complete verifier with `r eps -> 0` factors
its soundness through the test-free, `sigma`-free coarsening `Can_comp`. The
invariant is `kappa`. A proof that beats `Can_comp` must spread punctures over
`r >~ 1/eps` distinct views per edge, or give up pointwise completeness. The
first door (many views, each punctured on an `eps` set) stays open.

This neither proves nor refutes UGC.

DERIVATION affine-view-puncture-cost-collapse-proof

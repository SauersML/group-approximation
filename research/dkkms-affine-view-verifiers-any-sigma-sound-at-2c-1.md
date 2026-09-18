---
rg: 2
id: dkkms-affine-view-verifiers-any-sigma-sound-at-2c-1
kind: claim
title: A coarsening labelling distribution with uniform marginals absorbs every puncture, and folding-class functionals supply one on DKKMS instances, so affine-view unique verifiers over them have value at least 2c-1 for arbitrary bijections sigma
distinct_from:
  affine-view-verifiers-collapse-up-to-puncture-cost: that pays the worst-case puncture cost kappa of one fixed Can_comp labelling and needs pointwise completeness and r eps -> 0; this averages over a Can_comp labelling distribution with uniform marginals, pays only the oblivious rejection of compatible triples, and needs no pointwise hypothesis and no bound on the number r of punctured views.
  grassmann-composed-2to2-coarsenings-are-satisfiable: that shows Can has value 1 on DKKMS instances through one gauge labelling F* and kills affine-view verifiers with affine sigma; this adds the homogeneous gauges G_psi indexed by folding-class functionals, which make the satisfying labellings F* + G_psi uniform at every coarsening vertex, and extends the kill to arbitrary bijections sigma.
  puncture-triples-defeat-partition-coarsening: that counterexample has a rigid coarsening (the only optimal labelling is zero) and shows that kappa can be a constant; this names marginal uniformity as the invariant that the counterexample lacks and proves that the collapse holds whenever it is present.
  linear-view-unique-verifiers-collapse-to-quotient-coarsening: that needs affine sigma, where compatible and exact triples coincide; this treats arbitrary bijections sigma.
artifacts:
  - experiments/uniform-gauge-2026-09-17/check_uniform_gauge_transfer.py
  - experiments/uniform-gauge-2026-09-17/check_dkkms_homogeneous_gauge.py
---

**ESTABLISHED.** Route: `uniform-gauge-transfer-proof`.

Use the model of `affine-view-verifiers-collapse-up-to-puncture-cost`. The
outer game `Phi` is linear over `F_p`, with affine `H_e` projecting onto both
sides. The views `rho_w : A_(o(w)) -> F_p^k` are affine. The triples
`t = (w, w', sigma)` carry **arbitrary** bijections `sigma` of `F_p^k`. The
image relation `U_t`, compatibility, `beta_t`, the puncture set `S_t`, the weight
`w_comp` and the coarsening `Can_comp(Phi, V)` are as defined there. Completeness
is **oblivious**: `eps = E_e E_(t ~ tau_e) Pr_(h in H_e)[t rejects honest labels]`.
Put
```text
E_comp = sum_e mu_e sum_(compatible t on e) tau_e(t) |S_t| / |I_(w_t)|,
```
the part of `eps` carried by compatible triples.

1. **Uniform-marginal transfer.** Let `D` be a probability distribution on
   labellings `X` of `Can_comp(Phi, V)` whose marginal at every vertex `(z, K)` is
   uniform on `A_z / K`. Let `nu_D = E_(X ~ D) val_X(Can_comp)`. Then
   ```text
   val(V(Phi)) >= w_comp nu_D - E_comp >= nu_D - p eps / (p - 1).
   ```
   The bound holds with no pointwise hypothesis and no dependence on the number
   of punctured views per edge.
2. **Homogeneous gauges on DKKMS instances.** Let `Phi` be a DKKMS agreement
   game (notation of `grassmann-composed-2to2-coarsenings-are-satisfiable`) and
   `V` any affine-view unique verifier over it. For a nonzero subspace `N`
   carried by a coarsening vertex, let `Q(N)` be the dimension-`dim N` folding
   class of `(U, N)` for any legitimate `U` with `(U, N) in A_(dim N)`. If there
   is no such `U`, let `Q(N)` be a private class `{N}` with `R_Q(N) = N`. Let
   `pi_N : N -> R_(Q(N))` send `x` to its `R_Q`-component in `R_Q + H_U`. This
   map is a bijection and does not depend on `U`. For any choice of functionals
   `psi_Q in Fun(R_Q)`, one per class, put
   ```text
   G_psi(z, M)(r) = psi_(Q(M))( pi_M(r) ),      r in M.
   ```
   Then `F* + G_psi` satisfies every compatible triple of `Can_comp(Phi, V)`. With
   `psi` uniform, its marginal at every vertex `(z, Ann(M))` is uniform on `Fun(M)`.
3. **Class kill.** Hence, on **every** 3LIN input, satisfiable or not, every
   affine-view unique verifier over a DKKMS agreement game with oblivious
   completeness `c = 1 - eps` and **arbitrary** bijections `sigma` satisfies
   ```text
   val(V(Phi)) >= 1 - 2 eps = 2c - 1.
   ```
   A reduction to `Gap-UG(c, s)` through such a verifier needs `s >= 2c - 1`.
4. **The hypothesis is needed.** In the `F_8` instance of the puncture family
   (`r = 3`, `alpha = 2/5`), the only optimal `Can_comp` labelling is zero, so the
   marginals are not uniform. There `val(V) = 3/5 < 1 - 2 eps = 4/5`.

**The invariant.** Punctures cost a verifier only where the coarsening forces
labels. Item 1 turns the worst-case puncture cost `kappa` into an average, and
the average equals the oblivious rejection whenever the satisfying labellings
can be translated freely at every vertex. For affine constraints this is a
linear-algebra condition: the homogeneous solution space of `Can_comp` must
project onto the linear part of every `A_z / K`. Call its failure **gauge
rigidity**. The puncture counterexample is gauge-rigid: distinct multipliers
force label `0`. The DKKMS coarsening is not gauge-rigid, because the folding
offsets are coboundaries on folding classes (the old gauge `F*`) and every class
carries a free functional `psi_Q` (the new homogeneous gauge).

**Consequence for `unique-games-conjecture`.** Two doors were left open by
`affine-view-verifiers-collapse-up-to-puncture-cost` for affine views with
non-affine `sigma`: many punctured views per edge (`r eps >~ 1`), and verifiers
without pointwise completeness. For the DKKMS family, the only known hard 2-to-2
family, both doors are now closed. No bijection `sigma`, however irregular,
and no spreading of punctures over many views lets an affine-view unique
verifier on these instances pass `c = 1/2 + o(1)` with vanishing soundness. What
survives for affine views is an outer family whose coarsening is gauge-rigid, or
has value `< 1`, on NO instances. What survives in general are views that are not
affine (door P2 of `low-degree-view-unique-verifiers-collapse`).

This neither proves nor refutes UGC.

DERIVATION uniform-gauge-transfer-proof

## Attempts

- **Replay (swarm-0917-w5-pull-ugc-1, 2026-09-17).**
  - `check_uniform_gauge_transfer.py` brute-forces Item 1 on random small linear
    outer games over `F_2` and `F_3`: two to four edges, affine `H_e`, up to five
    affine views, and triples whose bijections are punctured extensions of
    `beta_t` or random. It computes `val(V)`, `eps`, `w_comp`, `E_comp` and all
    `Can_comp` labellings. It checks Item 1 for the uniform distribution on all
    labellings, and, whenever the marginals are uniform, for the uniform
    distribution on optimal labellings. Seeds `20260917` and `7` with 400
    instances each give 0 failures. The `F_8` puncture control shows non-uniform
    marginals and a failing bound, as in Item 4.
  - `check_dkkms_homogeneous_gauge.py` reuses the DKKMS builder of
    `grassmann-composed-2to2-coarsenings-are-satisfiable`. It checks that `pi_Q`
    does not depend on `U` and is bijective, that `G_psi` satisfies the
    homogeneous constraint of every exact triple, that `F* + G_psi` satisfies
    every exact triple, and that marginals are uniform. The default run (1800
    exact triples, 8 random `psi`) gives 0 failures, and so does
    `--seed 7 --l 3 --bvertices 60 --pairs 4` (960 triples). The control, which
    draws `psi` per vertex instead of per class, violates 835 and 412 triples.

---
rg: 2
id: two-site-center-measurement-interference-is-relator-paid
kind: claim
title: Actor relator energy pays the center-measurement interference on the marked A5 carrier
refuted_by:
  - bernoulli-center-measurement-retains-boundary-interference
distinct_from:
  two-site-a5-center-classicalization: that asks for the final permutation charts; this is the single block-mass composition estimate which, together with stochastic inverse rigidity, constructs them.
  priority-decoder-lipschitz-under-selector-gate-alignment: that controls decoded observables after selector allocations have already aligned; this concerns interference between consecutive actor transports through a finite lamp-center PVM.
  invariant-cartan-completion: that asks for one globally invariant diagonal algebra; this only asks for total-variation multiplicativity of finite center block-mass couplings on each prescribed actor window.
---

**REFUTED.**  The exact canonical Bernoulli model already violates the
inverse instance of `(TMI3)`: on one moved site the forward and backward
block-mass couplings are both independent, so their composition stays
independent and remains total-variation distance `35/72` from the identity
coupling.  See `bernoulli-center-measurement-retains-boundary-interference`.
The proposed estimate cannot be matrix-only either, because every entry of
the finite coupling is a fixed mixed group-word moment and therefore has the
same canonical limit in any hypothetical microstate sequence.

The statement below is retained as the failed target and as the exact record
of where fixed-window sequential measurement loses the actor boundary.

For a canonical microstate of

```text
W_5=A5^(G/Gamma) semidirect G,
```

fix a finite symmetric actor multiplication window `F`.  Let `Y` be a
finite set of lamp sites containing `(p,q)` and every translate needed to
evaluate the pair-preserving incidences and products in `F`.  Exactify the
commuting rational five-dimensional `A5` center projections on `Y`, and
write

```text
P=(P_omega)_(omega in {0,1}^Y)                         (TMI1)
```

for their joint PVM.  Its canonical atom weights are the fixed Bernoulli
weights with parameter `5/12`, up to `o(1)`.

For an actor lift `U_g`, form the classical block-mass coupling

```text
C_g(eta,omega)=tr(P_eta U_g P_omega U_g^*).            (TMI2)
```

Prove, after choosing `Y` (or a bounded enlargement depending only on `F`),
that presentation defect tending to zero forces

```text
||C_(gh)-C_g o_mu C_h||_TV ->0                         (TMI3)
```

for every tested product, together with the identity and inverse versions,
while retaining the `35/72-o(1)` exclusive-or mass on `(p,q)` and the exact
pair-preserving label covariance.

The difference in `(TMI3)` is exactly the interference created by inserting
the PVM `sum P_omega=1` between `U_g` and `U_h`.  Actor multiplicativity
controls `U_(gh)-U_gU_h` but does not by itself control this insertion.
The claim says that the lamp covariance and canonical mixed cylinder moments
pay the off-diagonal interference relevant to the marked carrier.

This is the remaining finite-matrix inequality.  If it holds,
`finite-pvm-couplings-with-approximate-inverses-classicalize` turns the
couplings into approximately multiplicative finite permutations, and the
two-site center labels give the forbidden marked-pair chart.  A countermodel
must therefore exhibit canonical lamp moments and vanishing group relators
while retaining order-one sequential-measurement interference on the
exclusive-or carrier.

## Attempts

- **Use actor multiplication alone.**  False: block-mass matrices forget
  phases, and the cross terms between distinct intermediate atoms can add
  coherently in `U_gU_h`.
- **Measure the full finite lamp packet.**  This makes each individual
  covariance deterministic only on coordinates whose translates remain in
  `Y`; no finite `Y` is invariant under the transitive actor.  The boundary
  interference is the same completion problem in a larger alphabet.
- **Drop to the two-site four-atom PVM.**  Pair-preserving incidences are then
  exact, but general actor generators leave the packet and their block-mass
  products retain uncontrolled interference.  Joint multiplication, not
  the number of center atoms, is load-bearing.
- **Live quantitative target.**  Expand the left side of `(TMI3)` as a sum
  of four-point mixed traces
  `tr(P_eta U_g P_theta U_h P_omega U_h^* P_theta' U_g^*)` and use the
  canonical wreath trace to identify the diagonal `theta=theta'` terms.
  What remains is to bound the off-diagonal sum from the finite actor/lamp
  relators without first assuming a common invariant diagonal algebra.

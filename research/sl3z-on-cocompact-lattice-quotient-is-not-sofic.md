---
rg: 2
id: sl3z-on-cocompact-lattice-quotient-is-not-sofic
kind: claim
title: For some cocompact lattice Λ of SL3(R), the action of SL3(Z) on SL3(R)/Λ is not sofic
distinct_from:
  sl3z-lattice-space-action-is-not-sofic: that is the self-coupling action on SL3(R)/SL3(Z), refuted because its Hecke orbits are finite and equidistribute; this takes a lattice outside the conjugate-commensurability class of SL3(Z), where no orbit is finite
  sl3z-admits-nonsofic-action: that asks for any nonsofic action of SL3(Z); this names an explicit free mixing candidate that survives the Hecke mechanism
---

**OPEN (two-sided).** There is a cocompact lattice `Λ <= SL_3(R)` such that the left action
`SL_3(Z) ↷ SL_3(R)/Λ`, with the invariant probability measure, is not sofic (Păunescu Definition 1.4).

**Facts.**
* *Essentially free.* `γ·gΛ = gΛ` iff `g^(−1)γg ∈ Λ`. For `γ != 1` only `λ != 1` can occur, and
  `{g : γg = gλ}` is empty or a coset of the proper closed centralizer of `λ`, a Haar-null set.
  Countably many `λ` give a null set.
* *Mixing.* `SL_3(R)` acts transitively, hence ergodically. Howe--Moore
  (`howe-moore-property-for-simple-lie-and-p-adic-groups`) makes the coefficients on `L²_0` `C_0`, and
  `SL_3(Z)` is discrete.
* *Dual form.* By the coupling `SL_3(R)` and `sofic-free-actions-are-soe-invariant`, it has the same
  status as `Λ ↷ SL_3(R)/SL_3(Z)`: a cocompact lattice acting on the space of unimodular lattices.
* *No finite orbits.* A finite orbit of `gΛ` would make `SL_3(Z) ∩ gΛg^(−1)` a lattice of finite index
  in both `SL_3(Z)` and `gΛg^(−1)`. But commensurable lattices are both uniform or both not (part 2
  artifact of `sl3z-lattice-space-action-is-sofic`, Section 8).
* *Sharp line.* Every pair of lattices inside the commensurability class of the conjugates of `SL_3(Z)`
  gives a sofic quotient action (`sl3-split-class-lattice-quotient-actions-are-sofic`). So a nonsofic
  action of this shape needs a lattice outside that class, and cocompact lattices are the simplest ones.

A proof would answer `sl3z-admits-nonsofic-action` and `mixing-free-nonsofic-action-of-sofic-group` with
one explicit action. A disproof would be a soficity theorem for a higher-rank mixing lattice action
with no periodic orbits at all.

Standard examples of `Λ` are the norm-one groups `SL_1(O_D)` of maximal orders in cubic division
algebras over `Q`. The existence of cocompact lattices in `SL_3(R)` is not imported here.

## Attempts

* **Hecke orbits via `finite-equidistributed-orbits-give-sofic-action`.** Dead. There are no finite
  orbits, and an extension has finite orbits only above finite orbits, so no extension can be treated
  this way either.
* **Snapping the Hecke orbits of `SL_3(Z)`.** In the dual form `Λ ↷ X_3`, the Hecke orbits `V_k`
  equidistribute. So for each `λ` there is a bijection of `V_k` moving most points to within `ε_k → 0`
  of `λx` (Strassen's theorem plus Birkhoff--von Neumann). But the bijections for `λ`, `λ'` and `λλ'`
  agree only metrically, not combinatorially, and equidistribution forces point spacing of order `ε_k`.
  So asymptotic multiplicativity in Hamming distance does not follow. Dies at: no separation scale.
* **The S-arithmetic cover.** `Λ ↷ (SL_3(R) × SL_3(Q_p))/SL_3(Z[1/p])` is a compact
  `SL_3(Z_p)`-extension of `Λ ↷ X_3`, so its soficity would suffice, but it has no finite orbits
  either. The action of `SL_3(R) × SL_3(Q_p)` on `SL_3(R)/Λ × Y` is stably orbit equivalent to
  `SL_3(Z[1/p]) ↷ SL_3(R)/Λ`, whose restriction to `SL_3(Z)` is the target. That makes the problem
  harder, not easier.
* **Kun--Thom mechanisms.** Blind for mixing actions:
  `kazhdan-fixed-algebra-blind-to-subgroup-ergodic-actions` and
  `permutation-centralizer-blind-to-weakly-mixing-actions`.
* **Diagonal enlargement.** The action is sofic iff `SL_3(Z) ↷ X_3 × SL_3(R)/Λ` is. Forward: product
  lemma in `induced-actions-sofic-iff-homogeneous-action-sofic-proof`, with
  `sl3z-lattice-space-action-is-sofic`. Backward: passage to a factor. No finite orbits appear, so
  nothing is gained.
* **Superrigidity of finite couplings (live; the negative angle).** `Λ` is cocompact, so the coupling
  cocycle `c : SL_3(Z) × SL_3(R)/Λ → Λ` built from a compact fundamental domain takes finitely many
  values for each `γ`. Consider a finite model that carries `c` exactly: a transitive finite set
  `SL_3(Z)/Γ_0` with an honest cocycle into `Λ`. That is the same as a homomorphism `ρ : Γ_0 → Λ`,
  `ρ(δ) = c(δ, Γ_0)`. By Margulis superrigidity, after passing to finite index, `ρ` has finite image
  or extends to an automorphism of `SL_3(R)`. In the second case `ρ(Γ_0)` would be a non-uniform
  lattice inside the uniform lattice `Λ`, which is impossible. So honest finite couplings see only
  finite quotients of `Λ`.
  *Calibration:* for `Λ = SL_3(Z)` the extending homomorphisms are the Hecke conjugations
  `x ↦ axa^(−1)` on `SL_3(Z) ∩ a^(−1)SL_3(Z)a`. These are exactly the models of
  `sl3z-lattice-space-action-is-sofic`, so the dichotomy separates the refuted candidate from this one
  along the right line.
  *Dies at:* a sofic approximation gives the cocycle identity only on most points. Upgrading
  almost-cocycles of a Kazhdan group to honest ones is a stability statement, and permutation
  stability fails for infinite sofic Kazhdan groups (Becker--Lubotzky; recalled, not verified). So a
  proof needs a relative, coupling-specific stability, or a route that uses superrigidity
  approximately. Margulis superrigidity is not imported here.

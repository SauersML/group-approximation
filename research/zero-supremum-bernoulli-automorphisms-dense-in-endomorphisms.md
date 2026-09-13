---
rg: 2
id: zero-supremum-bernoulli-automorphisms-dense-in-endomorphisms
kind: claim
title: At zero Rokhlin supremum, the automorphisms of a finite-base Bernoulli shift are dense among its endomorphisms
distinct_from:
  iid-density-iff-collapse-and-endomorphism-density: that proves over every group that density of generating i.i.d. partitions is collapse plus this property; this asks for the property at zero supremum.
  iid-generators-dense-at-zero-rokhlin-supremum: that asks for generating i.i.d. partitions of one shift with the distribution of another, which contains an isomorphism between the two; this concerns one shift and its factor maps onto itself.
---

**OPEN.** Let `G` be countably infinite with `h^Rok_sup(G) = 0`, and let `(L, λ)` be a finite base with
`H(λ) > 0`. Then `Aut_G(X_λ)` is dense in `End_G(X_λ)` for the metric `d(φ, ψ) = λ^G{y : φ(y)(1_G) ≠ ψ(y)(1_G)}`.

Equivalent forms, by `iid-density-iff-collapse-and-endomorphism-density`:
- the generating partitions are dense in `Ind_λ(X_λ)`;
- for every endomorphism `φ` and `ε > 0` there is an automorphism `T` with `d(φ ∘ T, id) < ε`.

The property is an isomorphism invariant of the action (item 2 there), so it does not depend on the base
chosen within an entropy class.

**Payoff.** With the finite-base total collapse at `s = 0` (`bernoulli-shifts-above-rokhlin-supremum-are-isomorphic`)
it gives `iid-generators-dense-at-zero-rokhlin-supremum`, by route `iid-density-from-collapse-and-endomorphism-density`.
Conversely that claim contains this one, the case `κ = λ`.

**Model tests.**
- On every nonamenable group with positive supremum the property fails for every finite base (item 5 of
  `iid-density-iff-collapse-and-endomorphism-density`). So the hypothesis `s = 0` cannot be weakened to
  nonamenability.
- Over `Z`, where the supremum is `∞`, the property is expected from Ornstein theory; this was not verified from a
  source here. If so, the property characterizes `s = 0` only among nonamenable groups.
- No group with `s = 0` is known.
- On every group containing `F_2`, at every supremum, the property fails for bases of entropy `>= log 4`
  (`ornstein-weiss-map-has-no-approximate-right-inverses`). So this claim implies that no group with zero supremum
  contains a free subgroup of rank two.
- **Status (2026-09-13).** On every nonamenable group, at every supremum, the property fails for bases of entropy
  `> log 4` (`spectral-gap-refutes-exactification-on-nonamenable-groups`). Groups with zero supremum are nonamenable,
  so this claim holds iff no countable group has zero supremum, i.e. iff
  `every-group-has-positive-rokhlin-entropy-action`. Only single bases of entropy at most `log 4` stay open.

## Attempts

- **Entropy obstructions.** Empty at `s = 0`. The sub-additivity bound behind item 5 needs a Bernoulli factor whose
  base entropy lies strictly between `0` and `s`.
- **Seward's perturbative factor theorem.** Not applicable, as recorded on
  `iid-generators-dense-at-zero-rokhlin-supremum`: it needs Rokhlin entropy room, and that room is `0` at `s = 0`.
- **Krieger density in the same alphabet.** Holds, and is not the obstruction. Let `h^Rok_G(X) = 0`, let `ξ` be any
  `L`-labelled partition with `|L| >= 2`, and let `r > 0`.
  - `seward-small-support-relative-generators` (trivial `F`, `p̄ = (1/2, 1/2)`) gives a pre-partition
    `β = {B_0, B_1}` with `µ(B_0 ∪ B_1) = r` and `σ-alg^red_G(β) = B(X)`.
  - Relabel `ξ` by `ℓ_0` on `B_0` and by `ℓ_1 ≠ ℓ_0` on `B_1`. The new partition extends `β`, so it generates by
    Lemma 2.2 there, and it differs from `ξ` on a set of measure at most `r`.

  So for every endomorphism `φ` the partition `ξ^φ` is within `r` of a generating `L`-labelled partition, whose law
  is within d-bar distance `r` of `λ^G`. No new labels are needed. What fails is exact independence.
- **Where it dies.** Given a non-invertible endomorphism `φ`, no construction is known of an automorphism `T` that
  makes `φ ∘ T` close to the identity. Equivalently, no construction is known of an endomorphism close to the
  identity that carries the same extension as `φ`.

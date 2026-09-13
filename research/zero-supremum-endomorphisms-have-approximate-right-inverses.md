---
rg: 2
id: zero-supremum-endomorphisms-have-approximate-right-inverses
kind: claim
title: At zero Rokhlin supremum, every endomorphism of a finite-base Bernoulli shift has approximate right inverses among its endomorphisms
distinct_from:
  bernoulli-isomorphism-from-approximate-right-inverses: that proves over every group that this property for two shifts gives their isomorphism; this asks for the property at zero supremum.
  zero-supremum-bernoulli-automorphisms-dense-in-endomorphisms: that asks for automorphisms close to every endomorphism, which implies this; this asks only for endomorphisms ζ with φ ∘ ζ close to the identity.
---

**OPEN.** Let `G` be countably infinite with `h^Rok_sup(G) = 0`, let `(L, λ)` be a finite base with `H(λ) > 0`, and
put `X = X_λ`. For every `φ ∈ End_G(X)` and `ε > 0` there is `ζ ∈ End_G(X)` with `d(φ ∘ ζ, id) < ε`, where
`d(φ, ψ) = λ^G{y : φ(y)(1_G) ≠ ψ(y)(1_G)}`.

Equivalently (item 1 of `bernoulli-isomorphism-from-approximate-right-inverses`): in the space of self-joinings of
`X`, the weak* closure of the endomorphism graphs is invariant under transposition.

**Payoff.**
- For two finite bases of different entropy it gives an isomorphism, which is
  `zero-rokhlin-supremum-forces-bernoulli-collapse` (route `zero-supremum-collapse-via-approximate-right-inverses`).
  By `positive-rokhlin-via-classification-and-collapse` the base-entropy classification root would then be
  equivalent to Seward's positive-entropy question.
- For every finite base it gives total finite collapse at supremum zero (item 6 of the node above).
- It is implied by `zero-supremum-bernoulli-automorphisms-dense-in-endomorphisms` (item 4 there). So it is weaker
  than the exactification claim `iid-generators-dense-at-zero-rokhlin-supremum`, and it still gives the collapse
  without an isomorphism as input.

**Model tests.**
- It fails on every nonamenable group with positive supremum, for every finite base (item 5 there).
- It holds over `Z` by the residual factor theorem of Burton–Keane–Serafin (model test there). `Z` has supremum `∞`,
  so the property characterizes supremum zero only among nonamenable groups.
- The content is only in non-invertible `φ`. For an automorphism, `ζ = φ^-1` is exact.
- No group with `s = 0` is known.
- On every group containing `F_2`, at every supremum, the property fails for bases of entropy `>= log 4`, and no two
  shifts of different entropy both have it (`ornstein-weiss-map-has-no-approximate-right-inverses`). So this claim
  implies that no group with zero supremum contains a free subgroup of rank two.
- **Status (2026-09-13).** On every nonamenable group, at every supremum, the property fails for bases of entropy
  `> log 4`, and no two shifts of different entropy both have it
  (`spectral-gap-refutes-exactification-on-nonamenable-groups`). Groups with zero supremum are nonamenable, so this
  claim holds iff no countable group has zero supremum, i.e. iff `every-group-has-positive-rokhlin-entropy-action`.
  Route `zero-supremum-collapse-via-approximate-right-inverses` therefore gives nothing toward a collapse.

## Attempts

- **What a right inverse must do.** `ζ` is an approximate equivariant section of the extension `X → X` given by `φ`,
  and the section must itself push `λ^G` exactly to `λ^G`. Take the case where `φ` is the projection of a splitting
  `X ≅ X × C` onto the first factor, when such a splitting exists. Then `ζ(x) = (a(x), c(x))` needs `a` within `ε` of
  the identity and `c` an exactly independent copy of `C`, both measurable in `x`. So even this case asks for an
  exactly independent complement in an approximately prescribed position. That is the non-generating half of the
  splittings in `bernoulli-infinite-power-iff-approximate-half-absorption`.
- **Entropy obstructions.** Empty at `s = 0`. The obstruction of item 5 needs a Bernoulli factor whose base entropy
  lies strictly between `0` and `s`.
- **Partition-metric exactification.** It would suffice, but it asks for more: an automorphism in place of `ζ`.
- **Seward's small-support generators.** They give, for every `φ`, generating partitions of `X` within any `r` of
  `ξ^φ` with the same labels. These are approximate inverses of `φ` in a non-exact sense: their laws are only within
  d-bar `r` of `λ^G`. The endomorphism `ζ` must have law exactly `λ^G`.
- **Free subgroups.** Refuted where `F_2 <= G`. A right inverse of the Ornstein–Weiss endomorphism must invent one bit
  for each coset of `F_2`, constant along its tree. It yields an odd, almost invariant unit vector for `F_2` on `L²_0`
  of a Bernoulli shift, which Kesten's bound excludes. By contrast, fibres that run along one partial injection can
  be cut into finite segments with small boundary, and there approximate inverses by automorphisms exist; this
  contrast is a sketch, not landed as a node.
- **Free subrelations.** The free subgroup can be replaced by Bowen's measurable free subrelation
  (`bernoulli-shifts-are-von-neumann-day`). The odd sector then carries a fundamental domain and a multiple of the
  regular representation, and Kesten's bound applies on every nonamenable group.
- **Where it dies.** Refuted as stated, on every group where the hypothesis can hold. Open only for a single base of
  entropy at most `log 4`, which has no collapse consequence.

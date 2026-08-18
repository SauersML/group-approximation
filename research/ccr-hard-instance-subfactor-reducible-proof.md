---
rg: 2
id: ccr-hard-instance-subfactor-reducible-proof
kind: route
title: The witness is in the relative commutant by hypothesis
target: ccr-hard-instance-subfactor-reducible
requires: []
artifacts:
  - research/kt-centralizer-normalization-hs.md
---

## Direct proof

`σ(Λ)' ∩ M` is exactly `P' ∩ M` for `P = σ(Λ)''`, since a bounded operator
commutes with a set iff it commutes with the von Neumann algebra it
generates.  If `x ∈ σ(Λ)' ∩ M` is a scalar, the (AC) question at `x` is
vacuous — the displayed distance is `0` for every `γ`, because the whole
unitary group lies in the commutant of a scalar.  So a nontrivial instance
has `x ∉ ℂ1`, and then `P' ∩ M` contains a non-scalar element, i.e.
`P' ∩ M ≠ ℂ1` and `P ⊆ M` is reducible.

For the second sentence: `Q ⊆ P` gives `Q' ⊇ P'`, hence
`Q' ∩ M ⊇ P' ∩ M ⊋ ℂ1`.  So no passage to a subalgebra of the Kazhdan copy
restores irreducibility, and in particular one cannot repair the hypothesis
by replacing `Λ` with a smaller Kazhdan subgroup.

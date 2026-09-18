---
rg: 2
id: artin-ghost-ideal-localizes-to-standard-parabolics
kind: claim
title: "The ghost ideal ⋂_s ZA(1 − s) of an Artin group splits along the cosets of any standard parabolic subgroup, so it vanishes as soon as some standard parabolic subgroup has no ghosts"
distinct_from:
  artin-complex-top-homology-is-intersection-of-ideals: that identifies the top homology of the Artin complex with the ideal; this is a coset-slicing theorem for the ideal itself, which transfers its vanishing from a standard parabolic subgroup to the whole group.
---

Let `A = A_Λ` be an Artin group on a finite set `S`. For `T ⊆ S` write `A_T` for the
standard parabolic subgroup, which is the Artin group of the induced subdiagram (van der
Lek). Define the **ghost ideal**

`G(A_T) = ⋂_{s ∈ T} ZA_T·(1 − s) ⊆ ZA_T`.

By `artin-complex-top-homology-is-intersection-of-ideals`, `G(A)` is the top homology
`H_{|S|−1}(Δ(A); Z)` of the Artin complex. In the language of discrete tomography it is the
kernel of the X-ray transform `ZA → ⊕_{s ∈ S} Z[A/⟨s⟩]` that sums a finitely supported
function along the cosets `g⟨s⟩`: a ghost is an invisible image.

**Theorem.** Let `T ⊆ S` and let `R` be a set of representatives of the left cosets `A/A_T`.
Every `x ∈ ZA` has a unique expansion `x = Σ_{r ∈ R} r·y_r` with `y_r ∈ ZA_T`, almost all
zero, and for every `s ∈ T`:

`x ∈ ZA·(1 − s)` if and only if `y_r ∈ ZA_T·(1 − s)` for every `r`.

Consequently `⋂_{s ∈ T} ZA·(1 − s) = ⊕_{r ∈ R} r·G(A_T)`, and

`G(A) ⊆ ⊕_{r ∈ R} r·G(A_T)`.

In particular, **if `G(A_T) = 0` for some `T ⊆ S`, then `G(A) = 0`.**

The ghost ideal of the free group `A_{st}` with `m_st = ∞` is zero (its X-ray graph is the
Bass–Serre tree), so `G(A) = 0` whenever `Λ` has an edge labelled `∞`.

Proof route: `artin-ghost-ideal-localizes-to-standard-parabolics-proof`. The consequence for
every Artin group with infinite Coxeter group is
`artin-ghost-ideals-reduce-to-four-lanner-trees`.

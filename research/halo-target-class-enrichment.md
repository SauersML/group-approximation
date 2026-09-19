---
rg: 2
id: halo-target-class-enrichment
kind: route
title: Enrich the halo-witness target class so the coordinate action qualifies
target: hyperlinear-wreath-model
requires: []
artifacts:
  - notes/NOTEPAD.md
  - notes/FALSE_HALO_ACTION_AUDIT.md
  - research/artifacts/kun-thom-2608-06222-verified.md
---

# Enrich the halo-witness target class so the coordinate action qualifies

The natural second attempt after `sofic-action-permanence` dies, and the reason
it also dies. Dead twice over, by two independent proofs.

## The idea

Alekseev--Bradford Corollary 5.2 is not stated for one class but for a menu,
verbatim from the source transcription:

> Let 𝒞 be one of the following: (a) The class of sofic groups; (b) The class
> of 𝕂-linear sofic groups, for 𝕂 a field; (c) The class of hyperlinear
> groups; (d) The class of weakly sofic groups. Let Γ, Δ ∈ 𝒞, and let
> β : Γ ↷ Δ be a sofic 𝒞-action by automorphisms. Then Δ ⋊_β Γ ∈ 𝒞.

`coordinate-action-not-sofic` refutes the hypothesis for class (a). But the
hypothesis is "sofic `𝒞`-action", and for a larger class `𝒞` the partial
homomorphisms in a witness may take values in a larger target group. So the
obvious move is to take `𝒞` = hyperlinear (class (c)) and try to build a sofic
hyperlinear-action witness for `G ↷ ⊕_{G/Γ} ℤ/2ℤ` using richer labels —
finite-dimensional unitary, Pauli, or Clifford labels in place of coset labels.
Both the lamp group and `G` are hyperlinear, so Corollary 5.2 would then hand
over hyperlinearity of `W` for free.

## Why it fails, twice

**Class-agnostically** (`single-lamps-recover-set-action`). A sofic `𝒞`-action
on the lamp group, for *any* class `𝒞` whatsoever, forces the underlying set
action `G ↷ G/Γ` to be sofic — read the labels off the single-coordinate lamps
`δ_z`, which are finitely many and injectively labelled, and the covariance
equation becomes the orbit-approximation equation verbatim. The target class is
never used. `coordinate-action-not-sofic` then closes it. This kills every
enrichment simultaneously, including classes not on Alekseev--Bradford's menu.

**Concretely, for the labels one would actually reach for**
(`halo-locally-sofic-target-collapse`). Any witness whose targets are locally
sofic collapses to a sofic-class witness, because each finite test only ever
sees the finitely generated subgroup the labels generate. Finitely generated
subgroups of `U(n)` are linear, hence residually finite by Malcev, hence sofic;
finite Clifford and Pauli groups are finite. So the specific enrichments on
offer are not enrichments at all.

## What survives

The audit's own conclusion, from `notes/FALSE_HALO_ACTION_AUDIT.md`:

> If a hyperlinear-action proof exists, then for some finite test its target
> `Lambda_0` in `(HAA3)` must itself be a finitely generated hyperlinear
> nonsofic group. Producing that target already solves the main problem.
>
> Thus the halo-action theorem is an excellent permanence result once a
> hyperlinear-nonsofic seed is known, but it is circular as a method for
> constructing the first seed.

That is the precise sense in which this route is dead: not blocked by a missing
lemma, but circular. It is worth keeping in the graph for that reason — it
prices the whole permanence toolkit, and it tells anyone reaching for richer
labels that the label alphabet is not where the difficulty lives.

**What a surviving variant would have to change.** Both proofs above attack the
*labels* while leaving the ambient approximation `phi : G -> Sym(A)` a genuine
permutation map. The label-extraction step is what converts a witness back into
an orbit approximation, and it only ever uses that the `pi_s` are injective on a
finite set. So a variant with any chance must replace `Sym(A)` itself — for
instance by unitaries that normalize a MASA only approximately in normalized
Hilbert--Schmidt distance — and must prove that label extraction genuinely fails
in that setting. That is not a weakening of the hypothesis; it is the
non-Cartan embedding problem of `hyperlinear-wreath-model` in different
notation, so the difficulty is conserved and the circularity hazard remains.

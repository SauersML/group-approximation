---
rg: 2
id: masa-normalizing-tracial-action
kind: route
title: HS-ify the Alekseev–Bradford sofic 𝒞-action (masa-normalizing tracial action)
target: hyperlinear-wreath-model
requires: []
artifacts:
  - notes/FALSE_MASA_NORMALIZING_TRACIAL_ACTION.md
  - notes/TRUE_DIAGONAL_NORMALIZER_RIGIDITY.md
---

# HS-ify the Alekseev–Bradford action model

Weaken Alekseev–Bradford Definition 4.23 by replacing the finite set `A` and
`Sym(A)` with a diagonal masa `D_n ⊆ M_n(ℂ)` and a map `φ : G → U(n)` that
approximately normalizes `D_n` in normalized Hilbert–Schmidt norm, then rerun
their Theorem 5.1 in `‖·‖₂`, hoping to escape Kun–Thom because a unitary tuple
has no generator graph. **Dead, under both readings of "approximately
normalizes".**

**Reading (i), uniform defect** — the only reading under which the masa is
structural and under which the ultraproduct statement `u D_𝒰 u* = D_𝒰` is
recovered. Then `diagonal-normalizer-rigidity` clause 1 puts each `φ(g)` at
`‖·‖₂`-distance `3√δ` from a monomial, clause 3 makes the extracted
permutations Hamming-multiplicative with a comparable defect, and the lamp
covariance transfers because `φ(g)` and the monomial are close. The relaxed
notion therefore *contains* a Definition-4.23 model of the same action: it is
equivalent to a sofic action, not weaker, and `coordinate-action-not-sofic`
kills it. The premise that "unitaries have no generator graph" is false for
unitaries constrained against a full masa — clause 1 recovers the graph.

**Reading (ii), defect tested only on the finitely many lamp elements.** Then
the rigidity lemma correctly does not apply, but the masa has been discarded
and what remains is: maps `ρ : Δ → U(n)`, `V : Γ → U(n)`, multiplicative and
separating on windows, with `‖V(g)ρ(h)V(g)* − ρ(β(g)[h])‖₂ < ε`. By
Alekseev–Bradford Lemma 3.4 plus a product map this is *equivalent* to
hyperlinearity of `Δ ⋊_β Γ` — the converse is immediate from
`φ(g)φ(h)φ(g)⁻¹ ≈ φ(ghg⁻¹)`. The permanence statement becomes the identity map
on the problem.

**Where the permutations are load-bearing in Theorem 5.1.** A line-by-line
audit (in the cited note) finds that Lemma 3.4, product-compatibility, the
final amalgamation with a separating `θ : Γ → G_(i₃)`, condition (i) and the
lamp separation all survive HS-ification verbatim. Exactly two steps break,
conditions (ii) and (iv) of Lemma 3.4, and both break on the same
object: the *acting map* `ψ : Sym(A) → G_(i₂)` of wreath-compatibility, whose
condition (b) is Hamming-to-`d_(i₂)` uniform continuity and whose condition
(c) is an **exact** conjugation identity `ψ(σ)τ(g)ψ(σ)⁻¹ = τ(σ·g)`. That
interface is the entire content of the framework — it converts a combinatorial
action model into a metric one. Remove it and no theorem remains; keep any
masa-level version of it and reading (i) reinstates the combinatorial model.

This refines, rather than repeats, `sofic-action-permanence`: that route
records that Alekseev–Bradford's *hypothesis* is unavailable. This one records
that the hypothesis has no Hilbert–Schmidt weakening either.

## Where label extraction fails, run explicitly

The single-lamp lemma of `notes/NOTEPAD.md` extracts injective set labels
`j_s(z) = π_s(δ_z)` from the partial homomorphisms of Definition 4.23 and
observes that the covariance equation *is* the orbit-approximation equation;
`notes/FALSE_HALO_ACTION_AUDIT.md` adds that enriching the target class cannot
help. Both keep `φ : G → Sym(A)`. Running the same extraction against a
tracial model, where the labels would be the minimal projections of the masa
and the would-be permutation is the one `Ad(φ(g))` induces on them:

- **Under reading (i) extraction goes through, and the coupling does not
  degrade.** The natural guess is that an approximately normalizing unitary
  permutes minimal projections only up to small corners, so that injective
  labels weaken to a sub-stochastic coupling. The coupling is exactly the
  doubly stochastic matrix `A_ij = |φ(g)_ij|²`, and
  `diagonal-normalizer-rigidity` shows the uniform defect bound forces
  `E_i[max_j A_ij] ≥ 1 − δ²`: the coupling is pinned to be nearly
  deterministic, with slack bounded by the defect and *independent of the
  dimension*. So the labels survive, they are Hamming-multiplicative, and the
  Kun–Thom obstruction applies unchanged. The difficulty is conserved exactly
  as the lamp lemma warns.
- **Under reading (ii) extraction fails, for a reason that is measured rather
  than hoped for.** The lamps only pin the coupling on the coordinates being
  tested. Writing `B_E = ⟨S_y : y ∈ E⟩` inside a larger window `E'`, the
  induced doubly stochastic matrix on the `2^{|E'|}` atoms of `B_{E'}` is
  deterministic on the `E`-coordinates and may be maximally mixing on
  `E' ∖ E`. The atoms of `B_E` have trace `2^{−|E|}`, a constant, while the
  masa's minimal projections have trace `1/N`; the gap between the two
  resolutions is the entire room, and it is exponential.

So the extraction argument does not kill the tracial programme outright, but it
does show the masa cannot be part of the definition — which is what leaves the
formulation tautologous under reading (ii).

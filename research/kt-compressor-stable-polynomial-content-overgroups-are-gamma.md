---
rg: 2
id: kt-compressor-stable-polynomial-content-overgroups-are-gamma
kind: claim
title: For the Theorem E pair the only compressor-stable overgroup of Gamma with polynomial elementary content is Gamma itself
distinct_from:
  kt-compressor-stable-overgroups-have-polynomial-content: that proves the content of a compressor-stable overgroup missing the normal closure is A; this asks whether content A already forces Δ = Γ
  kt-monomial-split-coset-wreaths-collapse-to-gamma: that settles the split overgroups E_r(F_q[M]) ⋊ Q; this is the non-split residue
  kt-pair-hyperlinear-floor-below-normal-closure: that is a hyperlinearity question; this is purely group-theoretic, and it would make that node equivalent to hyperlinear-wreath-model
---

**OPEN.** Notation as in
`kt-compressor-stable-overgroups-have-polynomial-content`. Let `Δ ≤ G` with

```text
Γ ≤ Δ,     P Δ P^(-1) ≤ Δ for all P ∈ Mon = SL_d(Z) ∩ M_d(N),     e_12(f) ∈ Δ ⇒ f ∈ A.
```

Then `Δ = Γ`.

A weaker version suffices for the reduction route
`kt-pair-floor-reduces-to-wreath-model-via-compressor-sandwich`. That version assumes in
addition that `P_Γ` compresses `Δ` (not only `Mon`), or that `Δ = Δ_hl(Γ,G)`.

## What is known

* The elementary content is forced: any `Mon`-stable `Δ ⊇ Γ` missing `⟨⟨Γ⟩⟩` satisfies
  the third hypothesis (`kt-compressor-stable-overgroups-have-polynomial-content`).
* `π(Δ)` is contained in `{±I}` or is Zariski dense. If `π(Δ)` consists of permutation
  matrices, `Δ = Γ`. Split overgroups `E_r(F_q[M]) ⋊ Q` with `M` proper are never
  `Mon`-stable unless they equal `Γ`, since their compressor core is `Γ`
  (`kt-monomial-split-coset-wreaths-collapse-to-gamma`).

## Why it is not routine

The hypotheses resemble the sandwich classification of overgroups of `E_r(A)` in
`GL_r(R)`. That classification is a theorem when the overgroup is normalized by `E_r(R)`,
and in some integral-extension settings. Here `R = A[x^(-1)]` is not integral over `A`.
Stepanov's free-product constructions of nonstandard overgroups of an elementary group
over a subring show that small root content alone does not force standardness in general.
What remains to exploit is stability under the compressors. Two unfinished lines of
attack were tried:

1. *Lattices.* For `H = Δ ∩ EL_r(R)`, the `A`-lattice `L = H·A^r` is `H`-stable, and its
   multiplier ring `O(L)` contains `A`. If `L` were finitely generated, integrality would
   give `O(L) = A`. Combined with the content condition this might give `H ≤ SL_r(A)`.
   Finite generation is not known.
2. *Transvection bookkeeping.* Conjugating `e_ij(a)` (`a ∈ A`) by `h ∈ H` and
   compressing by `I + kE_ab` produces elements whose elementary parts must stay
   polynomial. No computation along these lines reached `h ∈ SL_r(A)`.

A `Mon`-stable counterexample `Δ ≠ Γ` would not refute
`kt-pair-hyperlinear-floor-below-normal-closure`. It would supply the first candidate
below the normal closure that does not collapse to `hyperlinear-wreath-model`.

## Attempts

* **Reduction to the kernel (w3-121).** The projection part is not a separate problem.
  If the kernel `H = Δ ∩ EL_r(R)` lies in `SL_r(A)`, conjugating `U_ij(A)` by
  `(g,P) ∈ Δ` gives `g·M_r(P·A)·g^(-1) ⊆ M_r(A)`, hence `P·A ⊆ A`. The same holds for
  `P^(-1)`, so `π(Δ)` consists of permutation matrices, and the central-finite dichotomy
  makes it trivial. So this claim is equivalent to
  `kt-compressor-stable-kernel-overgroups-are-polynomial`
  (`kt-compressor-sandwich-equivalent-to-kernel-polynomiality`, route
  `kt-sandwich-from-kernel-polynomiality`). The Zariski-dense branch needs no separate
  treatment. Along the way: the entries of the kernel span `A` or `R`, and the
  one-variable analogue holds with no compressors (`SL_r(F_q[t])` is maximal in
  `SL_r(F_q[t^(±1)])`). The density argument behind it dies for `d ≥ 2` because no
  valuation ring meets `R` in `A`.
* **Kernel case proved (w5-121).** `kt-compressor-stable-kernel-overgroups-are-polynomial`
  is proved by `kt-kernel-overgroups-polynomial-via-vertex-compressors-proof`. For each bad
  exponent, one positive unimodular compressor, with all rows in a single normal cone of the
  column's Newton polytope, makes the column a monomial times an `A`-unimodular vector, and
  it also exposes the bad exponent. With `kt-sandwich-from-kernel-polynomiality` this proves
  the claim.

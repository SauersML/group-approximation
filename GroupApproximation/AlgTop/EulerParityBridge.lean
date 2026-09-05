import Mathlib

/-!
# The Euler-parity bridge: what is still owed, stated exactly

Lane `found-euler-class`, campaign target 3 (STW Problem LIX).

## Where the campaign stands

The proof of Lemma 2 of
`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`
is a parity contradiction between two numbers:

* the **zero count**.  The manuscript's section (2.10) of `W_g` has exactly one zero.
  This is proved, without any topology, in `AlgTop/ManuscriptSectionZeroCount.lean`
  (`manuscriptSection_eq_zero_iff`, `manuscriptSection_zero_unique`,
  `manuscriptSection_zero_exists`), on top of `AlgTop/MappingTorusSectionZeros.lean`
  and `AlgTop/CPTautologicalSection.lean`.
* the **Chern number**.  Lemma 3 gives `⟨c_r(W), [S¹ × M]⟩ ∈ 2ℤ` for every `W`
  restricting to `V` on the slice.  That is `AlgTop/MappingTorusParity.lean`
  (`two_dvd_chern_top`, `even_chern_top_pairing`).

Both halves are being supplied.  **What is not supplied, by anyone, is the sentence
that connects them**, and this file states it exactly rather than leaving it implicit
in a proof sketch.

## The missing input, precisely

```text
Even ⟨c_r(W_g), [S¹ × M]⟩  ↔  Even (number of zeros of the section)
```

This is the identity "the top Chern number of a complex bundle over a closed manifold
of matching dimension is the signed count of the zeros of a section with isolated
nondegenerate zeros", reduced mod `2`.  It is the composite of two classical facts:
the Euler class of the underlying oriented real bundle is the top Chern class
([Hatcher, VBKT, Prop. 3.13]), and the Euler number is the sum of the local indices of
such a section.  Discharging it needs a Thom class, which needs a relative cohomology
theory with excision; none of that exists in Mathlib at the campaign pin
(`git grep` at `81a5d257` finds no `ThomClass`, no `eulerClass`, no `fundamentalClass`,
no `ChernClass`, no `StiefelWhitney`, no Poincaré duality).

**Why mod 2 is the right form to owe.**  The oriented statement additionally requires
choosing an orientation of `S¹ × S⁵ × ∏ⱼ ℂP^{dⱼ}` and of `W_ℝ`, and computing the sign
of the determinant of the derivative at the zero — which for the tautological-line
version of the section is componentwise conjugation on `ℂ^d`, of real determinant
`(-1)^d`, so the sign is `(-1)^{Σⱼ dⱼ}` and has to be tracked through the product.
Mod `2` all of that disappears and the local input degenerates to *the derivative is
invertible*, which is exactly what `AlgTop/EulerLocalModel.lean`
(`eulerLocalModelEquiv`) and the chart homotopy
`CPn.tautChartHomotopy_eq_zero_iff` already supply.  Nothing else about the two
routes differs: the top-degree pairing itself is available integrally, from Künneth
and the sphere pairings of `notes/algtop-foundation-plan-2026-09-05.md`, with no
Poincaré duality.

## What this file contains

Only the arithmetic, fully proved and unconditional: given the bridge, Lemma 3, and
the count, the contradiction is immediate.  **The mathematical content of this file is
the specification above, not the lemmas below** — the lemmas are one line each, and
saying so is the point.  `lemmaTwo_contradiction` is the shape the assembled Lemma 2
will have, so that when the bridge is supplied the endpoint needs no rearranging.
-/

namespace GroupApproximation.AlgTop

/-- The parity contradiction, in the only arithmetic it needs.  `hbridge` is the owed
topological input; `hEven` is Lemma 3; `hOdd` is the zero count. -/
theorem false_of_parity_mismatch {n : ℤ} {k : ℕ}
    (hbridge : Even n ↔ Even k) (hEven : Even n) (hOdd : ¬ Even k) : False :=
  hOdd (hbridge.mp hEven)

theorem not_even_one : ¬ Even 1 := by decide

/-- **The shape of the assembled Lemma 2.**  `eulerNumber` is
`⟨c_r(W_g), [S¹ × M]⟩`; `zeroCount` is the number of zeros of the manuscript's section
(2.10), which `AlgTop/ManuscriptSectionZeroCount.lean` shows is `1`; `hEven` is
Lemma 3 (`AlgTop/MappingTorusParity.lean`); and `hbridge` is the one input nobody has
yet supplied, specified in this file's header.

Stated this way, the hypothesis that is still owed is visible in the statement rather
than hidden inside a proof, and the endpoint will not need rearranging when it
arrives. -/
theorem lemmaTwo_contradiction {eulerNumber : ℤ} {zeroCount : ℕ}
    (hbridge : Even eulerNumber ↔ Even zeroCount)
    (hEven : Even eulerNumber)
    (hcount : zeroCount = 1) : False := by
  refine false_of_parity_mismatch hbridge hEven ?_
  rw [hcount]
  exact not_even_one

end GroupApproximation.AlgTop

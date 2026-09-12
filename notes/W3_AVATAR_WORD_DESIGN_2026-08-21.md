# W3 design: the explicit avatar word family (2026-08-21)

Coordinator's word-level design for the free-group avatar router
(research/free-group-avatar-router.md), at the precision the
`RouterRelatorDesign` scaffold consumes.  Everything here is finite
word combinatorics; the gate and torsion leaves are consumed through
`GreendlingerFreeGate.router_conclusions_of_metric` only.

## 0. Inputs and notation

F = FreeGroup(y₁, y₂).  E = the source skeleton, finitely presented;
B = Γ(3) (the certified partner), finitely presented.  V = total number
of avatar-carrying generators (E's plus B's plus slack), ℓ_d = the word
length of the protected element d (the marked commutator) in E's
generators.

## 1. The padding step (load-bearing, do it FIRST)

The ball-injectivity engine demands `2·|W_d| ≤ min relator length`,
and both sides scale LINEARLY in avatar length — so avatar inflation
alone can never fix a short presentation relator.  The constraint is
presentational: every relator of the presentations fed to the rewriter
must be longer than `2·ℓ_d + margin` AS A WORD.  Standard Tietze
padding achieves this: adjoin a fresh generator w with defining
relator `w·(long word)⁻¹`, and replace each short relator ρ by
`ρ·w·(long word)⁻¹`; the presented group is unchanged and every
relator is long.  For the integerSource skeleton ℓ_d ≈ 10, so padding
to ≥ 30 letters suffices; Γ(3)'s thirteen-relator-descended
presentation pads the same way.  The padded presentations are part of
the DESIGN DATA, not an afterthought — w3's structure should carry
them explicitly.

## 2. The avatar code

Enumerate the avatar-carrying generators ν = 1, …, V.  Fix
L := 16·(V + 1) and K := 2L — the family is designed at metric constant
**C'(1/8)**, not 1/6 (UPDATE 2026-08-21 late: at λ ≤ 1/8, consumed in
the SHARP form |u| > (1−3λ)|r|, the torsion descent's residual case
A2b is arithmetically empty — see the finewilf decomposition; the
stronger constant costs only a larger L and removes a van-Kampen-class
atom from the program).  Assign

    W_ν := ∏_{j=1}^{L}  y₁ · y₂^( K·ν + j )

— positive words, globally distinct y₂-exponents (ranges
[Kν, Kν + L) are pairwise disjoint and each exponent appears exactly
once in the whole system).

Properties, each with its intended Lean discharge:
(a) Junction control: in any rewritten relator, a junction
    `W_x^{±} W_{x'}^{±}` cancels at most inside one y₂-run (exponents
    differ), so rewritten relators stay within one letter of their
    nominal length and are cyclically reduced after one normalization
    pass (design the enumeration so first/last exponents of adjacent
    avatars in every relator differ — free of charge since ALL
    exponents differ).
(b) Pieces: a common subword of two distinct symmetrized relators
    containing two consecutive y₂-runs pins (ν, j) uniquely, so
    pieces have length < 2·A_max + 2 with A_max = KV + L, while every
    relator has length ≥ (min padded word length)·L·A_min-ish; with
    L = 12(V+1) the ratio is comfortably below 1/6.  The Lean form:
    a decidable check on the FINITE family (the family is explicit,
    so `MetricSmallCancellation R (1/6)` is a finite computation —
    budget for a decide-style or hand-rolled verification lemma; this
    is the main mechanical cost).
(c) No proper powers: a period of a rewritten relator would translate
    the strictly increasing exponent sequence onto itself —
    impossible; discharge via the landed
    `PeriodicOverlap`/`noProperPower_symmetrization` toolkit on the
    exponent-sequence abstraction.
(d) Protected ball: |W_d| = ℓ_d·(avatar length), and after §1 every
    relator length ≥ (2ℓ_d + margin)·(avatar length), giving the
    engine's `2·|W_d| ≤ min |r|` with margin.

## 3. The relator family

    R := R_E ∪ R_B ∪ R_tie,
    R_E   = padded E-relators rewritten through the E-avatars,
    R_B   = padded B-relators rewritten through the B-avatars,
    R_tie = { y₁·T₁⁻¹, y₂·T₂⁻¹, y₁·T₁'⁻¹, y₂·T₂'⁻¹ },

with T_j the avatars of designated LONG words in the defect free pair
(a, b) — giving `y_j ∈ φ(N)`, hence defect_top and route_surjective —
and T'_j the avatars of designated long B-words — giving
`y_j ∈ ψ(B)`, hence partner_surjective and (T)-descent.  The four tie
words use exponent blocks disjoint from everything else and from each
other; their lengths are chosen ≥ the §1 padding floor.  Two-generation
is by presentation.  Finite presentation: |R| is finite by
construction.

## 4. Well-definedness

φ (resp. ψ) is defined on generators by the avatars; the required
check `∀ padded relator ρ, ρ(W…) ∈ ⟨⟨R⟩⟩` is literal membership of
R_E (resp. R_B) members — `subset_normalClosure`-level, no
combinatorics.  This is where the scaffold's current sorries at
well-definedness discharge for free once the family is explicit.

## 5. What remains genuinely open after this design

Only the two free-group leaves: `greendlingerConclusion_of_metric`
(the n ≥ 3 count) and the arc-inside-one-period case of the torsion
leaf.  Everything else in the router instantiation is finite
computation against this explicit family.  The design constants (L, K,
padding floor) are deliberately generous; shrinking them buys nothing.

import Mathlib.Algebra.FreeAlgebra
import GroupApproximation.Leavitt.UniversalLeavitt
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVSkewLaurentK2.Interface
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVStableK2.Reduction

/-!
# One-sided localization cores for stable `K₂(L_{𝔽₂}(1,2)) = 0` (lane LVK2Route)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`, "The finitely presented case"),
leaf T1b.iii, input W1: `LVH2GL3.StableK2Trivial (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))`.

Every known proof of W1 uses a localization step for `K₂` (Quillen 1973, §5 Thm 5).  The
two-sided Mayer–Vietoris form (`YaoFactorization`, Yao 1995 Thm 2.1) is more than is needed:
the localization sequence for a noncommutative Ore set gives exactness of
`K₂(R) → K₂(R[Σ⁻¹]) → K₁(T_Σ)`, where `T_Σ` is the category of `Σ`-torsion modules.  When
`K₁(T_Σ) = 0` this is the **base surjectivity** `LVStableK2.StableK2BaseSurjective` of the
localization map.  This file records two instances, each reducing W1 to one core:

* **Core-A** (skew Laurent): `S[t,t⁻¹;φ] = S[t;φ][t⁻¹]` with `t` normal; dévissage
  (Quillen 1973 §5 Thm 4) gives `K₁(T_t) = K₁(S)`, which is `0` for ultramatricial `𝔽₂`-rings.
  So `K₂(S[t;φ]) ↠ K₂(S[t,t⁻¹;φ])`, and only the *positive* half `S[t;φ]` is needed
  (`stableK2Trivial_skewLaurent_of_halfBaseSurjective`).  This replaces the two-sided
  `YaoFactorization` together with the negative half of `HalfK2Statement`.
* **Core-B** (universal localization): `L_{𝔽₂}(1,2)` is the universal localization of the free
  algebra `𝔽₂⟨x₀,x₁⟩` inverting the row `(x₀ x₁)` (Cohn; Ara–Brustenga–Cortiñas 2009,
  `yaoseq6.tex` Sec. 4).  The free algebra is a fir, so the localization is stably flat
  (Bergman–Dicks 1978), and Neeman–Ranicki 2004 give the localization sequence; the torsion
  category has `K₁ = K₁(𝔽₂) = 0`.  With Gersten's `K₂(𝔽₂⟨x₀,x₁⟩) = K₂(𝔽₂) = 0` this gives W1
  (`binaryLeavitt_stableK2Trivial_of_freeBaseSurjective`).

Each core is also *necessary* (the converse theorems), so these are exact reformulations.
-/

namespace GroupApproximation.Full.LVK2Route

section CoreA

variable {S : Type*} [Ring S] [MulSemiringAction (Multiplicative ℤ) S]

/-- **Core-A reduction.**  If `K₂(S[t;φ]) → K₂(S[t,t⁻¹;φ])` is stably surjective and
`S[t;φ]` has stable `K₂ = 0`, then `S[t,t⁻¹;φ]` has stable `K₂ = 0`.  (Quillen 1973 §5 Thm 4-5;
Yao 1995; `yaoseq6.tex` l.574-640; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem stableK2Trivial_skewLaurent_of_halfBaseSurjective
    (hB : LVStableK2.StableK2BaseSurjective (LVSkewLaurentK2.skewHalf S 1).subtype)
    (hPos : LVH2GL3.StableK2Trivial (LVSkewLaurentK2.skewHalf S 1)) :
    LVH2GL3.StableK2Trivial (LVSkewLaurentK2.SkewLaurent S) :=
  LVStableK2.stableK2Trivial_of_baseSurjective _ hB hPos

/-- Core-A with the positive component of the half-ring interface `HalfK2Statement`; the negative
half is not used.  (`yaoseq6.tex` l.574-640; `simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem stableK2Trivial_skewLaurent_of_halfBaseSurjective_of_halfK2
    (hB : LVStableK2.StableK2BaseSurjective (LVSkewLaurentK2.skewHalf S 1).subtype)
    (hHalf : LVSkewLaurentK2.HalfK2Statement S) :
    LVH2GL3.StableK2Trivial (LVSkewLaurentK2.SkewLaurent S) :=
  stableK2Trivial_skewLaurent_of_halfBaseSurjective hB hHalf.1

/-- **Core-A is necessary.**  Stable `K₂(S[t,t⁻¹;φ]) = 0` gives the base surjectivity.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem halfBaseSurjective_of_stableK2Trivial
    (hL : LVH2GL3.StableK2Trivial (LVSkewLaurentK2.SkewLaurent S)) :
    LVStableK2.StableK2BaseSurjective (LVSkewLaurentK2.skewHalf S 1).subtype :=
  LVStableK2.baseSurjective_of_stableK2Trivial _ hL

/-- **Core-A versus the endpoint**, given stable `K₂(S[t;φ]) = 0`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem halfBaseSurjective_iff_stableK2Trivial
    (hPos : LVH2GL3.StableK2Trivial (LVSkewLaurentK2.skewHalf S 1)) :
    LVStableK2.StableK2BaseSurjective (LVSkewLaurentK2.skewHalf S 1).subtype ↔
      LVH2GL3.StableK2Trivial (LVSkewLaurentK2.SkewLaurent S) :=
  ⟨fun hB => stableK2Trivial_skewLaurent_of_halfBaseSurjective hB hPos,
    halfBaseSurjective_of_stableK2Trivial⟩

end CoreA

section CoreB

/-- The generators `s₀, s₁` of `L_{𝔽₂}(1,2)`, the images of the free generators `x₀, x₁`.
(`yaoseq6.tex` Sec. 4; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
noncomputable def freeGen : Fin 2 → BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2) :=
  ![(BinaryLeavitt.family (ZMod 2)).s0, (BinaryLeavitt.family (ZMod 2)).s1]

/-- The universal-localization map `𝔽₂⟨x₀,x₁⟩ → L_{𝔽₂}(1,2)`, `xᵢ ↦ sᵢ` (Cohn; Ara–Brustenga–
Cortiñas 2009, `yaoseq6.tex` Sec. 4).  (`simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
noncomputable def freeToLeavitt :
    FreeAlgebra (ZMod 2) (Fin 2) →+* BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2) :=
  (FreeAlgebra.lift (ZMod 2) freeGen).toRingHom

/-- `freeToLeavitt` sends the free generator `xᵢ` to `sᵢ`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem freeToLeavitt_ι (i : Fin 2) :
    freeToLeavitt (FreeAlgebra.ι (ZMod 2) i) = freeGen i :=
  FreeAlgebra.lift_ι_apply freeGen i

/-- **Core-B reduction.**  Stable surjectivity of `K₂(𝔽₂⟨x₀,x₁⟩) → K₂(L_{𝔽₂}(1,2))`
(Neeman–Ranicki 2004 localization; Bergman–Dicks 1978 stable flatness) and Gersten's stable
`K₂(𝔽₂⟨x₀,x₁⟩) = 0` give W1.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem binaryLeavitt_stableK2Trivial_of_freeBaseSurjective
    (hB : LVStableK2.StableK2BaseSurjective freeToLeavitt)
    (hF : LVH2GL3.StableK2Trivial (FreeAlgebra (ZMod 2) (Fin 2))) :
    LVH2GL3.StableK2Trivial (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) :=
  LVStableK2.stableK2Trivial_of_baseSurjective freeToLeavitt hB hF

/-- **Core-B is necessary.**  W1 gives the base surjectivity of `freeToLeavitt`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem freeBaseSurjective_of_stableK2Trivial
    (h : LVH2GL3.StableK2Trivial (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))) :
    LVStableK2.StableK2BaseSurjective freeToLeavitt :=
  LVStableK2.baseSurjective_of_stableK2Trivial freeToLeavitt h

/-- **Core-B versus W1**, given Gersten's stable `K₂(𝔽₂⟨x₀,x₁⟩) = 0`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem freeBaseSurjective_iff_stableK2Trivial
    (hF : LVH2GL3.StableK2Trivial (FreeAlgebra (ZMod 2) (Fin 2))) :
    LVStableK2.StableK2BaseSurjective freeToLeavitt ↔
      LVH2GL3.StableK2Trivial (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) :=
  ⟨fun hB => binaryLeavitt_stableK2Trivial_of_freeBaseSurjective hB hF,
    freeBaseSurjective_of_stableK2Trivial⟩

end CoreB

end GroupApproximation.Full.LVK2Route

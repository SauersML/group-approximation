import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVSkewLaurentK2.Interface
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnK2.Coefficients

/-!
# Yao's fibration: the formal reduction (lane LVSkewLaurentK2-3a)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii; work order
WO-LVCohnK2-3.  Ara–Brustenga–Cortiñas (2009) `thm:skewyao` (`yaoseq6.tex` l.574-640) computes
`K₂(S[t,t⁻¹;φ])` from Yao's fibration: Step 1 is the Mayer–Vietoris exactness
`K₂(S[t₊]) ⊕ K₂(S[t₋]) → K₂(S[t₊,t₋]) → K₁(S) ⊕ K₁(S)`.  When `K₁(S) = 0` and both half rings have
stable `K₂ = 0`, the middle term vanishes.  This file proves that implication at the level of
Steinberg groups:

* `subtype_comp_halfConst`, `ringMap_subtype_halfConst`: constants pass through either half ring;
* `projection_ringMap_halfConst_eq`: a constant elementary matrix lifts to both half rings;
* `stableK2Trivial_of_yaoFactorization`: `K1Statement S`, `HalfK2Statement S` and
  `YaoFactorization S` give stable `K₂(S[t,t⁻¹;φ]) = 0`.

Proof: pad `k` to `a · b` (the factorization).  The image of `a` in `E_N(S[t;φ])` is a constant
matrix `g ∈ GL_N(S) = E_N(S)`.  Lift `g` to `e ∈ St_N(S)` and move `e` from `a` to `b`:
`a' = a · e₊⁻¹` and `b' = e₋ · b`.  Both lie in `K₂`, so both die after padding.
-/

namespace GroupApproximation.Full.LVSkewLaurentK2

open SteinbergGroup

section Reduction

variable {S : Type*} [Ring S] [MulSemiringAction (Multiplicative ℤ) S]

/-- The constants of either half ring are the constants of `S[t,t⁻¹;φ]`.
(`yaoseq6.tex` `thm:skewyao`; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem subtype_comp_halfConst (ε : ℤ) :
    (skewHalf S ε).subtype.comp (halfConst S ε) = constMap S :=
  RingHom.ext fun _ => rfl

/-- Steinberg elements with constant coefficients pass through either half ring.
(`yaoseq6.tex` `thm:skewyao`; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem ringMap_subtype_halfConst {N : ℕ} (ε : ℤ) (e : SteinbergGroup (Fin N) S) :
    ringMap (skewHalf S ε).subtype (ringMap (halfConst S ε) e) = ringMap (constMap S) e := by
  rw [LVCohnK2.ringMap_ringMap, subtype_comp_halfConst]

/-- The image in `E_N(S[t^ε;φ^ε])` of a Steinberg element with constant coefficients.
(`yaoseq6.tex` `thm:skewyao`; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem coe_projection_ringMap_halfConst {N : ℕ} (ε : ℤ) (e : SteinbergGroup (Fin N) S) :
    ((projection (ringMap (halfConst S ε) e) : elementaryGroup (Fin N) (skewHalf S ε)) :
      (Matrix (Fin N) (Fin N) (skewHalf S ε))ˣ) =
      elementaryMatrixUnitMap (halfConst S ε)
        ((projection e : elementaryGroup (Fin N) S) : (Matrix (Fin N) (Fin N) S)ˣ) := by
  rw [LVCohnK2.projection_ringMap, elementaryGroupMap_apply]

/-- **Yao's fibration, formal step.**  If `GL_n(S) = E_n(S)` for `n ≥ 2`, both half rings
`S[t;φ]` and `S[t⁻¹;φ⁻¹]` have stable `K₂ = 0`, and the Mayer–Vietoris factorization holds, then
`S[t,t⁻¹;φ]` has stable `K₂ = 0`.  (Ara–Brustenga–Cortiñas 2009, `thm:skewyao`, Steps 1-2,
`yaoseq6.tex` l.574-640: the terms `NK₂₊ ⊕ NK₂₋ ⊕ coker(1 - φ on K₂) ⊕ ker(1 - φ on K₁)` all
vanish; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem stableK2Trivial_of_yaoFactorization (hK1 : K1Statement S) (hHalf : HalfK2Statement S)
    (hYao : YaoFactorization S) : LVH2GL3.StableK2Trivial (SkewLaurent S) := by
  intro n k hk
  obtain ⟨hPos, hNeg⟩ := hHalf
  obtain ⟨N, h, a, b, g, hN, hkab, hag⟩ := hYao n k hk
  obtain ⟨e, he⟩ := projection_surjective (I := Fin N) (R := S) ⟨g, hK1 N hN g⟩
  obtain ⟨a', ha'⟩ : ∃ a' : SteinbergGroup (Fin N) (skewHalf S 1),
      a' = a * (ringMap (halfConst S 1) e)⁻¹ := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b' : SteinbergGroup (Fin N) (skewHalf S (-1)),
      b' = ringMap (halfConst S (-1)) e * b := ⟨_, rfl⟩
  have hsplit : indexMap (Fin.castLEEmb h) k =
      ringMap (skewHalf S 1).subtype a' * ringMap (skewHalf S (-1)).subtype b' := by
    rw [hkab, ha', hb', map_mul, map_mul, map_inv, ringMap_subtype_halfConst,
      ringMap_subtype_halfConst, mul_assoc, inv_mul_cancel_left]
  have hpe : projection (ringMap (halfConst S 1) e) = projection a := by
    apply Subtype.ext
    rw [coe_projection_ringMap_halfConst, he]
    exact hag.symm
  have ha'1 : projection a' = 1 := by
    rw [ha', map_mul, map_inv, hpe, mul_inv_eq_one]
  have hb'1 : projection b' = 1 := by
    apply LVCohnK2.projection_eq_one_of_ringMap (skewHalf S (-1)).subtype
      (skewHalf S (-1)).subtype_injective
    have hkN : projection (indexMap (Fin.castLEEmb h) k) = 1 :=
      LVH2GL3.projection_indexMap_eq_one (Fin.castLEEmb h) hk
    rw [hsplit, map_mul, LVCohnK2.projection_ringMap (skewHalf S 1).subtype a', ha'1, map_one,
      one_mul] at hkN
    exact hkN
  obtain ⟨N₁, h₁, hN₁⟩ := hPos N a' ha'1
  obtain ⟨N₂, h₂, hN₂⟩ := hNeg N b' hb'1
  have hnM : n ≤ N₁ + N₂ := by omega
  have hNM : N ≤ N₁ + N₂ := by omega
  have h1M : N₁ ≤ N₁ + N₂ := by omega
  have h2M : N₂ ≤ N₁ + N₂ := by omega
  refine ⟨N₁ + N₂, hnM, ?_⟩
  have ha'M : indexMap (Fin.castLEEmb hNM) a' = 1 := by
    rw [← LVH2GL3.indexMap_castLEEmb_castLEEmb h₁ h1M a', hN₁, map_one]
  have hb'M : indexMap (Fin.castLEEmb hNM) b' = 1 := by
    rw [← LVH2GL3.indexMap_castLEEmb_castLEEmb h₂ h2M b', hN₂, map_one]
  rw [← LVH2GL3.indexMap_castLEEmb_castLEEmb h hNM k, hsplit, map_mul,
    LVStableK2.indexMap_ringMap, LVStableK2.indexMap_ringMap, ha'M, hb'M, map_one, map_one,
    one_mul]

end Reduction

end GroupApproximation.Full.LVSkewLaurentK2

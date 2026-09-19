import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnColimit.Shift
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnColimit.Witness
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnK2.Products

/-!
# Descent of `K₂`-classes along the corner-shift colimit (lane LVCohnColimit)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii.  In Step 3 of the
proof of the degree-two Ara–Brustenga–Cortiñas theorem (`yaoseq6.tex` thm:skewyao; ABC,
Münster J. Math. 2 (2009), Thm 3.6) the Cohn algebra `C = C_2(𝔽₂)` is compared with the
direct limit `D` of the unital corner shifts
`θ_M : C × 𝔽₂ → C × 𝔽₂`, `(c, λ) ↦ (x^M c y^M + λ (1 - x^M y^M), λ)`.
This file proves, for an arbitrary ring `D` receiving compatible injective maps
`ι_M : C × 𝔽₂ → D` whose ranges exhaust `D`:

* `projection_eq_one_of_fst_snd`: an element of `St_I(R × K)` lies in `K₂` once both of its
  coordinate images do;
* `ringMap_fst_nonUnitalMap_inl`, `ringMap_snd_nonUnitalMap_inl`: `fst ∘ inl = id`,
  `snd ∘ inl = 0` on Steinberg groups;
* `ringMap_fst_cohnTheta_inl`: `fst ∘ θ_M ∘ inl` is the corner shift `a ↦ x^M a y^M`;
* `eq_one_of_ringMap_rangeRestrict_eq_one`: along an injective ring map, `St_I` of the source
  embeds into `St_I` of the range;
* `exists_cohnTheta_eq_one`: a class dying in `St_I(D)` already dies under some `θ_M`;
* `cohnShiftPow_descent`: if `D` has stable `K₂ = 0`, then every `k ∈ K₂(n, C)` is killed, after
  padding, by some corner shift `a ↦ x^M a y^M`.
-/

namespace GroupApproximation.Full.LVCohnColimit

open SteinbergGroup

noncomputable section

section Coordinates

variable {I : Type*} [Fintype I] [DecidableEq I] {R K : Type*} [Ring R] [Ring K]

/-- An element of `St_I(R × K)` whose two coordinate images lie in `K₂` lies in `K₂`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem projection_eq_one_of_fst_snd (u : SteinbergGroup I (R × K))
    (h1 : projection (ringMap (RingHom.fst R K) u) = 1)
    (h2 : projection (ringMap (RingHom.snd R K) u) = 1) : projection u = 1 := by
  rw [LVCohnK2.projection_ringMap] at h1 h2
  apply Subtype.ext
  apply Units.ext
  ext i j
  have e1 := congrArg
    (fun g : elementaryGroup I R => ((g : (Matrix I I R)ˣ) : Matrix I I R) i j) h1
  have e2 := congrArg
    (fun g : elementaryGroup I K => ((g : (Matrix I I K)ˣ) : Matrix I I K) i j) h2
  exact Prod.ext
    (e1.trans (congrArg (fun A : Matrix I I R => A i j)
      (map_one ((RingHom.fst R K).mapMatrix (m := I)))).symm)
    (e2.trans (congrArg (fun A : Matrix I I K => A i j)
      (map_one ((RingHom.snd R K).mapMatrix (m := I)))).symm)

/-- `fst ∘ inl = id` on Steinberg groups.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf
T1b.iii.) -/
theorem ringMap_fst_nonUnitalMap_inl (u : SteinbergGroup I R) :
    ringMap (RingHom.fst R K) (LVCohnK2.nonUnitalMap (LVCohnK2.inlHom R K) u) = u := by
  have hh : (ringMap (I := I) (RingHom.fst R K)).comp
      (LVCohnK2.nonUnitalMap (I := I) (LVCohnK2.inlHom R K)) = MonoidHom.id _ := by
    refine PresentedGroup.ext ?_
    rintro ⟨i, j, hij, a⟩
    change ringMap (RingHom.fst R K) (LVCohnK2.nonUnitalMap (LVCohnK2.inlHom R K) (x i j hij a)) =
      x i j hij a
    exact (congrArg (ringMap (RingHom.fst R K)) (LVCohnK2.nonUnitalMap_x _ i j hij a)).trans
      (ringMap_x _ i j hij _)
  exact DFunLike.congr_fun hh u

/-- `snd ∘ inl = 1` on Steinberg groups.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf
T1b.iii.) -/
theorem ringMap_snd_nonUnitalMap_inl (u : SteinbergGroup I R) :
    ringMap (RingHom.snd R K) (LVCohnK2.nonUnitalMap (LVCohnK2.inlHom R K) u) = 1 := by
  have hh : (ringMap (I := I) (RingHom.snd R K)).comp
      (LVCohnK2.nonUnitalMap (I := I) (LVCohnK2.inlHom R K)) = 1 := by
    refine PresentedGroup.ext ?_
    rintro ⟨i, j, hij, a⟩
    change ringMap (RingHom.snd R K) (LVCohnK2.nonUnitalMap (LVCohnK2.inlHom R K) (x i j hij a)) =
      1
    exact (congrArg (ringMap (RingHom.snd R K)) (LVCohnK2.nonUnitalMap_x _ i j hij a)).trans
      ((ringMap_x _ i j hij _).trans (x_zero (R := K) i j hij))
  exact DFunLike.congr_fun hh u

end Coordinates

section Range

variable {I : Type*} [Fintype I] [DecidableEq I] {A B : Type*} [Ring A] [Ring B]

/-- Along an injective ring map `f`, the Steinberg group of the source maps injectively to the
Steinberg group of the range (the corestriction is a ring isomorphism).
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem eq_one_of_ringMap_rangeRestrict_eq_one (f : A →+* B) (hf : Function.Injective f)
    (y : SteinbergGroup I A) (hy : ringMap (I := I) f.rangeRestrict y = 1) : y = 1 := by
  have hinv : ((RingEquiv.ofBijective f.rangeRestrict
      ⟨fun a b hab => hf (congrArg Subtype.val hab), f.rangeRestrict_surjective⟩).symm :
        f.range →+* A).comp f.rangeRestrict = RingHom.id A :=
    RingHom.ext fun c => RingEquiv.symm_apply_apply _ c
  have h2 := congrArg (ringMap (I := I) ((RingEquiv.ofBijective f.rangeRestrict
      ⟨fun a b hab => hf (congrArg Subtype.val hab), f.rangeRestrict_surjective⟩).symm :
        f.range →+* A)) hy
  rw [map_one, LVCohnK2.ringMap_ringMap, hinv, LVCohnK2.ringMap_id_apply] at h2
  exact h2

end Range

section Cohn

open LVCohnRelK1

/-- The corner shift `a ↦ x^M a y^M` on `C_2(𝔽₂)`.  (`yaoseq6.tex` thm:skewyao Step 3;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def cohnShiftPow (m : ℕ) : CohnTwoF2 →ₙ+* CohnTwoF2 :=
  cornerShift (cx false ^ m) (cy false ^ m) (cy_pow_mul_cx_pow m)

/-- `cohnShiftPow` on elements.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem cohnShiftPow_apply (m : ℕ) (a : CohnTwoF2) :
    cohnShiftPow m a = cx false ^ m * a * cy false ^ m :=
  rfl

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- `fst ∘ θ_M ∘ inl` is the corner shift `a ↦ x^M a y^M` on Steinberg groups.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem ringMap_fst_cohnTheta_inl (m : ℕ) (u : SteinbergGroup I CohnTwoF2) :
    ringMap (RingHom.fst CohnTwoF2 (ZMod 2)) (ringMap (cohnTheta m)
      (LVCohnK2.nonUnitalMap (LVCohnK2.inlHom CohnTwoF2 (ZMod 2)) u)) =
      LVCohnK2.nonUnitalMap (cohnShiftPow m) u := by
  have hh : ((ringMap (I := I) (RingHom.fst CohnTwoF2 (ZMod 2))).comp
      (ringMap (I := I) (cohnTheta m))).comp
        (LVCohnK2.nonUnitalMap (I := I) (LVCohnK2.inlHom CohnTwoF2 (ZMod 2))) =
      LVCohnK2.nonUnitalMap (I := I) (cohnShiftPow m) := by
    refine PresentedGroup.ext ?_
    rintro ⟨i, j, hij, a⟩
    change ringMap (RingHom.fst CohnTwoF2 (ZMod 2)) (ringMap (cohnTheta m)
      (LVCohnK2.nonUnitalMap (LVCohnK2.inlHom CohnTwoF2 (ZMod 2)) (x i j hij a))) =
        LVCohnK2.nonUnitalMap (cohnShiftPow m) (x i j hij a)
    rw [LVCohnK2.nonUnitalMap_x, ringMap_x, ringMap_x, LVCohnK2.nonUnitalMap_x]
    exact congrArg (fun c => x i j hij (RingHom.fst CohnTwoF2 (ZMod 2) c)) (cohnTheta_inl m a)
  exact DFunLike.congr_fun hh u

end Cohn

section Descent

open LVCohnRelK1

variable {D : Type*} [Ring D]

/-- Let `ι_M : C × 𝔽₂ → D` be injective ring maps with `ι_M ∘ θ_M = ι_0` whose ranges exhaust
`D`.  An element of `St_I(C × 𝔽₂)` dying in `St_I(D)` already dies under some `θ_M`.
(Continuity of `K₂` along the direct limit in ABC 2009, proof of Thm 3.6; `yaoseq6.tex`
thm:skewyao Step 3; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem exists_cohnTheta_eq_one {ι : ℕ → (CohnTwoF2 × ZMod 2 →+* D)}
    (hinj : ∀ M, Function.Injective (ι M))
    (hunion : ∀ s : Finset D, ∃ M, (s : Set D) ⊆ ((ι M).range : Set D))
    (hcompat : ∀ M, (ι M).comp (cohnTheta M) = ι 0)
    {I : Type*} [Fintype I] [DecidableEq I] (y : SteinbergGroup I (CohnTwoF2 × ZMod 2))
    (hy : ringMap (ι 0) y = 1) : ∃ M, ringMap (cohnTheta M) y = 1 := by
  have hle : ∀ M, (ι 0).range ≤ (ι M).range := by
    intro M d hd
    obtain ⟨c, rfl⟩ := RingHom.mem_range.mp hd
    exact RingHom.mem_range.mpr ⟨cohnTheta M c, DFunLike.congr_fun (hcompat M) c⟩
  have hsub : ((ι 0).range.subtype).comp (ι 0).rangeRestrict = ι 0 :=
    RingHom.ext fun _ => rfl
  obtain ⟨s, hs⟩ := exists_finset_of_ringMap_eq_one I (ι 0).range
    (ringMap (ι 0).rangeRestrict y)
    ((LVCohnK2.ringMap_ringMap (ι 0).rangeRestrict (ι 0).range.subtype y).trans
      ((congrArg (fun g : CohnTwoF2 × ZMod 2 →+* D => ringMap (I := I) g y) hsub).trans hy))
  obtain ⟨M, hM⟩ := hunion s
  have h1 := hs (ι M).range (hle M) hM
  have hcomp : (Subring.inclusion (hle M)).comp (ι 0).rangeRestrict =
      (ι M).rangeRestrict.comp (cohnTheta M) :=
    RingHom.ext fun c => Subtype.ext (DFunLike.congr_fun (hcompat M) c).symm
  refine ⟨M, eq_one_of_ringMap_rangeRestrict_eq_one (ι M) (hinj M) _ ?_⟩
  exact (LVCohnK2.ringMap_ringMap (cohnTheta M) (ι M).rangeRestrict y).trans
    ((congrArg (fun g : CohnTwoF2 × ZMod 2 →+* (ι M).range => ringMap (I := I) g y)
      hcomp.symm).trans
      ((LVCohnK2.ringMap_ringMap (ι 0).rangeRestrict (Subring.inclusion (hle M)) y).symm.trans
        h1))

/-- Descent to a corner shift: if the direct limit `D` of the corner shifts `θ_M` has stable
`K₂ = 0`, then every `k ∈ K₂(n, C)` is killed, after padding, by some corner shift
`a ↦ x^M a y^M`.  (ABC 2009, proof of Thm 3.6; `yaoseq6.tex` thm:skewyao Step 3;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem cohnShiftPow_descent (hD : LVH2GL3.StableK2Trivial D)
    {ι : ℕ → (CohnTwoF2 × ZMod 2 →+* D)} (hinj : ∀ M, Function.Injective (ι M))
    (hunion : ∀ s : Finset D, ∃ M, (s : Set D) ⊆ ((ι M).range : Set D))
    (hcompat : ∀ M, (ι M).comp (cohnTheta M) = ι 0)
    (n : ℕ) (k : SteinbergGroup (Fin n) CohnTwoF2) (hk : projection k = 1) :
    ∃ (M N : ℕ) (h : n ≤ N),
      indexMap (Fin.castLEEmb h) (LVCohnK2.nonUnitalMap (cohnShiftPow M) k) = 1 := by
  have hκ : projection (LVCohnK2.nonUnitalMap (LVCohnK2.inlHom CohnTwoF2 (ZMod 2)) k) = 1 :=
    projection_eq_one_of_fst_snd _ (by rw [ringMap_fst_nonUnitalMap_inl, hk])
      (by rw [ringMap_snd_nonUnitalMap_inl, map_one])
  have hκD : projection
      (ringMap (ι 0) (LVCohnK2.nonUnitalMap (LVCohnK2.inlHom CohnTwoF2 (ZMod 2)) k)) = 1 := by
    rw [LVCohnK2.projection_ringMap, hκ, map_one]
  obtain ⟨N, hN, hκN⟩ := hD n _ hκD
  rw [LVStableK2.indexMap_ringMap] at hκN
  obtain ⟨M, hM⟩ := exists_cohnTheta_eq_one hinj hunion hcompat _ hκN
  refine ⟨M, N, hN, ?_⟩
  have h2 := congrArg (ringMap (I := Fin N) (RingHom.fst CohnTwoF2 (ZMod 2))) hM
  rw [map_one, ← LVStableK2.indexMap_ringMap, ← LVStableK2.indexMap_ringMap,
    ringMap_fst_cohnTheta_inl] at h2
  exact h2

end Descent

end

end GroupApproximation.Full.LVCohnColimit

import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyDegGen
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyFieldSlice
import GroupApproximation.BooneHigman.Metabelian.ElemFPFieldK2BruhatBigCellSpans
import GroupApproximation.Meta.AxiomGuard

/-!
# Degree reduction for `K₂(F_p[X])`, part 6: the amalgam residual and the wiring

Lane `bh-met-91c`.  Notation of `ElemFPK2PolyDegSpans`; bars denote images under
`projection : St_I(F_p[X]) → E_I(F_p[X])`.

* `k2PolyDeg_AmalgamStatement` (**the residual**): the matrix group `Ḡ = E_{K'}(F_p[X])` is the
  amalgamated product of the constants `Ā = E_{K'}(F_p)` and the parabolic `P̄` along their
  intersection.  It is stated by its universal property, for homomorphisms into any group.
* `k2PolyDeg_step`: the residual, the constants lemma and `S ∩ K₂ = 1` give `G ∩ K₂ = 1`.
* `k2PolyDeg_S_eq_one_of_amalgam`: by induction on `K`, `S_K ∩ K₂ = 1` for every `K`.
* Endpoints: `k2PolyDeg_K2_eq_bot_of_amalgam` (`K₂(N, F_p[X]) = ⊥` for `N ≥ 5`),
  `k2PolyDeg_const_of_amalgam` (the `k2PolyField_ConstStatement` for `F_p`, `N ≥ 5`) and
  `k2PolyDeg_level_zero_of_amalgam` (`nk2Slice_LevelStatement (ZMod p) 0` for every prime `p`).

**LOUD: REFUTED.**  `k2PolyDeg_AmalgamStatement` is FALSE whenever `|K| ≥ 2`
(`k2PolyAmal_not_amalgamStatement`, `ElemFPK2PolyAmalRefute.lean`, lane `bh-met-91r`); the
Soulé "amalgam" reading below is wrong for `|K'| ≥ 3`.  The endpoints of this file are vacuous.

**LOUD strength note.**  `k2PolyDeg_AmalgamStatement` is a statement about *matrix groups only*:
it never mentions `K₂` or the Steinberg group, since `H` is arbitrary and `Ā, P̄, Ḡ` are
subgroups of `E_I(F_p[X]) ≤ GL_I(F_p[X])`.  It is **not** an equivalent restatement of the target,
and it is **not** proved to be logically weaker: its relation to `K₂(F_p[X]) = K₂(F_p)` is
incomparable as far as this file knows.  It is smaller in proof content: all the Steinberg-side
work (the kernel lemma, the constants lemma, the section argument and the induction) is proved
here.  It is not on the lane's forbidden list, as it is not homotopy invariance of `K₂` and
not a citation used as a hypothesis.

**Truth check (paper).**  Order `K'` with `L` last and let `B` be the lower-triangular Borel
subgroup, so `B ≤ P`, because `P̄` is the stabilizer of the line through `e_L`.  Nagao (`|K'| = 2`)
and Soulé (*Chevalley groups over polynomial rings*, 1979; `|K'| ≥ 3`) give
`SL_{K'}(k[t]) = SL_{K'}(k) *_{B(k)} B(k[t])`, and `SL_{K'}(k[t]) = E_{K'}(k[t])` for the
Euclidean ring `k[t]`.  Moreover `P̄ = ⟨P(k), B(k[t])⟩`.  To see this, note that the unipotent
radical `x_Lj(f)` (`j ∈ K`) is lower triangular, and an upper root `x_ij(f)` with `i, j ∈ K` is
`w x_ji(-f) w⁻¹` with `w ∈ E_K(k) ≤ P(k)`.  So given `φ₁` on `Ā` and `φ₂` on `P̄` that agree on
`Ā ∩ P̄`, Soulé extends `(φ₁, φ₂|B(k[t]))` to `Φ` on `Ḡ`.  Then `Φ = φ₂` on the generators
`P(k) ⊆ Ā ∩ P̄` and `B(k[t])` of `P̄`, hence on all of `P̄`.  The cases used have `m ∈ K` and
`L ∉ K`, so `|K'| ≥ 2`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan
  rootSpan_induction rootSpan_mono mem_rootSpan_true)

/-- **The residual.**  `E_{K'}(F_p[X])` is the amalgam of the constants `E_{K'}(F_p)` and the
parabolic `P̄` over their intersection.  This is a statement about matrix groups only; see the
module docstring for the LOUD strength note and the truth check (Nagao, Soulé). -/
def k2PolyDeg_AmalgamStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {I : Type} [Fintype I] [DecidableEq I] (K : Finset I) (m L n : I)
    (hmL : m ≠ L) (hmn : m ≠ n) (hLn : L ≠ n), L ∉ K → m ∈ K →
    ∀ (H : Type) [Group H] (φ₁ : (k2PolyDeg_A p K L).map projection →* H)
      (φ₂ : (k2PolyDeg_P p K m L n hmL hmn hLn).map projection →* H),
      (∀ (z : elementaryGroup I (Polynomial (ZMod p)))
        (h₁ : z ∈ (k2PolyDeg_A p K L).map projection)
        (h₂ : z ∈ (k2PolyDeg_P p K m L n hmL hmn hLn).map projection),
        φ₁ ⟨z, h₁⟩ = φ₂ ⟨z, h₂⟩) →
      ∃ Φ : (k2PolyDeg_G p K L).map projection →* H,
        (∀ (z : elementaryGroup I (Polynomial (ZMod p)))
          (h₁ : z ∈ (k2PolyDeg_A p K L).map projection)
          (h : z ∈ (k2PolyDeg_G p K L).map projection), Φ ⟨z, h⟩ = φ₁ ⟨z, h₁⟩) ∧
        (∀ (z : elementaryGroup I (Polynomial (ZMod p)))
          (h₂ : z ∈ (k2PolyDeg_P p K m L n hmL hmn hLn).map projection)
          (h : z ∈ (k2PolyDeg_G p K L).map projection), Φ ⟨z, h⟩ = φ₂ ⟨z, h₂⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_AmalgamStatement

section Step

variable {I : Type} [Fintype I] [DecidableEq I] {p : ℕ} [Fact p.Prime]

/-- **The inductive step.**  Given the residual and `C(St_I(F_p)) ∩ K₂ = 1`, `S_K ∩ K₂ = 1`
implies `G_{K ∪ {L}} ∩ K₂ = 1`. -/
theorem k2PolyDeg_step (hAm : k2PolyDeg_AmalgamStatement) {K : Finset I} {m L n : I}
    (hmL : m ≠ L) (hmn : m ≠ n) (hLn : L ≠ n) (hLK : L ∉ K) (hmK : m ∈ K)
    (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    (hC : ∀ g ∈ (ringMap (I := I) (Polynomial.C : ZMod p →+* Polynomial (ZMod p))).range,
      g ∈ K2 I (Polynomial (ZMod p)) → g = 1)
    (ih : ∀ s ∈ k2PolyDeg_S p K, s ∈ K2 I (Polynomial (ZMod p)) → s = 1)
    {g : SteinbergGroup I (Polynomial (ZMod p))} (hg : g ∈ k2PolyDeg_G p K L)
    (hK2 : g ∈ K2 I (Polynomial (ZMod p))) : g = 1 := by
  have hPK : ∀ z ∈ k2PolyDeg_P p K m L n hmL hmn hLn, z ∈ K2 I (Polynomial (ZMod p)) → z = 1 :=
    fun z hz hzK => k2PolyDeg_eq_one_of_mem_P hmL hmn hLn hLK ih hz hzK
  have hP : ∀ z ∈ k2PolyDeg_P p K m L n hmL hmn hLn, projection z = 1 → z = 1 :=
    fun z hz h1 => hPK z hz ((mem_K2_iff z).mpr h1)
  have hAC : ∀ z ∈ k2PolyDeg_A p K L,
      z ∈ (ringMap (I := I) (Polynomial.C : ZMod p →+* Polynomial (ZMod p))).range := by
    intro z hz
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hz
    exact MonoidHom.mem_range.mpr ⟨y, rfl⟩
  have hA : ∀ z ∈ k2PolyDeg_A p K L, projection z = 1 → z = 1 :=
    fun z hz h1 => hC z (hAC z hz) ((mem_K2_iff z).mpr h1)
  have hcompat : ∀ (z : elementaryGroup I (Polynomial (ZMod p)))
      (h₁ : z ∈ (k2PolyDeg_A p K L).map projection)
      (h₂ : z ∈ (k2PolyDeg_P p K m L n hmL hmn hLn).map projection),
      k2PolyDeg_inv projection _ hA ⟨z, h₁⟩ = k2PolyDeg_inv projection _ hP ⟨z, h₂⟩ := by
    intro z h₁ h₂
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp h₁
    obtain ⟨b, hb, hab⟩ := Subgroup.mem_map.mp h₂
    rw [k2PolyDeg_inv_apply projection _ hA ha h₁ rfl,
      k2PolyDeg_inv_apply projection _ hP hb h₂ hab]
    exact k2PolyDeg_eq_of_const_of_mem_P hmL hmn hLn hC hPK (hAC a ha) hb hab.symm
  obtain ⟨Φ, hΦ₁, hΦ₂⟩ := hAm p K m L n hmL hmn hLn hLK hmK
    (SteinbergGroup I (Polynomial (ZMod p))) (k2PolyDeg_inv projection _ hA)
    (k2PolyDeg_inv projection _ hP) hcompat
  refine k2PolyDeg_eq_one_of_extension hmL hmn hLn hthird Φ (fun z hz hzG => ?_)
    (fun z hz hzG => ?_) hg hK2
  · exact (hΦ₁ _ (Subgroup.mem_map_of_mem projection hz) hzG).trans
      (k2PolyDeg_inv_apply projection _ hA hz _ rfl)
  · exact (hΦ₂ _ (Subgroup.mem_map_of_mem projection hz) hzG).trans
      (k2PolyDeg_inv_apply projection _ hP hz _ rfl)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_step

/-- **The induction.**  Given the residual and `C(St_I(F_p)) ∩ K₂ = 1` (with `|I| ≥ 3`),
`S_K ∩ K₂ = 1` for every finset `K`. -/
theorem k2PolyDeg_S_eq_one_of_amalgam (hAm : k2PolyDeg_AmalgamStatement)
    (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    (hC : ∀ g ∈ (ringMap (I := I) (Polynomial.C : ZMod p →+* Polynomial (ZMod p))).range,
      g ∈ K2 I (Polynomial (ZMod p)) → g = 1) (K : Finset I) :
    ∀ s ∈ k2PolyDeg_S p K, s ∈ K2 I (Polynomial (ZMod p)) → s = 1 := by
  induction K using Finset.induction_on with
  | empty =>
    intro s hs _
    exact rootSpan_induction (p := fun i j => i ∈ (∅ : Finset I) ∧ j ∈ (∅ : Finset I))
      (Q := fun z => z = 1)
      (fun i j _ _ (hq : i ∈ (∅ : Finset I) ∧ j ∈ (∅ : Finset I)) =>
        absurd hq.1 (Finset.notMem_empty i)) rfl
      (fun g k _ _ h1 h2 => show g * k = 1 by
        rw [show g = 1 from h1, show k = 1 from h2, one_mul]) hs
  | insert L K hLK ih =>
    intro s hs hK2
    rcases Finset.eq_empty_or_nonempty K with hK0 | ⟨m, hmK⟩
    · subst hK0
      have key : ∀ k : I, k ∈ insert L (∅ : Finset I) → k = L := fun k hk =>
        (Finset.mem_insert.mp hk).resolve_right (Finset.notMem_empty k)
      exact rootSpan_induction
        (p := fun i j => i ∈ insert L (∅ : Finset I) ∧ j ∈ insert L (∅ : Finset I))
        (Q := fun z => z = 1)
        (fun i j hij _ (hq : i ∈ insert L (∅ : Finset I) ∧ j ∈ insert L (∅ : Finset I)) =>
          absurd ((key i hq.1).trans (key j hq.2).symm) hij) rfl
        (fun g k _ _ h1 h2 => show g * k = 1 by
          rw [show g = 1 from h1, show k = 1 from h2, one_mul]) hs
    · have hmL : m ≠ L := fun e => hLK (e ▸ hmK)
      obtain ⟨n, hmn, hLn⟩ := hthird m L
      exact k2PolyDeg_step hAm hmL hmn hLn hLK hmK hthird hC ih hs hK2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_S_eq_one_of_amalgam

end Step

section Endpoints

/-- The residual kills every element of `K₂(N, F_p[X])`, `N ≥ 5`. -/
theorem k2PolyDeg_eq_one_of_amalgam (hAm : k2PolyDeg_AmalgamStatement) {p : ℕ} (hp : p.Prime)
    {N : ℕ} (hN : 5 ≤ N) {g : St N (Polynomial (ZMod p))}
    (hg : g ∈ K2n N (Polynomial (ZMod p))) : g = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hthird : ∀ a b : Fin N, ∃ k, a ≠ k ∧ b ≠ k :=
    FieldK2.bruhatBigCell_third (by rw [Fintype.card_fin]; omega)
  have hS : g ∈ k2PolyDeg_S p (Finset.univ : Finset (Fin N)) :=
    rootSpan_mono (p := fun _ _ : Fin N => True)
      (q := fun i j => i ∈ (Finset.univ : Finset (Fin N)) ∧ j ∈ (Finset.univ : Finset (Fin N)))
      (fun i j _ _ => ⟨Finset.mem_univ i, Finset.mem_univ j⟩) (mem_rootSpan_true g)
  exact k2PolyDeg_S_eq_one_of_amalgam hAm hthird
    (fun z hz hzK => k2PolyField_eq_one_of_mem_range hp hN hzK hz) Finset.univ g hS hg

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_eq_one_of_amalgam

/-- The residual gives `K₂(N, F_p[X]) = ⊥` for `N ≥ 5`. -/
theorem k2PolyDeg_K2_eq_bot_of_amalgam (hAm : k2PolyDeg_AmalgamStatement) {p : ℕ}
    (hp : p.Prime) {N : ℕ} (hN : 5 ≤ N) : K2n N (Polynomial (ZMod p)) = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).mpr fun _ hg => k2PolyDeg_eq_one_of_amalgam hAm hp hN hg

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_K2_eq_bot_of_amalgam

/-- The residual gives `k2PolyField_ConstStatement (ZMod p) N` for every prime `p`, `N ≥ 5`. -/
theorem k2PolyDeg_const_of_amalgam (hAm : k2PolyDeg_AmalgamStatement) :
    ∀ p : ℕ, p.Prime → ∀ N : ℕ, 5 ≤ N → k2PolyField_ConstStatement (ZMod p) N := by
  intro p hp N hN g hg
  rw [k2PolyDeg_eq_one_of_amalgam hAm hp hN hg]
  exact Subgroup.one_mem _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_const_of_amalgam

/-- **Wiring.**  The residual gives `nk2Slice_LevelStatement (ZMod p) 0` for every prime `p`,
through `ElemFPCharZero.k2PolyField_level_zero_of_const`. -/
theorem k2PolyDeg_level_zero_of_amalgam (hAm : k2PolyDeg_AmalgamStatement) :
    ∀ p : ℕ, p.Prime → ElemFPCharZero.nk2Slice_LevelStatement (ZMod p) 0 :=
  ElemFPCharZero.k2PolyField_level_zero_of_const fun p hp =>
    k2PolyDeg_const_of_amalgam hAm p hp 5 le_rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_level_zero_of_amalgam

end Endpoints

end GroupApproximation.BooneHigman.Metabelian.ElemFP

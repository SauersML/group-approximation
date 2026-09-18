import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyDegAmalgam
import GroupApproximation.Meta.AxiomGuard

/-!
# Repairing the degree-reduction route for `K₂(F_p[X])`: the Steinberg-side section residual

Lane `bh-met-91z`.  Notation of `ElemFPK2PolyDegSpans`: `G = G_{K'}(F_p[X])`, `A` the constants,
`P = T ⊔ (S ⊔ V)` the parabolic, all inside `St_I(F_p[X])`; bars are images under `projection`.

The residual `k2PolyDeg_AmalgamStatement` of lane `bh-met-91c` is FALSE for `|K| ≥ 2`
(`k2PolyAmal_not_amalgamStatement`, lane `bh-met-91r`).  Here it is replaced by option (c) of
the lane: the universal property is asked **only** for the two Steinberg-side maps that
`k2PolyDeg_step` actually feeds it (`H = St_I(F_p[X])`, `φ₁, φ₂` the sections of `projection` on
`A` and `P`), and the hypotheses available at that point of the induction are granted.

* `k2PolyRank2_SectionStatement`: the new residual.
* `k2PolyRank2_step`: the residual gives the inductive step `G ∩ K₂ = 1`.
* `k2PolyRank2_section_of_amalgam`: the old (false) residual implies the new one, so the new one
  is formally weaker than the old one.

**Truth check.**  The refutation's obstruction does NOT survive.  It used `H` = the pushout
`Ā *_{Ā ∩ P̄} P̄`, where `x_kL(1) x_Lm(X) x_kL(1)⁻¹ = x_km(X) x_Lm(X)` fails.  Here `H = St_I`,
where it is the Steinberg relation (C1) (`conj_x_left`); checked on matrices over `F_2, F_3`
(scratchpad `bh91z/chk.py`).  The residual is TRUE, because `K₂(N, F_p[X]) = 0` for `N ≥ 5` is a
true theorem: given it, `projection` is injective on `G`, and its inverse is the required `Φ`.

**LOUD: ONLY EQUIVALENT.**  Under the hypotheses it grants (`S ∩ K₂ = 1`, constants `∩ K₂ = 1`,
a third index), the residual is *equivalent* to the conclusion `G ∩ K₂ = 1` of the inductive
step.  One direction is `k2PolyRank2_step`.  Conversely, if `G ∩ K₂ = 1`, then
`k2PolyDeg_inv projection G _` is a `Φ` as required, because `A, P ≤ G`.  Hence, quantified over
all `K`, the residual is equivalent to `K₂(N, F_p[X]) = ⊥` (`N ≥ 5`).  It is **not** a genuine
reduction in logical strength.  What it isolates is the part of the proof content that is not
yet in Lean: the Steinberg-side kernel lemma, the constants lemma, the extension theorem, the
induction and the wiring are all proved (lane `bh-met-91c` and `k2PolyRank2_step`).

**Why no strictly smaller true residual was found (paper analysis).**
* (b) A colimit over `Ā` and the line stabilisers `P̄^{(l)}`, `l ∈ K'` (or all conjugates
  `a P̄ a⁻¹`, `a ∈ Ā`) collapses to the same statement.  For `|K'| ≥ 3` every Steinberg relation
  of `St_{K'}` has at most two column indices, so it lives in some `P^{(l)}` (checked
  combinatorially in `chk.py`).  The colimit is then `St_{K'}` modulo `K₂`-parts of the pieces,
  which are trivial by induction, so "`Ḡ` is the colimit" is again `G ∩ K₂ = 1`.
* (a) The rank-2 amalgam (`|K| = 1`) is true: reduced words in `SL₂(F_2) *_{B(F_2)} B(F_2[X])`
  with degrees `≤ 2` and length `≤ 3` were checked to be non-constant in `chk.py`.  But the step
  for `|K| ≥ 2` cannot be reduced to rank-2 pieces by a Curtis–Tits argument: rank-2 pieces
  carry no information about `K₂` elements that are products across different pieces.  A
  genuinely smaller matrix-side input must be a presentation whose pieces have *constant* Levi
  and degree-bounded unipotent radicals (a colimit over the vertex stabilisers of a sector).
  That statement is stronger than needed, and it is a citation (Soulé), which the lane forbids.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic

/-- **The new residual** (option (c)).  At the inductive step, with `S ∩ K₂ = 1` and
`C(St_I(F_p)) ∩ K₂ = 1` granted, some homomorphism `Φ : Ḡ → St_I(F_p[X])` sends `π z` back to
`z` for every `z` in the constants `A` and every `z ∈ P`.  LOUD: under these hypotheses it is
equivalent to `G ∩ K₂ = 1`; see the module docstring. -/
def k2PolyRank2_SectionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {I : Type} [Fintype I] [DecidableEq I] (K : Finset I) (m L n : I)
    (hmL : m ≠ L) (hmn : m ≠ n) (hLn : L ≠ n), L ∉ K → m ∈ K →
    (∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k) →
    (∀ g ∈ (ringMap (I := I) (Polynomial.C : ZMod p →+* Polynomial (ZMod p))).range,
      g ∈ K2 I (Polynomial (ZMod p)) → g = 1) →
    (∀ s ∈ k2PolyDeg_S p K, s ∈ K2 I (Polynomial (ZMod p)) → s = 1) →
    ∃ Φ : (k2PolyDeg_G p K L).map projection →* SteinbergGroup I (Polynomial (ZMod p)),
      (∀ z ∈ k2PolyDeg_A p K L, ∀ hz : projection z ∈ (k2PolyDeg_G p K L).map projection,
        Φ ⟨projection z, hz⟩ = z) ∧
      (∀ z ∈ k2PolyDeg_P p K m L n hmL hmn hLn,
        ∀ hz : projection z ∈ (k2PolyDeg_G p K L).map projection, Φ ⟨projection z, hz⟩ = z)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyRank2_SectionStatement

section Step

variable {I : Type} [Fintype I] [DecidableEq I] {p : ℕ} [Fact p.Prime]

/-- **The inductive step from the new residual.**  `S_K ∩ K₂ = 1` and the constants lemma give
`G_{K ∪ {L}} ∩ K₂ = 1`. -/
theorem k2PolyRank2_step (hSec : k2PolyRank2_SectionStatement) {K : Finset I} {m L n : I}
    (hmL : m ≠ L) (hmn : m ≠ n) (hLn : L ≠ n) (hLK : L ∉ K) (hmK : m ∈ K)
    (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    (hC : ∀ g ∈ (ringMap (I := I) (Polynomial.C : ZMod p →+* Polynomial (ZMod p))).range,
      g ∈ K2 I (Polynomial (ZMod p)) → g = 1)
    (ih : ∀ s ∈ k2PolyDeg_S p K, s ∈ K2 I (Polynomial (ZMod p)) → s = 1)
    {g : SteinbergGroup I (Polynomial (ZMod p))} (hg : g ∈ k2PolyDeg_G p K L)
    (hK2 : g ∈ K2 I (Polynomial (ZMod p))) : g = 1 := by
  obtain ⟨Φ, hΦA, hΦP⟩ := hSec p K m L n hmL hmn hLn hLK hmK hthird hC ih
  exact k2PolyDeg_eq_one_of_extension hmL hmn hLn hthird Φ hΦA hΦP hg hK2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyRank2_step

end Step

/-- The old (false) amalgam residual implies the new one: the new residual is the special case
`H = St_I(F_p[X])`, `φ₁, φ₂` = the sections, of the old universal property. -/
theorem k2PolyRank2_section_of_amalgam (hAm : k2PolyDeg_AmalgamStatement) :
    k2PolyRank2_SectionStatement := by
  intro p _ I _ _ K m L n hmL hmn hLn hLK hmK _ hC ih
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
  refine ⟨Φ, fun z hz hzG => ?_, fun z hz hzG => ?_⟩
  · exact (hΦ₁ _ (Subgroup.mem_map_of_mem projection hz) hzG).trans
      (k2PolyDeg_inv_apply projection _ hA hz _ rfl)
  · exact (hΦ₂ _ (Subgroup.mem_map_of_mem projection hz) hzG).trans
      (k2PolyDeg_inv_apply projection _ hP hz _ rfl)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyRank2_section_of_amalgam

end GroupApproximation.BooneHigman.Metabelian.ElemFP

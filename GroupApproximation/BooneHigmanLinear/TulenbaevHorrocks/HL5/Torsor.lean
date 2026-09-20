import GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Local
import GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.Hom
import GroupApproximation.Meta.AxiomGuard

/-!
# H.L5: the set `V̄_T` and the one-sided core from the torsor action (lane k2-hl25b)

A. Lavrenov, S. Sinchuk, *A Horrocks-type theorem for even orthogonal K₂*, Doc. Math. 25 (2020),
arXiv:1909.02637, §§5.4–5.5 (Def 5.32, Prop 5.39, Lemma 5.41, Thm 3), which restates
M. S. Tulenbaev, *The Steinberg group of a polynomial ring*, Math. USSR Sb. 45 (1983), Prop 4.3.

Let `A` be a local ring with maximal ideal `𝔪`, `R = A[T, T⁻¹]` and `B = A[T⁻¹] + 𝔪[T] ⊆ R`
(`Graded.horrB 𝔪`, the same ring as `HL1.horrBm`).  As everywhere in `TulenbaevHorrocks`, the
ring `A[X⁻¹]` is modelled by `A[X]` read through `toLaurentNeg` (`X ↦ T⁻¹`).

* `gBar`: `Ḡ^{≥0}_M`, the image in `St_N(R)` of the elements of `St_N(A[X])` trivial modulo `𝔪`
  (these form `St̄(A[X], 𝔪[X])`).  `gZero`: `G⁰_M = St̄(A, 𝔪)`, the elements of `St_N(A)` trivial
  modulo `𝔪`.  `unitsOneAddM`: `(1 + 𝔪)ˣ`.
* `VbarT`: L–S (5.15), the triples `Ḡ^{≥0}_M × St_N(A[X⁻¹]) × (1 + 𝔪)ˣ` modulo
  `(p · j₊i₊(γ), h, u) ∼ (p, i₋(γ) · h, u)` for `γ ∈ G⁰_M`.
* `TorsorAction`: an action of `St_N(B)` on `V̄_T` with L–S Prop 5.39(1).  Building it is L–S
  (5.16)–(5.19), Lemmas 5.33–5.38 over H.L4's `P_α`, `S_α`, and Prop 5.39 through pal-q111's H.L2
  interface (lane pal-q111, `HL5Act/`).
* `Lemma541 T`: L–S Lemma 5.41 for the action `T`, stated for every preimage `b` of
  `p₁ ∈ Ḡ^{≥0}_M` under `j_R : St_N(B) → St_N(R)`.  In this form it needs `j_R` injective, i.e.
  H.L1 (`HL1.StHorrBInjAt`, k2-vdk).  `TorsorActionAt := ∃ T, Lemma541 T`.
* `stLocalOneSidedAt_of_torsorAction`: the first half of L–S Thm 3, giving pal-q111's
  `StLocalOneSidedAt`.  If `α ≡ 1 (mod 𝔪)` and `j₊α = j₋β`, then `b = j_B⁻(β)⁻¹` is a preimage of
  `p₁ = j₊(α)⁻¹ ∈ Ḡ^{≥0}_M`, so `[p₁, β, 1] = b · j_B⁻(β) · [1, 1, 1] = [1, 1, 1]` and `β = i₋(γ)`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GroupApproximation
namespace BooneHigmanLinear
namespace TulenbaevHorrocks
namespace HL5

open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic Polynomial
open GroupApproximation.BooneHigmanLinear.Tulenbaev

section Ring

variable (A : Type) [CommRing A] [IsLocalRing A]

/-- `B = A[T⁻¹] + 𝔪[T] ⊆ A[T, T⁻¹]` (the same ring as `HL1.horrBm`). -/
abbrev horrBm : Subring (LaurentPolynomial A) :=
  Graded.horrB (IsLocalRing.maximalIdeal A)

theorem C_mem_horrBm (a : A) : LaurentPolynomial.C a ∈ horrBm A := by
  show AddMonoidAlgebra.single (0 : ℤ) a ∈ horrBm A
  exact Graded.single_mem_horrB (Graded.allowed_of_nonneg (by omega) a)

#audit_axioms C_mem_horrBm

theorem T_neg_one_mem_horrBm : (LaurentPolynomial.T (-1) : LaurentPolynomial A) ∈ horrBm A := by
  show AddMonoidAlgebra.single (-1 : ℤ) (1 : A) ∈ horrBm A
  exact Graded.single_mem_horrB (Graded.allowed_of_nonneg (by omega) (1 : A))

#audit_axioms T_neg_one_mem_horrBm

/-- `A[X] → B`, `X ↦ T⁻¹`: Tulenbaev's `A[X⁻¹] → B`. -/
noncomputable def negToB : A[X] →+* horrBm A :=
  Polynomial.eval₂RingHom
    ((LaurentPolynomial.C : A →+* LaurentPolynomial A).codRestrict (horrBm A) (C_mem_horrBm A))
    ⟨LaurentPolynomial.T (-1), T_neg_one_mem_horrBm A⟩

theorem subtype_comp_negToB : (horrBm A).subtype.comp (negToB A) = toLaurentNeg A := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [negToB, toLaurentNeg]
  · simp [negToB, toLaurentNeg]

#audit_axioms subtype_comp_negToB

end Ring

section Torsor

variable (A : Type) [CommRing A] [IsLocalRing A] (N : ℕ)

/-- `j_R ∘ j_B⁻ = j₋`: the map `St_N(A[X⁻¹]) → St_N(B) → St_N(R)` is `toLaurentNeg`. -/
theorem ringMap_subtype_negToB (β : SteinbergGroup (Fin N) A[X]) :
    ringMap (horrBm A).subtype (ringMap (negToB A) β) = ringMap (toLaurentNeg A) β := by
  rw [ringMap_ringMap, subtype_comp_negToB]

#audit_axioms ringMap_subtype_negToB

/-- **`Ḡ^{≥0}_M`** (L–S Def 5.32): the image in `St_N(A[T, T⁻¹])` of the elements of `St_N(A[X])`
that are trivial modulo `𝔪`. -/
def gBar : Subgroup (SteinbergGroup (Fin N) (LaurentPolynomial A)) :=
  (ringMap (I := Fin N) (resPoly A)).ker.map (ringMap (toLaurentPos A))

/-- **`G⁰_M = St̄(A, 𝔪)`** (L–S Def 5.32): the elements of `St_N(A)` trivial modulo `𝔪`. -/
def gZero : Subgroup (SteinbergGroup (Fin N) A) :=
  (ringMap (I := Fin N) (IsLocalRing.residue A)).ker

/-- **`(1 + 𝔪)ˣ`**: the units of `A` that are `1` modulo `𝔪`. -/
def unitsOneAddM : Subgroup Aˣ :=
  (Units.map (IsLocalRing.residue A).toMonoidHom).ker

/-- The triples `V_T = Ḡ^{≥0}_M × St_N(A[X⁻¹]) × (1 + 𝔪)ˣ` of L–S (5.15). -/
abbrev Triple : Type :=
  gBar A N × SteinbergGroup (Fin N) A[X] × unitsOneAddM A

/-- The relation of L–S (5.15): `(p · j₊i₊(γ), h, u) ∼ (p, i₋(γ) · h, u)` for `γ ∈ G⁰_M`
(here `j₊i₊ = j₋i₋` is the constant map `A → A[T, T⁻¹]`). -/
abbrev Rel (x y : Triple A N) : Prop :=
  x.2.2 = y.2.2 ∧ ∃ γ ∈ gZero A N,
    (y.1 : SteinbergGroup (Fin N) (LaurentPolynomial A)) =
        x.1 * ringMap (LaurentPolynomial.C : A →+* LaurentPolynomial A) γ ∧
      y.2.1 = (ringMap (Polynomial.C : A →+* A[X]) γ)⁻¹ * x.2.1

theorem rel_equivalence : Equivalence (Rel A N) where
  refl x := ⟨rfl, 1, (gZero A N).one_mem, by simp, by simp⟩
  symm := by
    rintro x y ⟨hu, γ, hγ, h1, h2⟩
    refine ⟨hu.symm, γ⁻¹, (gZero A N).inv_mem hγ, ?_, ?_⟩
    · rw [h1, map_inv, mul_inv_cancel_right]
    · rw [h2, map_inv, inv_inv, mul_inv_cancel_left]
  trans := by
    rintro x y z ⟨hu, γ, hγ, h1, h2⟩ ⟨hu', δ, hδ, h1', h2'⟩
    refine ⟨hu.trans hu', γ * δ, (gZero A N).mul_mem hγ hδ, ?_, ?_⟩
    · rw [h1', h1, map_mul, mul_assoc]
    · rw [h2', h2, map_mul, mul_inv_rev, mul_assoc]

#audit_axioms rel_equivalence

/-- The equivalence relation of L–S (5.15). -/
def setoid : Setoid (Triple A N) :=
  ⟨Rel A N, rel_equivalence A N⟩

/-- **`V̄_T`** (L–S (5.15); the set on which Tulenbaev, Prop 4.3, lets `St(B)` act). -/
abbrev VbarT : Type :=
  Quotient (setoid A N)

/-- `[p, h, u] ∈ V̄_T`. -/
def mk (p : gBar A N) (h : SteinbergGroup (Fin N) A[X]) (u : unitsOneAddM A) : VbarT A N :=
  Quotient.mk (setoid A N) (p, h, u)

/-- **The action of `St_N(B)` on `V̄_T`** with L–S Prop 5.39(1) (Tulenbaev Prop 4.3):
`j_B⁻(h₁) · [1, h, u] = [1, h₁ h, u]`.  Built by L–S 5.33–5.39 (lane pal-q111, `HL5Act/`). -/
structure TorsorAction where
  smul : SteinbergGroup (Fin N) (horrBm A) → VbarT A N → VbarT A N
  one_smul : ∀ v, smul 1 v = v
  mul_smul : ∀ b c v, smul (b * c) v = smul b (smul c v)
  smul_negToB : ∀ (h₁ h : SteinbergGroup (Fin N) A[X]) (u : unitsOneAddM A),
    smul (ringMap (negToB A) h₁) (mk A N 1 h u) = mk A N 1 (h₁ * h) u

variable {A N} in
/-- **L–S Lemma 5.41** for an action `T`, at every `b ∈ St_N(B)` with `j_R b ∈ Ḡ^{≥0}_M`:
`b · [p, h, u] = [j_R b · p, h, u]`.  L–S state it for the unique preimage `j_R⁻¹(p₁)`, so this
form needs `j_R` injective (H.L1, `HL1.StHorrBInjAt`). -/
def Lemma541 (T : TorsorAction A N) : Prop :=
  ∀ (b : SteinbergGroup (Fin N) (horrBm A)) (hb : ringMap (horrBm A).subtype b ∈ gBar A N)
    (p : gBar A N) (h : SteinbergGroup (Fin N) A[X]) (u : unitsOneAddM A),
    T.smul b (mk A N p h u) =
      mk A N ⟨ringMap (horrBm A).subtype b * p, (gBar A N).mul_mem hb p.2⟩ h u

/-- **H.L5's output**: an action of `St_N(B)` on `V̄_T` with L–S Prop 5.39(1) and Lemma 5.41. -/
def TorsorActionAt : Prop :=
  ∃ T : TorsorAction A N, Lemma541 T

#audit_axioms TorsorActionAt

/-- **L–S Theorem 3, first half (Tulenbaev Prop 4.3(a))**: the torsor action gives the one-sided
relative core.  If `α ∈ St_N(A[X])` is trivial modulo `𝔪` and `j₊α = j₋β`, then `β ∈ St_N(A)`. -/
theorem stLocalOneSidedAt_of_torsorAction (hT : TorsorActionAt A N) : StLocalOneSidedAt A N := by
  obtain ⟨T, h541⟩ := hT
  intro α β hα hαβ
  have hp₁ : (ringMap (toLaurentPos A) α)⁻¹ ∈ gBar A N :=
    (gBar A N).inv_mem (Subgroup.mem_map.mpr ⟨α, MonoidHom.mem_ker.mpr hα, rfl⟩)
  obtain ⟨b, hbdef⟩ : ∃ b, b = (ringMap (I := Fin N) (negToB A) β)⁻¹ := ⟨_, rfl⟩
  have hjb : ringMap (horrBm A).subtype b = (ringMap (toLaurentPos A) α)⁻¹ := by
    rw [hbdef, map_inv, ringMap_subtype_negToB, hαβ]
  have hb : ringMap (horrBm A).subtype b ∈ gBar A N := by
    rw [hjb]
    exact hp₁
  have key : mk A N ⟨(ringMap (toLaurentPos A) α)⁻¹, hp₁⟩ β 1 = mk A N 1 1 1 := by
    have h1 := h541 b hb 1 β 1
    have h2 := T.smul_negToB β 1 1
    rw [mul_one] at h2
    have hp : (⟨(ringMap (toLaurentPos A) α)⁻¹, hp₁⟩ : gBar A N) =
        ⟨ringMap (horrBm A).subtype b *
            ((1 : gBar A N) : SteinbergGroup (Fin N) (LaurentPolynomial A)),
          (gBar A N).mul_mem hb (1 : gBar A N).2⟩ := by
      apply Subtype.ext
      show (ringMap (toLaurentPos A) α)⁻¹ = ringMap (horrBm A).subtype b *
        ((1 : gBar A N) : SteinbergGroup (Fin N) (LaurentPolynomial A))
      rw [hjb, Subgroup.coe_one, mul_one]
    rw [hp, ← h1, ← h2, ← T.mul_smul, hbdef, inv_mul_cancel, T.one_smul]
  have key' : Quotient.mk (setoid A N)
        ((⟨(ringMap (toLaurentPos A) α)⁻¹, hp₁⟩ : gBar A N), β, (1 : unitsOneAddM A)) =
      Quotient.mk (setoid A N)
        ((1 : gBar A N), (1 : SteinbergGroup (Fin N) A[X]), (1 : unitsOneAddM A)) :=
    key
  obtain ⟨-, γ, -, -, h2⟩ := (Quotient.exact key' : Rel A N _ _)
  have h2' : (1 : SteinbergGroup (Fin N) A[X]) =
      (ringMap (Polynomial.C : A →+* A[X]) γ)⁻¹ * β := h2
  exact MonoidHom.mem_range.mpr ⟨γ, inv_mul_eq_one.mp h2'.symm⟩

#audit_axioms stLocalOneSidedAt_of_torsorAction

/-- The one-sided core at every local ring, ranks `N ≥ n₀`, from the torsor action there. -/
theorem stLocalOneSidedStatementAt_of_torsorAction {n₀ : ℕ}
    (h : ∀ (A : Type) [CommRing A] [IsLocalRing A] (N : ℕ), n₀ ≤ N → TorsorActionAt A N) :
    StLocalOneSidedStatementAt n₀ := by
  intro A _ _ N hN
  exact stLocalOneSidedAt_of_torsorAction A N (h A N hN)

#audit_axioms stLocalOneSidedStatementAt_of_torsorAction

end Torsor

end HL5
end TulenbaevHorrocks
end BooneHigmanLinear
end GroupApproximation

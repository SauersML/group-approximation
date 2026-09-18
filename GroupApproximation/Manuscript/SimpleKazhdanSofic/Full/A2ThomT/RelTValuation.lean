import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2ThomT.RelTSpectral
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2ThomT.RelTSequence

/-!
# Relative property (T): shear data on `F_p[X]²` and the four spectral regions

`simple_kazhdan_sofic_group.tex`, Introduction, tex l.57–59 (table row A2): Thom's Kazhdan group
uses relative property (T) of `(F_p[t,t⁻¹]^3 ⋊ SL_3, F_p[t,t⁻¹]^3)` (A. Thom, Groups Geom. Dyn. 4
(2010), §2.1, Lemma 2.1), proved by Burger's argument (Burger 1991; Shalom 1999; Kassabov 2007, §2).

A `RelTShear G p` is an additive plane `vec : F_p[X]² → G` together with upper and lower shears
`up r`, `low r` acting on it by conjugation as `(a, b) ↦ (a + r b, b)` and `(a, b) ↦ (a, b + r a)`.
For an orthogonal representation, a character `χ` of the plane algebra gives the sequences
`lam χ n = χ(Xⁿ, 0)` and `mu χ n = χ(0, Xⁿ)`, and we define the regions

* `regionA`: `λ` becomes nontrivial strictly before `μ`;
* `regionB`: `λ` and `μ` become nontrivial at the same index;
* `regionC`: `μ` becomes nontrivial strictly before `λ`;
* `regionD`: `λ 0 ≠ 1` or `μ 0 ≠ 1`.

The dual actions of the shears by `X` and by `1` move these regions exactly as in Burger's
argument (`mapsTo_upX`, `mapsTo_lowX`, `mapsTo_up1`, `mapsTo_low1`), and every character nontrivial
at some plane element lies in their union (`mem_regions_of_ne_one`).
-/

namespace GroupApproximation.Full.A2ThomT

open WeakDual MeasureTheory Polynomial
open RepresentedRootPlaneSpectralMeasure

noncomputable section

universe u v

attribute [local instance] RelTPlane.relTPlaneCharacterMeasurableSpace

namespace RelTSeq

variable {α : Type*} [MeasurableSpace α]

theorem measurable_seqVal {f : α → ℕ → ℂ} (hf : ∀ n, Measurable fun a ↦ f a n = 1) (k : ℕ) :
    Measurable fun a ↦ SeqVal (f a) k := by
  apply Measurable.and
  · apply Measurable.forall
    intro n
    exact Measurable.imp measurable_const (hf n)
  · exact (hf k).not

theorem measurable_seqA {f g : α → ℕ → ℂ} (hf : ∀ n, Measurable fun a ↦ f a n = 1)
    (hg : ∀ n, Measurable fun a ↦ g a n = 1) : Measurable fun a ↦ SeqA (f a) (g a) := by
  apply (hf 0).and
  apply (hg 0).and
  apply Measurable.exists
  intro k
  apply (measurable_seqVal hf k).and
  apply Measurable.forall
  intro n
  exact Measurable.imp measurable_const (hg n)

theorem measurable_seqB {f g : α → ℕ → ℂ} (hf : ∀ n, Measurable fun a ↦ f a n = 1)
    (hg : ∀ n, Measurable fun a ↦ g a n = 1) : Measurable fun a ↦ SeqB (f a) (g a) := by
  apply (hf 0).and
  apply (hg 0).and
  apply Measurable.exists
  intro k
  exact (measurable_seqVal hf k).and (measurable_seqVal hg k)

theorem measurable_seqD {f g : α → ℕ → ℂ} (hf : ∀ n, Measurable fun a ↦ f a n = 1)
    (hg : ∀ n, Measurable fun a ↦ g a n = 1) : Measurable fun a ↦ SeqD (f a) (g a) :=
  (hf 0).not.or (hg 0).not

end RelTSeq

namespace RelTPlane

variable {G : Type u} [Group G] {V : Type*} [AddCommGroup V] (Q : RelTPlane G V)

/-- If every plane element is a conjugate of a plane element by `g`, then `g⁻¹` normalizes. -/
theorem normalizes_inv {g : G} (h : ∀ x : V, ∃ y : V, g * Q.vec y * g⁻¹ = Q.vec x) :
    Q.Normalizes g⁻¹ := by
  intro x
  obtain ⟨y, hy⟩ := h x
  refine ⟨y, ?_⟩
  rw [← hy, inv_inv]
  simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

end RelTPlane

/-- Shear data on the plane `F_p[X]²` inside a group. -/
structure RelTShear (G : Type u) [Group G] (p : ℕ) extends
    RelTPlane G (Polynomial (ZMod p) × Polynomial (ZMod p)) where
  /-- The upper shear `(a, b) ↦ (a + r b, b)`. -/
  up : Polynomial (ZMod p) → G
  /-- The lower shear `(a, b) ↦ (a, b + r a)`. -/
  low : Polynomial (ZMod p) → G
  up_conj : ∀ r a b : Polynomial (ZMod p), up r * vec (a, b) * (up r)⁻¹ = vec (a + r * b, b)
  low_conj : ∀ r a b : Polynomial (ZMod p), low r * vec (a, b) * (low r)⁻¹ = vec (a, b + r * a)

namespace RelTShear

variable {G : Type u} [Group G] {p : ℕ} (S : RelTShear G p)

theorem up_normalizes (r : Polynomial (ZMod p)) : S.toRelTPlane.Normalizes (S.up r) := by
  intro x
  obtain ⟨a, b⟩ := x
  exact ⟨(a + r * b, b), S.up_conj r a b⟩

theorem up_inv_normalizes (r : Polynomial (ZMod p)) : S.toRelTPlane.Normalizes (S.up r)⁻¹ := by
  apply S.toRelTPlane.normalizes_inv
  intro x
  obtain ⟨a, b⟩ := x
  refine ⟨(a - r * b, b), ?_⟩
  rw [S.up_conj, sub_add_cancel]

theorem low_normalizes (r : Polynomial (ZMod p)) : S.toRelTPlane.Normalizes (S.low r) := by
  intro x
  obtain ⟨a, b⟩ := x
  exact ⟨(a, b + r * a), S.low_conj r a b⟩

theorem low_inv_normalizes (r : Polynomial (ZMod p)) :
    S.toRelTPlane.Normalizes (S.low r)⁻¹ := by
  apply S.toRelTPlane.normalizes_inv
  intro x
  obtain ⟨a, b⟩ := x
  refine ⟨(a, b - r * a), ?_⟩
  rw [S.low_conj, sub_add_cancel]

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (rho : G →* (E ≃ₗᵢ[ℝ] E))

/-- The dual action of the upper shear by `r`. -/
def dualUp (r : Polynomial (ZMod p)) :
    characterSpace ℂ (S.toRelTPlane.represented rho).algebra ≃ᵐ
      characterSpace ℂ (S.toRelTPlane.represented rho).algebra :=
  S.toRelTPlane.dual rho (S.up r) (S.up_normalizes r) (S.up_inv_normalizes r)

/-- The dual action of the lower shear by `r`. -/
def dualLow (r : Polynomial (ZMod p)) :
    characterSpace ℂ (S.toRelTPlane.represented rho).algebra ≃ᵐ
      characterSpace ℂ (S.toRelTPlane.represented rho).algebra :=
  S.toRelTPlane.dual rho (S.low r) (S.low_normalizes r) (S.low_inv_normalizes r)

theorem dualUp_coordinate (r a b : Polynomial (ZMod p))
    (chi : characterSpace ℂ (S.toRelTPlane.represented rho).algebra) :
    S.dualUp rho r chi ((S.toRelTPlane.represented rho).coordinate (a, b)) =
      chi ((S.toRelTPlane.represented rho).coordinate (a + r * b, b)) :=
  S.toRelTPlane.dual_coordinate rho (S.up r) (S.up_normalizes r) (S.up_inv_normalizes r)
    (a, b) (a + r * b, b) (S.up_conj r a b) chi

theorem dualLow_coordinate (r a b : Polynomial (ZMod p))
    (chi : characterSpace ℂ (S.toRelTPlane.represented rho).algebra) :
    S.dualLow rho r chi ((S.toRelTPlane.represented rho).coordinate (a, b)) =
      chi ((S.toRelTPlane.represented rho).coordinate (a, b + r * a)) :=
  S.toRelTPlane.dual_coordinate rho (S.low r) (S.low_normalizes r) (S.low_inv_normalizes r)
    (a, b) (a, b + r * a) (S.low_conj r a b) chi

theorem chi_coordinate_mk (chi : characterSpace ℂ (S.toRelTPlane.represented rho).algebra)
    (a b : Polynomial (ZMod p)) :
    chi ((S.toRelTPlane.represented rho).coordinate (a, b)) =
      chi ((S.toRelTPlane.represented rho).coordinate (a, 0)) *
        chi ((S.toRelTPlane.represented rho).coordinate (0, b)) := by
  rw [← S.toRelTPlane.chi_coordinate_add rho chi, Prod.mk_add_mk, add_zero, zero_add]

theorem chi_coordinate_add_fst (chi : characterSpace ℂ (S.toRelTPlane.represented rho).algebra)
    (a b : Polynomial (ZMod p)) :
    chi ((S.toRelTPlane.represented rho).coordinate (a + b, 0)) =
      chi ((S.toRelTPlane.represented rho).coordinate (a, 0)) *
        chi ((S.toRelTPlane.represented rho).coordinate (b, 0)) := by
  rw [← S.toRelTPlane.chi_coordinate_add rho chi, Prod.mk_add_mk, add_zero]

theorem chi_coordinate_add_snd (chi : characterSpace ℂ (S.toRelTPlane.represented rho).algebra)
    (a b : Polynomial (ZMod p)) :
    chi ((S.toRelTPlane.represented rho).coordinate (0, a + b)) =
      chi ((S.toRelTPlane.represented rho).coordinate (0, a)) *
        chi ((S.toRelTPlane.represented rho).coordinate (0, b)) := by
  rw [← S.toRelTPlane.chi_coordinate_add rho chi, Prod.mk_add_mk, add_zero]

/-- The first valuation sequence `λ n = χ(Xⁿ, 0)`. -/
def lam (chi : characterSpace ℂ (S.toRelTPlane.represented rho).algebra) (n : ℕ) : ℂ :=
  chi ((S.toRelTPlane.represented rho).coordinate (X ^ n, 0))

/-- The second valuation sequence `μ n = χ(0, Xⁿ)`. -/
def mu (chi : characterSpace ℂ (S.toRelTPlane.represented rho).algebra) (n : ℕ) : ℂ :=
  chi ((S.toRelTPlane.represented rho).coordinate (0, X ^ n))

/-! ### The dual shears on the valuation sequences -/

theorem lam_up (r : Polynomial (ZMod p))
    (chi : characterSpace ℂ (S.toRelTPlane.represented rho).algebra) (n : ℕ) :
    S.lam rho (S.dualUp rho r chi) n = S.lam rho chi n := by
  show S.dualUp rho r chi ((S.toRelTPlane.represented rho).coordinate (X ^ n, 0)) =
    chi ((S.toRelTPlane.represented rho).coordinate (X ^ n, 0))
  rw [S.dualUp_coordinate, mul_zero, add_zero]

theorem mu_low (r : Polynomial (ZMod p))
    (chi : characterSpace ℂ (S.toRelTPlane.represented rho).algebra) (n : ℕ) :
    S.mu rho (S.dualLow rho r chi) n = S.mu rho chi n := by
  show S.dualLow rho r chi ((S.toRelTPlane.represented rho).coordinate (0, X ^ n)) =
    chi ((S.toRelTPlane.represented rho).coordinate (0, X ^ n))
  rw [S.dualLow_coordinate, mul_zero, add_zero]

theorem mu_upX (chi : characterSpace ℂ (S.toRelTPlane.represented rho).algebra) (n : ℕ) :
    S.mu rho (S.dualUp rho X chi) n = S.lam rho chi (n + 1) * S.mu rho chi n := by
  show S.dualUp rho X chi ((S.toRelTPlane.represented rho).coordinate (0, X ^ n)) =
    chi ((S.toRelTPlane.represented rho).coordinate (X ^ (n + 1), 0)) *
      chi ((S.toRelTPlane.represented rho).coordinate (0, X ^ n))
  rw [S.dualUp_coordinate, zero_add, ← pow_succ',
    S.chi_coordinate_mk rho chi (X ^ (n + 1)) (X ^ n)]

theorem mu_up1 (chi : characterSpace ℂ (S.toRelTPlane.represented rho).algebra) (n : ℕ) :
    S.mu rho (S.dualUp rho 1 chi) n = S.lam rho chi n * S.mu rho chi n := by
  show S.dualUp rho 1 chi ((S.toRelTPlane.represented rho).coordinate (0, X ^ n)) =
    chi ((S.toRelTPlane.represented rho).coordinate (X ^ n, 0)) *
      chi ((S.toRelTPlane.represented rho).coordinate (0, X ^ n))
  rw [S.dualUp_coordinate, zero_add, one_mul, S.chi_coordinate_mk rho chi (X ^ n) (X ^ n)]

theorem lam_lowX (chi : characterSpace ℂ (S.toRelTPlane.represented rho).algebra) (n : ℕ) :
    S.lam rho (S.dualLow rho X chi) n = S.mu rho chi (n + 1) * S.lam rho chi n := by
  show S.dualLow rho X chi ((S.toRelTPlane.represented rho).coordinate (X ^ n, 0)) =
    chi ((S.toRelTPlane.represented rho).coordinate (0, X ^ (n + 1))) *
      chi ((S.toRelTPlane.represented rho).coordinate (X ^ n, 0))
  rw [S.dualLow_coordinate, zero_add, ← pow_succ',
    S.chi_coordinate_mk rho chi (X ^ n) (X ^ (n + 1))]
  exact mul_comm _ _

theorem lam_low1 (chi : characterSpace ℂ (S.toRelTPlane.represented rho).algebra) (n : ℕ) :
    S.lam rho (S.dualLow rho 1 chi) n = S.mu rho chi n * S.lam rho chi n := by
  show S.dualLow rho 1 chi ((S.toRelTPlane.represented rho).coordinate (X ^ n, 0)) =
    chi ((S.toRelTPlane.represented rho).coordinate (0, X ^ n)) *
      chi ((S.toRelTPlane.represented rho).coordinate (X ^ n, 0))
  rw [S.dualLow_coordinate, zero_add, one_mul, S.chi_coordinate_mk rho chi (X ^ n) (X ^ n)]
  exact mul_comm _ _

/-! ### The four regions -/

/-- `λ` becomes nontrivial strictly before `μ`. -/
def regionA : Set (characterSpace ℂ (S.toRelTPlane.represented rho).algebra) :=
  {chi | RelTSeq.SeqA (S.lam rho chi) (S.mu rho chi)}

/-- `λ` and `μ` become nontrivial at the same index. -/
def regionB : Set (characterSpace ℂ (S.toRelTPlane.represented rho).algebra) :=
  {chi | RelTSeq.SeqB (S.lam rho chi) (S.mu rho chi)}

/-- `μ` becomes nontrivial strictly before `λ`. -/
def regionC : Set (characterSpace ℂ (S.toRelTPlane.represented rho).algebra) :=
  {chi | RelTSeq.SeqA (S.mu rho chi) (S.lam rho chi)}

/-- The scalar region `λ 0 ≠ 1 ∨ μ 0 ≠ 1`. -/
def regionD : Set (characterSpace ℂ (S.toRelTPlane.represented rho).algebra) :=
  {chi | RelTSeq.SeqD (S.lam rho chi) (S.mu rho chi)}

theorem measurable_lam_eq_one (n : ℕ) :
    Measurable fun chi : characterSpace ℂ (S.toRelTPlane.represented rho).algebra ↦
      S.lam rho chi n = 1 :=
  measurableSet_setOf.mp (S.toRelTPlane.measurableSet_chi_coordinate_eq_one rho (X ^ n, 0))

theorem measurable_mu_eq_one (n : ℕ) :
    Measurable fun chi : characterSpace ℂ (S.toRelTPlane.represented rho).algebra ↦
      S.mu rho chi n = 1 :=
  measurableSet_setOf.mp (S.toRelTPlane.measurableSet_chi_coordinate_eq_one rho (0, X ^ n))

theorem measurableSet_regionA : MeasurableSet (S.regionA rho) :=
  measurableSet_setOf.mpr (RelTSeq.measurable_seqA (f := S.lam rho) (g := S.mu rho)
    (S.measurable_lam_eq_one rho) (S.measurable_mu_eq_one rho))

theorem measurableSet_regionB : MeasurableSet (S.regionB rho) :=
  measurableSet_setOf.mpr (RelTSeq.measurable_seqB (f := S.lam rho) (g := S.mu rho)
    (S.measurable_lam_eq_one rho) (S.measurable_mu_eq_one rho))

theorem measurableSet_regionC : MeasurableSet (S.regionC rho) :=
  measurableSet_setOf.mpr (RelTSeq.measurable_seqA (f := S.mu rho) (g := S.lam rho)
    (S.measurable_mu_eq_one rho) (S.measurable_lam_eq_one rho))

theorem measurableSet_regionD : MeasurableSet (S.regionD rho) :=
  measurableSet_setOf.mpr (RelTSeq.measurable_seqD (f := S.lam rho) (g := S.mu rho)
    (S.measurable_lam_eq_one rho) (S.measurable_mu_eq_one rho))

theorem disjoint_regionA_regionB : Disjoint (S.regionA rho) (S.regionB rho) :=
  Set.disjoint_left.mpr fun chi hA hB ↦
    RelTSeq.not_ap_and_bp (f := S.lam rho chi) (g := S.mu rho chi) hA hB

theorem disjoint_regionC_regionB : Disjoint (S.regionC rho) (S.regionB rho) :=
  Set.disjoint_left.mpr fun chi hC hB ↦
    RelTSeq.not_ap_and_bp (f := S.mu rho chi) (g := S.lam rho chi) hC
      (RelTSeq.bp_symm (f := S.lam rho chi) (g := S.mu rho chi) hB)

/-! ### Placements of the regions under the dual shears -/

theorem mapsTo_upX : Set.MapsTo (S.dualUp rho X) (S.regionA rho ∪ S.regionB rho)
    (S.regionC rho ∪ S.regionD rho) := by
  intro chi hchi
  have hl : S.lam rho (S.dualUp rho X chi) = S.lam rho chi := funext (S.lam_up rho X chi)
  have hm : S.mu rho (S.dualUp rho X chi) =
      fun n ↦ S.lam rho chi (n + 1) * S.mu rho chi n := funext (S.mu_upX rho chi)
  show RelTSeq.SeqA (S.mu rho (S.dualUp rho X chi)) (S.lam rho (S.dualUp rho X chi)) ∨
    RelTSeq.SeqD (S.lam rho (S.dualUp rho X chi)) (S.mu rho (S.dualUp rho X chi))
  rw [hl, hm]
  rcases hchi with hA | hB
  · exact RelTSeq.upShift_of_A (f := S.lam rho chi) (g := S.mu rho chi) hA
  · exact RelTSeq.upShift_of_B (f := S.lam rho chi) (g := S.mu rho chi) hB

theorem mapsTo_lowX : Set.MapsTo (S.dualLow rho X) (S.regionC rho ∪ S.regionB rho)
    (S.regionA rho ∪ S.regionD rho) := by
  intro chi hchi
  have hl : S.lam rho (S.dualLow rho X chi) =
      fun n ↦ S.mu rho chi (n + 1) * S.lam rho chi n := funext (S.lam_lowX rho chi)
  have hm : S.mu rho (S.dualLow rho X chi) = S.mu rho chi := funext (S.mu_low rho X chi)
  show RelTSeq.SeqA (S.lam rho (S.dualLow rho X chi)) (S.mu rho (S.dualLow rho X chi)) ∨
    RelTSeq.SeqD (S.lam rho (S.dualLow rho X chi)) (S.mu rho (S.dualLow rho X chi))
  rw [hl, hm]
  rcases hchi with hC | hB
  · exact Or.imp id RelTSeq.dp_symm
      (RelTSeq.upShift_of_A (f := S.mu rho chi) (g := S.lam rho chi) hC)
  · exact Or.imp id RelTSeq.dp_symm
      (RelTSeq.upShift_of_B (f := S.mu rho chi) (g := S.lam rho chi)
        (RelTSeq.bp_symm (f := S.lam rho chi) (g := S.mu rho chi) hB))

theorem mapsTo_up1 : Set.MapsTo (S.dualUp rho 1) (S.regionA rho) (S.regionB rho) := by
  intro chi hchi
  have hl : S.lam rho (S.dualUp rho 1 chi) = S.lam rho chi := funext (S.lam_up rho 1 chi)
  have hm : S.mu rho (S.dualUp rho 1 chi) =
      fun n ↦ S.lam rho chi n * S.mu rho chi n := funext (S.mu_up1 rho chi)
  show RelTSeq.SeqB (S.lam rho (S.dualUp rho 1 chi)) (S.mu rho (S.dualUp rho 1 chi))
  rw [hl, hm]
  exact RelTSeq.bp_of_ap (f := S.lam rho chi) (g := S.mu rho chi) hchi

theorem mapsTo_low1 : Set.MapsTo (S.dualLow rho 1) (S.regionC rho) (S.regionB rho) := by
  intro chi hchi
  have hl : S.lam rho (S.dualLow rho 1 chi) =
      fun n ↦ S.mu rho chi n * S.lam rho chi n := funext (S.lam_low1 rho chi)
  have hm : S.mu rho (S.dualLow rho 1 chi) = S.mu rho chi := funext (S.mu_low rho 1 chi)
  show RelTSeq.SeqB (S.lam rho (S.dualLow rho 1 chi)) (S.mu rho (S.dualLow rho 1 chi))
  rw [hl, hm]
  exact RelTSeq.bp_symm (RelTSeq.bp_of_ap (f := S.mu rho chi) (g := S.lam rho chi) hchi)

/-- Every character that is nontrivial at some plane element lies in one of the four regions. -/
theorem mem_regions_of_ne_one [NeZero p]
    (chi : characterSpace ℂ (S.toRelTPlane.represented rho).algebra) (a b : Polynomial (ZMod p))
    (hab : chi ((S.toRelTPlane.represented rho).coordinate (a, b)) ≠ 1) :
    chi ∈ S.regionA rho ∪ S.regionB rho ∪ S.regionC rho ∪ S.regionD rho := by
  have hex : ∃ n, S.lam rho chi n ≠ 1 ∨ S.mu rho chi n ≠ 1 := by
    by_contra hnone
    push Not at hnone
    apply hab
    have h1 : ∀ c : Polynomial (ZMod p),
        chi ((S.toRelTPlane.represented rho).coordinate (c, 0)) = 1 := fun c ↦
      RelTSeq.polyTrivial (fun c ↦ chi ((S.toRelTPlane.represented rho).coordinate (c, 0)))
        (S.chi_coordinate_add_fst rho chi) (S.toRelTPlane.chi_coordinate_zero rho chi)
        (fun n ↦ (hnone n).1) c
    have h2 : ∀ c : Polynomial (ZMod p),
        chi ((S.toRelTPlane.represented rho).coordinate (0, c)) = 1 := fun c ↦
      RelTSeq.polyTrivial (fun c ↦ chi ((S.toRelTPlane.represented rho).coordinate (0, c)))
        (S.chi_coordinate_add_snd rho chi) (S.toRelTPlane.chi_coordinate_zero rho chi)
        (fun n ↦ (hnone n).2) c
    rw [S.chi_coordinate_mk rho chi a b, h1, h2, mul_one]
  rcases RelTSeq.cover hex with h | h | h | h
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

end RelTShear

end

end GroupApproximation.Full.A2ThomT

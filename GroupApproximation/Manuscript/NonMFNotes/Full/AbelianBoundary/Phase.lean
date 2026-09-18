import GroupApproximation.Manuscript.NonMFNotes.Full.AbelianBoundary.Diagonal
import GroupApproximation.Manuscript.NonMFNotes.Full.AbelianBoundary.Bump
import GroupApproximation.Algebra.PermutationalWreath
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# Phase representations of lamp groups on finite quotients

Manuscript `non_mf_group_notes.tex`, `thm:notes-abelian-boundary` (tex lines 2078--2160),
torsion-free half (tex lines 2098--2150).  For a finite-index subgroup `K ≤ G`, the
proof puts lamps on `ℓ²(G ⧸ K)`:

* `Λ_n(g) δ_y = δ_{g y}` (`gRep`), the permutation representation;
* `D_n(a) δ_y = e^{i θ(a) f_n(y)} δ_y` for a lamp at the base site, moved to the site `x`
  by the coset representative `x.out`.  For a finitely supported configuration `f` the
  phases add up (`phase`), so `lampRep` is a homomorphism.

`opLength_conj_single_le` is the estimate from tex lines 2128--2133: conjugating a
one-site lamp by `Λ_n(g)` gives the lamp at the translated site up to
`|θ(a)| / (n + 1)`, provided the "cocycle" `(g x.out)⁻¹ (g x).out ∈ H` is one of the first `n`
generators.
-/

namespace GroupApproximation.Full.NN06

open Matrix

noncomputable section

variable {G : Type} [Group G] {H : Subgroup G} {A : Type} [AddCommGroup A]

/-- The finite model `ℓ²(G ⧸ K)` for a finite-index subgroup `K` (tex line 2119, `F_n`). -/
def quotModel (K : Subgroup G) [K.FiniteIndex] : FiniteModel :=
  ⟨G ⧸ K, Fintype.ofFinite (G ⧸ K), Classical.decEq (G ⧸ K)⟩

theorem quotModel_card_pos (K : Subgroup G) [K.FiniteIndex] :
    0 < Fintype.card (quotModel K) :=
  Fintype.card_pos_iff.mpr ⟨(QuotientGroup.mk (1 : G) : G ⧸ K)⟩

/-- The phase of a lamp configuration at a point of `G ⧸ K`:
`∑_x θ(f x) · f_n(x.out⁻¹ z)` (tex line 2126). -/
def phase (θ : A →+ ℝ) (e : ℕ → G) (n : ℕ) (K : Subgroup G)
    (f : Lamp (Multiplicative A) (G ⧸ H)) (z : G ⧸ K) : ℝ :=
  ∑ᶠ x : G ⧸ H, θ (Multiplicative.toAdd (f.toFun x)) * bump e n K (x.out⁻¹ • z)

theorem phase_term_finite (θ : A →+ ℝ) (e : ℕ → G) (n : ℕ) (K : Subgroup G)
    (f : Lamp (Multiplicative A) (G ⧸ H)) (z : G ⧸ K) :
    Function.HasFiniteSupport
      (fun x : G ⧸ H => θ (Multiplicative.toAdd (f.toFun x)) * bump e n K (x.out⁻¹ • z)) := by
  show (Function.support
    (fun x : G ⧸ H => θ (Multiplicative.toAdd (f.toFun x)) * bump e n K (x.out⁻¹ • z))).Finite
  refine Set.Finite.subset
    (f.2 : {x : G ⧸ H | (f : G ⧸ H → Multiplicative A) x ≠ 1}.Finite) ?_
  intro x hx
  have hx' : θ (Multiplicative.toAdd (f.toFun x)) * bump e n K (x.out⁻¹ • z) ≠ 0 := hx
  show f.toFun x ≠ 1
  intro h1
  exact hx' (by rw [h1, toAdd_one, map_zero, zero_mul])

theorem phase_mul (θ : A →+ ℝ) (e : ℕ → G) (n : ℕ) (K : Subgroup G)
    (f g : Lamp (Multiplicative A) (G ⧸ H)) :
    phase θ e n K (f * g) = phase θ e n K f + phase θ e n K g := by
  funext z
  show ∑ᶠ x : G ⧸ H, θ (Multiplicative.toAdd ((f * g).toFun x)) * bump e n K (x.out⁻¹ • z) =
    (∑ᶠ x : G ⧸ H, θ (Multiplicative.toAdd (f.toFun x)) * bump e n K (x.out⁻¹ • z)) +
      ∑ᶠ x : G ⧸ H, θ (Multiplicative.toAdd (g.toFun x)) * bump e n K (x.out⁻¹ • z)
  rw [← finsum_add_distrib (phase_term_finite θ e n K f z) (phase_term_finite θ e n K g z)]
  refine finsum_congr fun x => ?_
  rw [Lamp.mul_apply, toAdd_mul, map_add, add_mul]

theorem phase_single [DecidableEq (G ⧸ H)] (θ : A →+ ℝ) (e : ℕ → G) (n : ℕ)
    (K : Subgroup G) (x : G ⧸ H) (k : Multiplicative A) (z : G ⧸ K) :
    phase θ e n K (Lamp.single x k) z =
      θ (Multiplicative.toAdd k) * bump e n K (x.out⁻¹ • z) := by
  have hzero : ∀ y : G ⧸ H, y ≠ x →
      θ (Multiplicative.toAdd ((Lamp.single x k).toFun y)) * bump e n K (y.out⁻¹ • z) = 0 :=
    fun y hy => by rw [Lamp.single_apply_of_ne hy, toAdd_one, map_zero, zero_mul]
  show ∑ᶠ y : G ⧸ H, θ (Multiplicative.toAdd ((Lamp.single x k).toFun y)) *
      bump e n K (y.out⁻¹ • z) = θ (Multiplicative.toAdd k) * bump e n K (x.out⁻¹ • z)
  refine (finsum_eq_single _ x hzero).trans ?_
  rw [Lamp.single_apply_self]

/-- The diagonal lamp representation `f ↦ D_n(f)` on `ℓ²(G ⧸ K)` (tex line 2126). -/
def lampRep (θ : A →+ ℝ) (e : ℕ → G) (n : ℕ) (K : Subgroup G) [K.FiniteIndex] :
    Lamp (Multiplicative A) (G ⧸ H) →* Matrix.unitaryGroup (quotModel K) ℂ :=
  MonoidHom.mk' (fun f => diagUnitary (quotModel K) (phase θ e n K f)) fun f g =>
    (congrArg (diagUnitary (quotModel K)) (phase_mul θ e n K f g)).trans
      (diagUnitary_add (quotModel K) (phase θ e n K f) (phase θ e n K g))

theorem lampRep_apply (θ : A →+ ℝ) (e : ℕ → G) (n : ℕ) (K : Subgroup G) [K.FiniteIndex]
    (f : Lamp (Multiplicative A) (G ⧸ H)) :
    lampRep θ e n K f = diagUnitary (quotModel K) (phase θ e n K f) :=
  rfl

/-- The permutation representation `Λ_n` of `G` on `ℓ²(G ⧸ K)` (tex line 2125). -/
def gRep (K : Subgroup G) [K.FiniteIndex] : G →* Matrix.unitaryGroup (quotModel K) ℂ :=
  (permUnitaryHom (quotModel K)).comp (MulAction.toPermHom G (G ⧸ K))

theorem gRep_apply (K : Subgroup G) [K.FiniteIndex] (g : G) :
    gRep K g = permUnitaryHom (quotModel K) (MulAction.toPermHom G (G ⧸ K) g) :=
  rfl

/-- `|c a - c b| ≤ |c| r` from `|b - a| ≤ r`. -/
theorem abs_mul_sub_le {c a b r : ℝ} (h : |b - a| ≤ r) : |c * a - c * b| ≤ |c| * r := by
  calc |c * a - c * b| = |c| * |b - a| := by rw [← mul_sub, abs_mul, abs_sub_comm]
    _ ≤ |c| * r := mul_le_mul_of_nonneg_left h (abs_nonneg c)

/-- The translated phase differs from the phase at the translated site by at most
`|θ(a)| / (n + 1)` (tex lines 2128--2131). -/
theorem abs_phase_translate_le [DecidableEq (G ⧸ H)] (θ : A →+ ℝ) (e : ℕ → G) {n j : ℕ}
    (K : Subgroup G) (hj : j ≤ n) {g : G} {x : G ⧸ H}
    (hej : e j = (g * x.out)⁻¹ * (g • x).out) (k : Multiplicative A) (z : G ⧸ K) :
    |phase θ e n K (Lamp.single x k) (g⁻¹ • z) - phase θ e n K (Lamp.single (g • x) k) z| ≤
      |θ (Multiplicative.toAdd k)| / ((n : ℝ) + 1) := by
  have hg : (g • x).out⁻¹ = (e j)⁻¹ * x.out⁻¹ * g⁻¹ := by
    rw [hej]
    group
  have hsmul : (g • x).out⁻¹ • z = (e j)⁻¹ • (x.out⁻¹ • (g⁻¹ • z)) := by
    rw [hg, mul_smul, mul_smul]
  rw [phase_single, phase_single, hsmul]
  have ht' : ((e j)⁻¹)⁻¹ ∈ gens e n := by
    rw [inv_inv]
    exact e_mem_gens e hj
  have hb := abs_bump_smul_sub_le e (inv_e_mem_gens e hj) ht' (x.out⁻¹ • (g⁻¹ • z))
  exact (abs_mul_sub_le hb).trans_eq (mul_one_div _ _)

/-- The coset cocycle `(g x.out)⁻¹ (g x).out` lies in `H`. -/
theorem cocycle_mem (g : G) (x : G ⧸ H) : (g * x.out)⁻¹ * (g • x).out ∈ H := by
  have h : (QuotientGroup.mk (g * x.out) : G ⧸ H) = QuotientGroup.mk (g • x).out :=
    (MulAction.Quotient.mk_smul_out H g x).trans (QuotientGroup.out_eq' (g • x)).symm
  exact QuotientGroup.eq.mp h

/-- **Almost equivariance** (tex lines 2129--2133):
`‖Λ_n(g) D_n(a @ x) Λ_n(g)* - D_n(a @ g x)‖ ≤ |θ(a)|/(n+1)` once the cocycle is among the first
`n` generators. -/
theorem opLength_conj_single_le [DecidableEq (G ⧸ H)] (θ : A →+ ℝ) (e : ℕ → G) {n j : ℕ}
    (K : Subgroup G) [K.FiniteIndex] (hj : j ≤ n) {g : G} {x : G ⧸ H}
    (hej : e j = (g * x.out)⁻¹ * (g • x).out) (k : Multiplicative A) :
    opLength (quotModel K) ((lampRep θ e n K (Lamp.single (g • x) k))⁻¹ *
      (gRep K g * lampRep θ e n K (Lamp.single x k) * (gRep K g)⁻¹)) ≤
      |θ (Multiplicative.toAdd k)| / ((n : ℝ) + 1) := by
  have hconj : gRep K g * lampRep θ e n K (Lamp.single x k) * (gRep K g)⁻¹ =
      diagUnitary (quotModel K) (fun z => phase θ e n K (Lamp.single x k)
        ((MulAction.toPermHom G (G ⧸ K) g)⁻¹ z)) := by
    rw [lampRep_apply, gRep_apply]
    exact perm_conj_diagUnitary (quotModel K) (MulAction.toPermHom G (G ⧸ K) g)
      (phase θ e n K (Lamp.single x k))
  rw [hconj, lampRep_apply]
  have hr : (0 : ℝ) ≤ |θ (Multiplicative.toAdd k)| / ((n : ℝ) + 1) :=
    div_nonneg (abs_nonneg _) (Nat.cast_add_one_pos n).le
  exact opLength_diag_inv_mul_le (quotModel K) hr
    fun z => abs_phase_translate_le θ e K hj hej k z

end

#audit_axioms phase_mul
#audit_axioms phase_single
#audit_axioms abs_phase_translate_le
#audit_axioms cocycle_mem
#audit_axioms opLength_conj_single_le

end GroupApproximation.Full.NN06

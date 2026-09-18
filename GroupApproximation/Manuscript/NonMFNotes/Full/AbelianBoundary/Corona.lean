import GroupApproximation.Manuscript.NonMFNotes.Full.AbelianBoundary.Phase
import GroupApproximation.Algebra.PermutationalWreathSimple
import GroupApproximation.Meta.AxiomGuard

/-!
# The corona homomorphism of a lamp extension

Manuscript `non_mf_group_notes.tex`, `thm:notes-abelian-boundary` (tex lines 2078--2160),
torsion-free half (tex lines 2098--2150).  We take a sequence `N n` of finite-index
subgroups of `G` and an enumeration `e : ℕ → G` that covers `H`.  The representations
`D_n` (`lampRep`) and `Λ_n` (`gRep`) on `ℓ²(G ⧸ N n)` give homomorphisms
into the cofinite norm-matrix corona.  These are `coronaLamp` and `coronaG`.

They intertwine the lamp action up to null sequences (tex lines 2129--2133):
`coronaCompat`.  The universal property of the semidirect product then gives
`coronaHom : Lamp A (G ⧸ H) ⋊ G →* NormMatrixCoronaUnitary`.
-/

namespace GroupApproximation.Full.NN06

open Matrix

noncomputable section

variable {G : Type} [Group G] {H : Subgroup G} {A : Type} [AddCommGroup A]

/-- The finite models `ℓ²(G ⧸ N n)`. -/
abbrev quotModels (N : ℕ → Subgroup G) [∀ n, (N n).FiniteIndex] : ℕ → FiniteModel :=
  fun n => quotModel (N n)

theorem quotModels_card_pos (N : ℕ → Subgroup G) [∀ n, (N n).FiniteIndex] (n : ℕ) :
    0 < Fintype.card (quotModels N n) :=
  quotModel_card_pos (N n)

/-- The lamp representation in the corona, `f ↦ [(D_n(f))_n]` (tex line 2126). -/
def coronaLamp (θ : A →+ ℝ) (e : ℕ → G) (N : ℕ → Subgroup G) [∀ n, (N n).FiniteIndex] :
    Lamp (Multiplicative A) (G ⧸ H) →* NormMatrixCoronaUnitary (quotModels N) :=
  (QuotientGroup.mk' (nullCofiniteOpSubgroup (quotModels N))).comp
    (MonoidHom.pi fun n => lampRep θ e n (N n))

theorem coronaLamp_apply (θ : A →+ ℝ) (e : ℕ → G) (N : ℕ → Subgroup G)
    [∀ n, (N n).FiniteIndex] (f : Lamp (Multiplicative A) (G ⧸ H)) :
    coronaLamp θ e N f =
      (QuotientGroup.mk (fun n => lampRep θ e n (N n) f) : NormMatrixCoronaUnitary (quotModels N)) :=
  rfl

/-- The permutation representation in the corona, `g ↦ [(Λ_n(g))_n]` (tex line 2125). -/
def coronaG (N : ℕ → Subgroup G) [∀ n, (N n).FiniteIndex] :
    G →* NormMatrixCoronaUnitary (quotModels N) :=
  (QuotientGroup.mk' (nullCofiniteOpSubgroup (quotModels N))).comp
    (MonoidHom.pi fun n => gRep (N n))

/-- `c / (n + 1) < ε` once `n ≥ M > c / ε`. -/
theorem div_succ_lt {c ε : ℝ} (hε : 0 < ε) {M n : ℕ} (hM : c / ε < M) (hn : M ≤ n) :
    c / ((n : ℝ) + 1) < ε := by
  rw [div_lt_iff₀ (Nat.cast_add_one_pos n)]
  have h1 : c < (M : ℝ) * ε := (div_lt_iff₀ hε).mp hM
  have h2 : (M : ℝ) * ε ≤ (n : ℝ) * ε :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn) hε.le
  linarith

/-- A property holding from some index on holds cofinitely. -/
theorem eventually_cofinite_of_ge {p : ℕ → Prop} (m : ℕ) (h : ∀ n, m ≤ n → p n) :
    ∀ᶠ n in Filter.cofinite, p n := by
  rw [Nat.cofinite_eq_atTop]
  exact Filter.eventually_atTop.mpr ⟨m, h⟩

/-- **Asymptotic equivariance** (tex lines 2129--2133): in the corona, `coronaG` conjugates
`coronaLamp` exactly as `G` acts on configurations. -/
theorem coronaCompat (θ : A →+ ℝ) (e : ℕ → G) (N : ℕ → Subgroup G) [∀ n, (N n).FiniteIndex]
    (hsurj : ∀ h ∈ H, ∃ j, e j = h) (g : G) :
    (coronaLamp (H := H) θ e N).comp
        (lampActionHom (K := Multiplicative A) (X := G ⧸ H) g).toMonoidHom =
      (MulAut.conj (coronaG N g)).toMonoidHom.comp (coronaLamp θ e N) := by
  classical
  refine MonoidHom.eq_of_eqOn_dense
    (s := {f : Lamp (Multiplicative A) (G ⧸ H) |
      ∃ (x : G ⧸ H) (k : Multiplicative A), f = Lamp.single x k})
    ((Subgroup.eq_top_iff' _).mpr fun f => Lamp.mem_closure_singles f) ?_
  rintro _ ⟨x, k, rfl⟩
  show coronaLamp θ e N (lampAut (K := Multiplicative A) (X := G ⧸ H) g (Lamp.single x k)) =
    coronaG N g * coronaLamp θ e N (Lamp.single x k) * (coronaG N g)⁻¹
  rw [lampAut_single]
  refine (QuotientGroup.eq (s := nullCofiniteOpSubgroup (quotModels N))
    (a := fun n => lampRep θ e n (N n) (Lamp.single (g • x) k))
    (b := fun n => gRep (N n) g * lampRep θ e n (N n) (Lamp.single x k) *
      (gRep (N n) g)⁻¹)).mpr ?_
  show IsNullCofiniteOpSeq (quotModels N) _
  intro ε hε
  obtain ⟨j, hj⟩ := hsurj _ (cocycle_mem g x)
  obtain ⟨M, hM⟩ := exists_nat_gt (|θ (Multiplicative.toAdd k)| / ε)
  refine eventually_cofinite_of_ge (max j M) fun n hn => ?_
  exact (opLength_conj_single_le θ e (N n) (le_of_max_le_left hn) hj k).trans_lt
    (div_succ_lt hε hM (le_of_max_le_right hn))

/-- The corona representation of `Lamp A (G ⧸ H) ⋊ G` (tex lines 2125--2133). -/
def coronaHom (θ : A →+ ℝ) (e : ℕ → G) (N : ℕ → Subgroup G) [∀ n, (N n).FiniteIndex]
    (hsurj : ∀ h ∈ H, ∃ j, e j = h) :
    Wreath (Multiplicative A) G (G ⧸ H) →* NormMatrixCoronaUnitary (quotModels N) :=
  SemidirectProduct.lift (coronaLamp θ e N) (coronaG N) (coronaCompat θ e N hsurj)

theorem coronaHom_inl (θ : A →+ ℝ) (e : ℕ → G) (N : ℕ → Subgroup G)
    [∀ n, (N n).FiniteIndex] (hsurj : ∀ h ∈ H, ∃ j, e j = h)
    (f : Lamp (Multiplicative A) (G ⧸ H)) :
    coronaHom θ e N hsurj (SemidirectProduct.inl f) = coronaLamp θ e N f :=
  SemidirectProduct.lift_inl _ _ _ f

end

#audit_axioms div_succ_lt
#audit_axioms coronaCompat
#audit_axioms coronaHom_inl

end GroupApproximation.Full.NN06

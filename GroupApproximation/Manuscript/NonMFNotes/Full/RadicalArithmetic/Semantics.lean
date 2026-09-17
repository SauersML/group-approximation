import GroupApproximation.Computability.MFRecognitionOpenCore
import GroupApproximation.Sofic.OperatorMFPairAmplification
import GroupApproximation.Sofic.NormMFCoronaRadical
import GroupApproximation.Sofic.ActualCoronaMFRadical
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:mf-radical-arithmetic`: microstate semantics of radical non-membership

Manuscript `non_mf_group_notes.tex`, `thm:mf-radical-arithmetic`, proof:

> "Marked corona extraction and amplification, in one direction, and the
> diagonal norm-corona construction, in the other, give
> `v ∉ Res_MF(G_P) ⟺ ∀ n ∃ d D(P,v,n,d)`."

This file proves that equivalence with `D(P,v,n,d)` replaced by the
open-condition microstate predicate `MFRecognitionPi02.PassesOpen c [v] k M`
(relator defects `< 1/(k+1)`, survivor displacement `> 1/3`), which the
repository's matrix-answer checker already decides.

* Forward (marked corona extraction and amplification): a corona
  representation not killing `v` has a lift that is asymptotically exact on
  relators and frequently `δ`-separated at `v`; a Kronecker power of bounded
  order `p ≤ N` pushes the separation above `1` while multiplying relator
  defects by at most `N + 1`.
* Backward (diagonal norm-corona construction): a sequence of microstates
  with defects `< 1/(k+1)` induces a genuine homomorphism into the cofinite
  corona in which `v` survives.
-/

namespace GroupApproximation.Full.NN02

open PresentationCodes AdianRabinWordProblem MFMicrostate

noncomputable section

/-! ## Kronecker powers of microstates -/

/-- The `p`-th Kronecker power as a homomorphism of unitary groups. -/
def radTensorHom (Y : FiniteModel) (p : ℕ) :
    Matrix.unitaryGroup Y ℂ →* Matrix.unitaryGroup (opTensorModel Y p) ℂ where
  toFun U := ⟨opTensorPow (U : Matrix Y Y ℂ) p, opTensorPow_mem_unitaryGroup U.property p⟩
  map_one' := by
    apply Subtype.ext
    exact opTensorPow_one p
  map_mul' a b := by
    apply Subtype.ext
    change opTensorPow ((a : Matrix Y Y ℂ) * (b : Matrix Y Y ℂ)) p =
      opTensorPow (a : Matrix Y Y ℂ) p * opTensorPow (b : Matrix Y Y ℂ) p
    exact opTensorPow_mul _ _ p

/-- The Kronecker-power microstate of a family of generator unitaries. -/
def radTensorMicrostate (c : PresentationCode) (Y : FiniteModel) (hY : Nonempty Y)
    (g : Fin (genCount c) → Matrix.unitaryGroup Y ℂ) (p : ℕ) : Microstate c where
  model := opTensorModel Y p
  card_pos := Fintype.card_pos_iff.mpr ⟨opTensorRepeat (Classical.choice hY) p⟩
  gen j := radTensorHom Y p (g j)

theorem radTensorMicrostate_hom (c : PresentationCode) (Y : FiniteModel) (hY : Nonempty Y)
    (g : Fin (genCount c) → Matrix.unitaryGroup Y ℂ) (p : ℕ)
    (x : FreeGroup (Fin (genCount c))) :
    (radTensorMicrostate c Y hY g p).hom x = radTensorHom Y p (FreeGroup.lift g x) :=
  FreeGroup.lift_unique (f := fun j => radTensorHom Y p (g j))
    ((radTensorHom Y p).comp (FreeGroup.lift g))
    (fun j => by
      show radTensorHom Y p (FreeGroup.lift g (FreeGroup.of j)) = radTensorHom Y p (g j)
      rw [FreeGroup.lift_apply_of]) (x := x) |>.symm

/-- Tensor powers multiply displacements by at most the order. -/
theorem radTensorMicrostate_len_le (c : PresentationCode) (Y : FiniteModel) (hY : Nonempty Y)
    (g : Fin (genCount c) → Matrix.unitaryGroup Y ℂ) (p : ℕ) (w : List (ℕ × Bool)) :
    (radTensorMicrostate c Y hY g p).len w ≤
      (p : ℝ) * opLength Y (FreeGroup.lift g (wordOf c w)) := by
  have h := l2_opNorm_opTensorPow_sub_le hY (FreeGroup.lift g (wordOf c w)).property
    (one_mem (Matrix.unitaryGroup Y ℂ)) p
  rw [opTensorPow_one] at h
  rw [Microstate.len_def, radTensorMicrostate_hom]
  exact h

/-! ## Lifts into the cofinite corona -/

theorem radMk'_eq_one_of_null {X : ℕ → FiniteModel} {v : ∀ n, Matrix.unitaryGroup (X n) ℂ}
    (hv : IsNullCofiniteOpSeq X v) : QuotientGroup.mk' (nullCofiniteOpSubgroup X) v = 1 := by
  apply MonoidHom.mem_ker.1
  rw [QuotientGroup.ker_mk']
  exact hv

theorem radNull_of_mk'_eq_one {X : ℕ → FiniteModel} {v : ∀ n, Matrix.unitaryGroup (X n) ℂ}
    (hv : QuotientGroup.mk' (nullCofiniteOpSubgroup X) v = 1) : IsNullCofiniteOpSeq X v := by
  have hk : v ∈ MonoidHom.ker (QuotientGroup.mk' (nullCofiniteOpSubgroup X)) :=
    MonoidHom.mem_ker.2 hv
  rw [QuotientGroup.ker_mk'] at hk
  exact hk

theorem radFreeLift_apply_eval {α : Type} {X : ℕ → FiniteModel}
    (u : α → ∀ n, Matrix.unitaryGroup (X n) ℂ) (n : ℕ) (x : FreeGroup α) :
    FreeGroup.lift u x n = FreeGroup.lift (fun j => u j n) x :=
  FreeGroup.lift_unique (f := fun j => u j n)
    ((Pi.evalMonoidHom (fun n => Matrix.unitaryGroup (X n) ℂ) n).comp (FreeGroup.lift u))
    (fun j => by
      show FreeGroup.lift u (FreeGroup.of j) n = u j n
      rw [FreeGroup.lift_apply_of]) (x := x)

theorem radCorona_lift_ev {c : PresentationCode} {X : ℕ → FiniteModel}
    (ρ : Carrier c →* NormMatrixCoronaUnitary X)
    (u : Fin (genCount c) → ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (hu : ∀ j, QuotientGroup.mk' (nullCofiniteOpSubgroup X) (u j) = ρ (PresentedGroup.of j))
    (x : FreeGroup (Fin (genCount c))) :
    QuotientGroup.mk' (nullCofiniteOpSubgroup X) (FreeGroup.lift u x) = ρ (evHom c x) := by
  have h1 := FreeGroup.lift_unique (f := fun j => ρ (PresentedGroup.of j))
    ((QuotientGroup.mk' (nullCofiniteOpSubgroup X)).comp (FreeGroup.lift u))
    (fun j => by
      show QuotientGroup.mk' (nullCofiniteOpSubgroup X) (FreeGroup.lift u (FreeGroup.of j)) =
        ρ (PresentedGroup.of j)
      rw [FreeGroup.lift_apply_of]
      exact hu j) (x := x)
  have h2 := FreeGroup.lift_unique (f := fun j => ρ (PresentedGroup.of j))
    (ρ.comp (evHom c)) (fun _ => rfl) (x := x)
  exact h1.trans h2.symm

/-! ## Forward direction: marked corona extraction and amplification -/

theorem exists_passesOpen_of_not_mem {c : PresentationCode} {v : List (ℕ × Bool)}
    (hv : ev c v ∉ coronaMFResidual (Carrier c)) (k : ℕ) :
    ∃ M : Microstate c, MFRecognitionPi02.PassesOpen c [v] k M := by
  have hsurv : ∃ (X : ℕ → FiniteModel) (_ : ∀ n, 0 < Fintype.card (X n))
      (ρ : Carrier c →* NormMatrixCoronaUnitary X), ρ (ev c v) ≠ 1 := by
    by_contra hcon
    apply hv
    rw [mem_coronaMFResidual_iff]
    intro X hX ρ
    by_contra hρ
    exact hcon ⟨X, hX, ρ, hρ⟩
  obtain ⟨X, hX, ρ, hρ⟩ := hsurv
  choose u hu using fun j : Fin (genCount c) =>
    QuotientGroup.mk'_surjective (nullCofiniteOpSubgroup X) (ρ (PresentedGroup.of j))
  have hev : ∀ x, QuotientGroup.mk' (nullCofiniteOpSubgroup X) (FreeGroup.lift u x) =
      ρ (evHom c x) := radCorona_lift_ev ρ u hu
  have hrel : ∀ r ∈ c.2, IsNullCofiniteOpSeq X (FreeGroup.lift u (wordOf c r)) := by
    intro r hr
    apply radNull_of_mk'_eq_one
    rw [hev]
    have h1 : evHom c (wordOf c r) = 1 :=
      (ev_eq_one_iff c r).2 (wordProblem_of_mem_relators hr)
    rw [h1, map_one]
  have hvnot : ¬ IsNullCofiniteOpSeq X (FreeGroup.lift u (wordOf c v)) := by
    intro hnull
    apply hρ
    have h1 := radMk'_eq_one_of_null hnull
    rw [hev] at h1
    exact h1
  have hex : ∃ δ : ℝ, 0 < δ ∧ ∃ᶠ n in Filter.cofinite,
      δ ≤ opLength (X n) (FreeGroup.lift u (wordOf c v) n) := by
    by_contra hcon
    apply hvnot
    intro δ hδ
    by_contra hbad
    exact hcon ⟨δ, hδ, (Filter.not_eventually.1 hbad).mono fun n hn => not_lt.1 hn⟩
  obtain ⟨δ, hδ, hfreq⟩ := hex
  have hδsq : 0 < δ ^ 2 := by positivity
  obtain ⟨N, hNraw⟩ := exists_nat_gt (8 / δ ^ 2)
  have hN : 8 < (N : ℝ) * δ ^ 2 := by
    rwa [div_lt_iff₀ hδsq] at hNraw
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = 1 / ((k : ℝ) + 1) / ((N : ℝ) + 1) := ⟨_, rfl⟩
  have hε : 0 < ε := by
    rw [hεdef]
    positivity
  have hkey : ((N : ℝ) + 1) * ε = 1 / ((k : ℝ) + 1) := by
    rw [hεdef]
    exact mul_div_cancel₀ _ hNpos.ne'
  have hev2 : ∀ᶠ n in Filter.cofinite, ∀ r ∈ c.2.toFinset,
      opLength (X n) (FreeGroup.lift u (wordOf c r) n) < ε := by
    rw [Filter.eventually_all_finset]
    intro r hr
    exact hrel r (List.mem_toFinset.1 hr) ε hε
  obtain ⟨n, hnsep, hnrel⟩ := (hfreq.and_eventually hev2).exists
  have hYn : Nonempty (X n) := Fintype.card_pos_iff.mp (hX n)
  obtain ⟨p, _, hpN, hpfar⟩ := OperatorNormAmplification.exists_tensorPower_far_from_one hYn
    (FreeGroup.lift u (wordOf c v) n).property hδ hnsep N hN
  refine ⟨radTensorMicrostate c (X n) hYn (fun j => u j n) p, And.intro ?_ ?_⟩
  · intro r hr
    have hr' := hnrel r (List.mem_toFinset.2 hr)
    rw [radFreeLift_apply_eval u n (wordOf c r)] at hr'
    have hpN' : (p : ℝ) ≤ (N : ℝ) + 1 := by
      have hpN'' : (p : ℝ) ≤ N := by exact_mod_cast hpN
      linarith
    calc (radTensorMicrostate c (X n) hYn (fun j => u j n) p).len r
        ≤ (p : ℝ) * opLength (X n) (FreeGroup.lift (fun j => u j n) (wordOf c r)) :=
          radTensorMicrostate_len_le c (X n) hYn (fun j => u j n) p r
      _ ≤ ((N : ℝ) + 1) * opLength (X n) (FreeGroup.lift (fun j => u j n) (wordOf c r)) :=
          mul_le_mul_of_nonneg_right hpN' (opLength_nonneg _ _)
      _ < ((N : ℝ) + 1) * ε := mul_lt_mul_of_pos_left hr' hNpos
      _ = 1 / ((k : ℝ) + 1) := hkey
  · intro w hw
    rw [List.mem_singleton] at hw
    rw [hw, Microstate.len_def, radTensorMicrostate_hom,
      ← radFreeLift_apply_eval u n (wordOf c v)]
    exact lt_trans (by norm_num : (1 : ℝ) / 3 < 1) hpfar

/-! ## Backward direction: the diagonal norm-corona construction -/

/-- The diagonal free-group homomorphism of a sequence of microstates. -/
def radDiagonalHom {c : PresentationCode} (M : ℕ → Microstate c) :
    FreeGroup (Fin (genCount c)) →* ∀ n, Matrix.unitaryGroup (M n).model ℂ :=
  MonoidHom.pi fun n => (M n).hom

/-- The corona images of the generators under the diagonal construction. -/
def radDiagonalGen {c : PresentationCode} (M : ℕ → Microstate c) (j : Fin (genCount c)) :
    NormMatrixCoronaUnitary (fun n => (M n).model) :=
  QuotientGroup.mk' (nullCofiniteOpSubgroup (fun n => (M n).model))
    (radDiagonalHom M (FreeGroup.of j))

theorem lift_radDiagonalGen {c : PresentationCode} (M : ℕ → Microstate c)
    (x : FreeGroup (Fin (genCount c))) :
    FreeGroup.lift (radDiagonalGen M) x =
      QuotientGroup.mk' (nullCofiniteOpSubgroup (fun n => (M n).model)) (radDiagonalHom M x) :=
  (FreeGroup.lift_unique (f := radDiagonalGen M)
    ((QuotientGroup.mk' (nullCofiniteOpSubgroup (fun n => (M n).model))).comp
      (radDiagonalHom M))
    (fun _ => rfl) (x := x)).symm

theorem radDiagonal_relator_null {c : PresentationCode} (M : ℕ → Microstate c)
    (hM : ∀ k, ∀ r ∈ c.2, (M k).len r < 1 / ((k : ℝ) + 1)) {r : List (ℕ × Bool)}
    (hr : r ∈ c.2) :
    IsNullCofiniteOpSeq (fun n => (M n).model) (radDiagonalHom M (wordOf c r)) := by
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_one_div_lt hε
  rw [Nat.cofinite_eq_atTop]
  refine Filter.eventually_atTop.2 ⟨K, fun n hn => ?_⟩
  have hsmall : (M n).len r < 1 / ((n : ℝ) + 1) := hM n r hr
  have hmono : 1 / ((n : ℝ) + 1) ≤ 1 / ((K : ℝ) + 1) := by
    apply one_div_le_one_div_of_le
    · positivity
    · have hKn : (K : ℝ) ≤ n := by exact_mod_cast hn
      linarith
  show opLength (M n).model ((M n).hom (wordOf c r)) < ε
  exact lt_of_lt_of_le hsmall (hmono.trans hK.le)

theorem radDiagonal_survivor_not_null {c : PresentationCode} {v : List (ℕ × Bool)}
    (M : ℕ → Microstate c) (hM : ∀ k, 1 / 3 < (M k).len v) :
    ¬ IsNullCofiniteOpSeq (fun n => (M n).model) (radDiagonalHom M (wordOf c v)) := by
  intro hnull
  have h := hnull (1 / 3) (by norm_num)
  rw [Nat.cofinite_eq_atTop] at h
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 h
  have h1 : (M K).len v < 1 / 3 := hK K le_rfl
  exact lt_irrefl _ (lt_trans (hM K) h1)

theorem not_mem_of_forall_passesOpen {c : PresentationCode} {v : List (ℕ × Bool)}
    (h : ∀ k, ∃ M : Microstate c, MFRecognitionPi02.PassesOpen c [v] k M) :
    ev c v ∉ coronaMFResidual (Carrier c) := by
  choose M hM using h
  have hrels : ∀ r ∈ relatorSet c, FreeGroup.lift (radDiagonalGen M) r = 1 := by
    intro r hr
    obtain ⟨u, hu, rfl⟩ := mem_relatorSet_iff.1 hr
    rw [lift_radDiagonalGen]
    exact radMk'_eq_one_of_null (radDiagonal_relator_null M (fun k => (hM k).1) hu)
  have hsurv : ¬ IsNullCofiniteOpSeq (fun n => (M n).model) (radDiagonalHom M (wordOf c v)) :=
    radDiagonal_survivor_not_null M (fun k => (hM k).2 v (List.mem_singleton_self v))
  intro hmem
  rw [mem_coronaMFResidual_iff] at hmem
  have h1 := hmem (fun n => (M n).model) (fun n => (M n).card_pos)
    (PresentedGroup.toGroup hrels)
  have h2 : FreeGroup.lift (radDiagonalGen M) (wordOf c v) = 1 := h1
  rw [lift_radDiagonalGen] at h2
  exact hsurv (radNull_of_mk'_eq_one h2)

/-! ## The equivalence -/

/-- **`thm:mf-radical-arithmetic`, proof display** (`non_mf_group_notes.tex`):
`v ∉ Res_MF(G_P) ⟺ ∀ n ∃ microstate passing the open test at level n`,
for the internal unitary-sequence radical. -/
theorem not_mem_coronaMFResidual_iff (c : PresentationCode) (v : List (ℕ × Bool)) :
    ev c v ∉ coronaMFResidual (Carrier c) ↔
      ∀ k, ∃ M : Microstate c, MFRecognitionPi02.PassesOpen c [v] k M :=
  ⟨fun hv k => exists_passesOpen_of_not_mem hv k, not_mem_of_forall_passesOpen⟩

/-- The same equivalence for the literal manuscript radical
`manuscriptCoronaMFResidual` (natural matrix dimensions). -/
theorem not_mem_manuscriptCoronaMFResidual_iff (c : PresentationCode) (v : List (ℕ × Bool)) :
    ev c v ∉ manuscriptCoronaMFResidual (Carrier c) ↔
      ∀ k, ∃ M : Microstate c, MFRecognitionPi02.PassesOpen c [v] k M := by
  rw [manuscriptCoronaMFResidual_eq_coronaMFResidual]
  exact not_mem_coronaMFResidual_iff c v

/-- Closed form of the microstate semantics of radical non-membership. -/
def RadicalWordSemantics : Prop :=
  ∀ (c : PresentationCode) (v : List (ℕ × Bool)),
    ev c v ∉ manuscriptCoronaMFResidual (Carrier c) ↔
      ∀ k, ∃ M : Microstate c, MFRecognitionPi02.PassesOpen c [v] k M

/-- **`thm:mf-radical-arithmetic`, proof display, closed.** -/
theorem manuscriptRadicalWordSemantics : RadicalWordSemantics :=
  not_mem_manuscriptCoronaMFResidual_iff

end

#audit_closed_axioms GroupApproximation.Full.NN02.manuscriptRadicalWordSemantics

end GroupApproximation.Full.NN02

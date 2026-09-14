import GroupApproximation.Manuscript.SimpleKazhdanSofic.MatricialMarkedLimit
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MainAssembly
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.CharP.Two
import Mathlib.Order.Filter.Cofinite
import Mathlib.Order.Filter.Ultrafilter.Basic

/-!
# `simple_kazhdan_sofic_group.tex`, "Finite simple models": the marked limit

`simple_kazhdan_sofic_group.tex` at 696c4b602, "Finite simple models", tex 214–234:

> Let $F$ be the free algebra over $\F_2$ on letters $\tau_s$, $s\in S$, and let $\pi\colon F\to R$
> and $\rho_k\colon F\to M_{N_k}(\F_2)$ be the ring homomorphisms with $\pi(\tau_s)=s$ and
> $\rho_k(\tau_s)=\varphi_k(s)$. Both are onto, so $G$ and $\EL_3(M_{N_k}(\F_2))$ are quotients of
> $\EL_3(F)$. [...] So a word that is trivial in $G$ is trivial in $\SL_{3N_k}(\F_2)$ for large $k$.
> Conversely, [...] its kernel on $G$ is a normal subgroup that does not contain $e_{12}(1)$, so it
> is trivial. As this holds for every $\omega$, each nontrivial word is nontrivial in
> $\SL_{3N_k}(\F_2)$ for all but finitely many $k$. So these finite simple groups converge to $G$ in
> the space of marked groups [...]

The matricial hypotheses are those of the printed definition (tex l.113–117), and in addition the
matrix sizes are eventually positive: without that the printed conclusion fails, since `M_0(F₂)`
satisfies every printed axiom while `SL_0(F₂)` is trivial.

* `one_add_one_eq_zero_of_matricial`: the kernel argument applied to `e_12(1 + 1)` shows `R` has
  characteristic two, so `R` is an `F₂`-algebra and the free algebra `F` of the printed proof maps
  to it;
* `piLetters`, `rhoLetters`: `π` and `ρ_k` on the letters `τ_s`;
* `isMarkedLimit_of_matricial`: `EL_n(R)` marked by the `e_ij(s)` is the limit of
  `EL_n(M_{N_k}(F₂))` marked by the `e_ij(φ_k(s))`, for every `n ≥ 3`, in ct-two-ended's
  `IsMarkedLimit` spelling.
-/

namespace GroupApproximation

namespace SimpleKazhdanSofic

open Filter

/-- `1 + 1 = 0` in every matrix algebra over `F₂`. -/
theorem one_add_one_matrix_zmodTwo (m : ℕ) : (1 + 1 : Matrix (Fin m) (Fin m) (ZMod 2)) = 0 :=
  Matrix.ext fun i j => by
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _

/-- `FreeGroup.lift` commutes with homomorphisms. -/
theorem lift_comp_hom {ι G H : Type*} [Group G] [Group H] (f : G →* H) (q : ι → G)
    (w : FreeGroup ι) : FreeGroup.lift (fun p => f (q p)) w = f (FreeGroup.lift q w) :=
  (FreeGroup.lift_unique (f := fun p => f (q p)) (f.comp (FreeGroup.lift q))
    (fun p => by simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of]) (x := w)).symm

section Matricial

variable {R : Type*} [Ring R] (S : Finset R) (N : ℕ → ℕ)
  (φ : ∀ k, R → Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))

theorem nontrivial_matrix_eventually (hpos : ∀ᶠ k in atTop, 0 < N k) :
    ∀ᶠ k in atTop, Nontrivial (Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)) :=
  hpos.mono fun k hk => by
    haveI : Nonempty (Fin (N k)) := ⟨⟨0, hk⟩⟩
    infer_instance

theorem hyperfilter_le_atTop : ((hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ) ≤ atTop := by
  rw [← Nat.cofinite_eq_atTop]
  exact hyperfilter_le_cofinite

/-- The kernel argument (tex 229–231) applied to the root `e_12(1 + 1)`: a matricial ring with
simple `EL_n`, `n ≥ 2`, has characteristic two. -/
theorem one_add_one_eq_zero_of_matricial {n : ℕ} (hn : 2 ≤ n)
    [IsSimpleGroup ↥(elementaryGroup (Fin n) R)] (h1 : ∀ k, φ k 1 = 1)
    (hadd : ∀ r s : R, ∀ᶠ k in atTop, φ k (r + s) = φ k r + φ k s)
    (hmul : ∀ r s : R, ∀ᶠ k in atTop, φ k (r * s) = φ k r * φ k s)
    (hpos : ∀ᶠ k in atTop, 0 < N k) : (1 + 1 : R) = 0 := by
  have hi : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hΦ : ultraMap φ hyperfilter_le_atTop h1 hadd hmul (1 + 1) = 0 := by
    rw [map_add, map_one]
    show ((1 + 1 : ∀ k, Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)) :
        (ultraCon ((hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ)
          (fun k => Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))).Quotient) =
      ((0 : ∀ k, Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)) :
        (ultraCon ((hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ)
          (fun k => Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))).Quotient)
    exact congrArg (fun x : ∀ k, Matrix (Fin (N k)) (Fin (N k)) (ZMod 2) =>
      (x : (ultraCon ((hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ)
          (fun k => Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))).Quotient))
      (funext fun k => one_add_one_matrix_zmodTwo (N k))
  have hg := eq_one_of_ultraMap_eq_one φ hyperfilter_le_atTop h1 hadd hmul
    (nontrivial_matrix_eventually N hpos) hn
    (⟨elementaryUnit _ _ hi (1 + 1 : R), elementaryUnit_mem _ _ _ _⟩ : ↥(elementaryGroup (Fin n) R))
    (by
      apply Subtype.ext
      show elementaryMatrixUnitMap (ultraMap φ hyperfilter_le_atTop h1 hadd hmul)
          (elementaryUnit _ _ hi (1 + 1 : R)) = 1
      rw [elementaryMatrixUnitMap_elementaryUnit, hΦ, elementaryUnit_zero])
  have hg' : elementaryUnit (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ hi (1 + 1 : R) =
      elementaryUnit _ _ hi 0 := by
    rw [elementaryUnit_zero]
    exact congrArg Subtype.val hg
  exact elementaryUnit_injective _ _ hi hg'

/-- `π : F → R`, `τ_s ↦ s` (tex 215–216). -/
noncomputable def piLetters [Algebra (ZMod 2) R] : FreeAlgebra (ZMod 2) ↥S →+* R :=
  (FreeAlgebra.lift (ZMod 2) fun s : ↥S => (s : R)).toRingHom

/-- `ρ_k : F → M_{N_k}(F₂)`, `τ_s ↦ φ_k(s)` (tex 215–216). -/
noncomputable def rhoLetters (k : ℕ) :
    FreeAlgebra (ZMod 2) ↥S →+* Matrix (Fin (N k)) (Fin (N k)) (ZMod 2) :=
  (FreeAlgebra.lift (ZMod 2) fun s : ↥S => φ k s).toRingHom

theorem piLetters_ι [Algebra (ZMod 2) R] (s : ↥S) :
    piLetters S (FreeAlgebra.ι (ZMod 2) s) = s :=
  FreeAlgebra.lift_ι_apply _ s

omit [Ring R] in
theorem rhoLetters_ι (k : ℕ) (s : ↥S) :
    rhoLetters S N φ k (FreeAlgebra.ι (ZMod 2) s) = φ k s :=
  FreeAlgebra.lift_ι_apply _ s

/-- **The marked limit of `thm:general`** (tex 214–234), for every `n ≥ 3`: under the printed
matricial hypotheses, with eventually positive sizes and simple `EL_n(R)`, `EL_n(R)` marked by the
`e_ij(s)`, `s ∈ S`, is the limit of `EL_n(M_{N_k}(F₂))` marked by the `e_ij(φ_k(s))`. -/
theorem isMarkedLimit_of_matricial {n : ℕ} (hn : 3 ≤ n) (hS1 : (1 : R) ∈ S)
    (hS : Subring.closure (S : Set R) = ⊤) (h1 : ∀ k, φ k 1 = 1)
    (hgen : ∀ k, Subring.closure (φ k '' (S : Set R)) = ⊤)
    (hev : ∀ r s : R, ∀ᶠ k in atTop, φ k (r + s) = φ k r + φ k s ∧ φ k (r * s) = φ k r * φ k s)
    (hpos : ∀ᶠ k in atTop, 0 < N k) [IsSimpleGroup ↥(elementaryGroup (Fin n) R)] :
    IsMarkedLimit (rootMarking n (Subtype.val : ↥S → R))
      (fun k => rootMarking n (fun s : ↥S => φ k s)) := by
  have hadd : ∀ r s : R, ∀ᶠ k in atTop, φ k (r + s) = φ k r + φ k s :=
    fun r s => (hev r s).mono fun _ h => h.1
  have hmul : ∀ r s : R, ∀ᶠ k in atTop, φ k (r * s) = φ k r * φ k s :=
    fun r s => (hev r s).mono fun _ h => h.2
  refine ⟨?_, fun k => ?_, fun w => ?_⟩
  · refine closure_range_rootMarking_eq_top hn _ ⟨⟨1, hS1⟩, rfl⟩ ?_
    rw [Subtype.range_coe_subtype]
    exact hS
  · refine closure_range_rootMarking_eq_top hn _ ⟨⟨1, hS1⟩, h1 k⟩ ?_
    have hr : Set.range (fun s : ↥S => φ k s) = φ k '' (S : Set R) := by
      ext y
      constructor
      · rintro ⟨s, rfl⟩
        exact ⟨s, s.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [hr]
    exact hgen k
  · have h2 : (1 + 1 : R) = 0 :=
      one_add_one_eq_zero_of_matricial N φ (n := n) (by omega) h1 hadd hmul hpos
    letI : Module (ZMod 2) R := AddCommGroup.zmodModule (n := 2) fun x => by
      rw [two_nsmul, ← one_mul x, ← add_mul, h2, zero_mul]
    letI : Algebra (ZMod 2) R := ZMod.algebraOfModule 2 R
    have hletter : ∀ b : ↥S, ∀ᶠ k in atTop,
        φ k (piLetters S (FreeAlgebra.ι (ZMod 2) b)) = rhoLetters S N φ k (FreeAlgebra.ι (ZMod 2) b) :=
      fun b => Eventually.of_forall fun k => by rw [piLetters_ι, rhoLetters_ι]
    have hs : rootMarking n (Subtype.val : ↥S → R) =
        fun p => elementaryGroupMap (piLetters S)
          (rootMarking n (fun s : ↥S => FreeAlgebra.ι (ZMod 2) s) p) := by
      funext p
      apply Subtype.ext
      show elementaryUnit p.1.1.1 p.1.1.2 p.1.2 (p.2 : R) =
        elementaryMatrixUnitMap (piLetters S)
          (elementaryUnit p.1.1.1 p.1.1.2 p.1.2 (FreeAlgebra.ι (ZMod 2) p.2))
      rw [elementaryMatrixUnitMap_elementaryUnit, piLetters_ι]
    have hσ : ∀ k, rootMarking n (fun s : ↥S => φ k s) =
        fun p => elementaryGroupMap (rhoLetters S N φ k)
          (rootMarking n (fun s : ↥S => FreeAlgebra.ι (ZMod 2) s) p) := by
      intro k
      funext p
      apply Subtype.ext
      show elementaryUnit p.1.1.1 p.1.1.2 p.1.2 (φ k p.2) =
        elementaryMatrixUnitMap (rhoLetters S N φ k)
          (elementaryUnit p.1.1.1 p.1.1.2 p.1.2 (FreeAlgebra.ι (ZMod 2) p.2))
      rw [elementaryMatrixUnitMap_elementaryUnit, rhoLetters_ι]
    set W := FreeGroup.lift (rootMarking n (fun s : ↥S => FreeAlgebra.ι (ZMod 2) s)) w
    set A : Matrix (Fin n) (Fin n) (FreeAlgebra (ZMod 2) ↥S) :=
      (((W : ↥(elementaryGroup (Fin n) (FreeAlgebra (ZMod 2) ↥S))) :
        (Matrix (Fin n) (Fin n) (FreeAlgebra (ZMod 2) ↥S))ˣ) :
          Matrix (Fin n) (Fin n) (FreeAlgebra (ZMod 2) ↥S))
    have hLs : FreeGroup.lift (rootMarking n (Subtype.val : ↥S → R)) w =
        elementaryGroupMap (piLetters S) W := by
      rw [hs]
      exact lift_comp_hom (elementaryGroupMap (piLetters S)) _ w
    have hLσ : ∀ k, FreeGroup.lift (rootMarking n (fun s : ↥S => φ k s)) w =
        elementaryGroupMap (rhoLetters S N φ k) W := by
      intro k
      rw [hσ k]
      exact lift_comp_hom (elementaryGroupMap (rhoLetters S N φ k)) _ w
    have hsA : FreeGroup.lift (rootMarking n (Subtype.val : ↥S → R)) w = 1 ↔
        (piLetters S).mapMatrix A = 1 := by
      rw [hLs]
      constructor
      · intro h
        exact congrArg (fun z : ↥(elementaryGroup (Fin n) R) =>
          ((z : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R)) h
      · intro h
        exact Subtype.ext (Units.ext h)
    have hσA : ∀ k, FreeGroup.lift (rootMarking n (fun s : ↥S => φ k s)) w = 1 ↔
        (rhoLetters S N φ k).mapMatrix A = 1 := by
      intro k
      rw [hLσ k]
      constructor
      · intro h
        exact congrArg
          (fun z : ↥(elementaryGroup (Fin n) (Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))) =>
            ((z : (Matrix (Fin n) (Fin n) (Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)))ˣ) :
              Matrix (Fin n) (Fin n) (Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)))) h
      · intro h
        exact Subtype.ext (Units.ext h)
    by_cases hw : FreeGroup.lift (rootMarking n (Subtype.val : ↥S → R)) w = 1
    · filter_upwards [eventually_mapMatrix_eq_one φ (piLetters S) (rhoLetters S N φ) h1 hadd hmul
        hletter A (hsA.1 hw)] with k hk
      exact ⟨fun _ => hw, fun _ => (hσA k).2 hk⟩
    · have hne : ∀ᶠ k in atTop, ¬ (rhoLetters S N φ k).mapMatrix A = 1 := by
        by_contra hfreq
        have hfr : ∃ᶠ k in atTop, (rhoLetters S N φ k).mapMatrix A = 1 :=
          (not_eventually.1 hfreq).mono fun _ hk => not_not.1 hk
        haveI := frequently_iff_neBot.1 hfr
        set u := Ultrafilter.of (atTop ⊓ 𝓟 {k | (rhoLetters S N φ k).mapMatrix A = 1})
        have hu : (u : Filter ℕ) ≤ atTop := (Ultrafilter.of_le _).trans inf_le_left
        have huA : ∀ᶠ k in (u : Filter ℕ), (rhoLetters S N φ k).mapMatrix A = 1 :=
          le_principal_iff.1 ((Ultrafilter.of_le _).trans inf_le_right)
        apply hw
        refine eq_one_of_ultraMap_eq_one φ hu h1 hadd hmul (nontrivial_matrix_eventually N hpos)
          (by omega) _ ?_
        rw [hLs]
        refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
        have hij : ∀ᶠ k in (u : Filter ℕ),
            φ k (piLetters S (A i j)) = (1 : Matrix (Fin n) (Fin n)
              (Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))) i j :=
          (huA.and ((eventually_map_comp_eq φ (piLetters S) (rhoLetters S N φ) h1 hadd hmul
            hletter (A i j)).filter_mono hu)).mono fun k h => by
              rw [h.2]
              exact congrFun (congrFun h.1 i) j
        show ((fun k => φ k (piLetters S (A i j)) : ∀ k, Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)) :
            (ultraCon (u : Filter ℕ) (fun k => Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))).Quotient) =
          (1 : Matrix (Fin n) (Fin n)
            (ultraCon (u : Filter ℕ) (fun k => Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))).Quotient) i j
        rw [Matrix.one_apply]
        split_ifs with hij'
        · show ((fun k => φ k (piLetters S (A i j)) : ∀ k, Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)) :
              (ultraCon (u : Filter ℕ) (fun k => Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))).Quotient) =
            ((fun _ => 1 : ∀ k, Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)) :
              (ultraCon (u : Filter ℕ) (fun k => Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))).Quotient)
          exact (RingCon.eq (c := ultraCon (u : Filter ℕ)
            (fun k => Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)))).2
            (hij.mono fun k hk => by
              show φ k (piLetters S (A i j)) = 1
              rw [hk, Matrix.one_apply, if_pos hij'])
        · show ((fun k => φ k (piLetters S (A i j)) : ∀ k, Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)) :
              (ultraCon (u : Filter ℕ) (fun k => Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))).Quotient) =
            ((fun _ => 0 : ∀ k, Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)) :
              (ultraCon (u : Filter ℕ) (fun k => Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))).Quotient)
          exact (RingCon.eq (c := ultraCon (u : Filter ℕ)
            (fun k => Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)))).2
            (hij.mono fun k hk => by
              show φ k (piLetters S (A i j)) = 0
              rw [hk, Matrix.one_apply, if_neg hij'])
      filter_upwards [hne] with k hk
      exact ⟨fun h => absurd ((hσA k).1 h) hk, fun h => absurd h hw⟩

end Matricial

end SimpleKazhdanSofic

end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.one_add_one_eq_zero_of_matricial
#audit_axioms GroupApproximation.SimpleKazhdanSofic.isMarkedLimit_of_matricial

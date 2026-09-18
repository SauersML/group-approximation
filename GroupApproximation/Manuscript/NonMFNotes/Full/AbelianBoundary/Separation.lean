import GroupApproximation.Manuscript.NonMFNotes.Full.AbelianBoundary.Corona
import GroupApproximation.Algebra.FiniteResidual
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Algebra.Group.Torsion
import Mathlib.Data.Finite.Prod
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import GroupApproximation.Meta.AxiomGuard

/-!
# Separating lamp configurations in the corona

Manuscript `non_mf_group_notes.tex`, `thm:notes-abelian-boundary` (tex lines 2078--2160),
torsion-free half (tex lines 2134--2150).  Fix a nontrivial configuration
`b : Lamp A (G ⧸ H)` and a site `x₀` with `b x₀ = a ≠ 0`.

* `A` is torsion-free, so `ℤ a ≅ ℤ`.  `ℝ` is divisible, hence injective as a `ℤ`-module, so
  some `θ : A →+ ℝ` has `θ a = π` (`exists_hom_real_eq_pi`).
* `G` is residually finite, so for each `n` there is a finite-index `N n` avoiding the finite
  set `badSet` of elements that could make two supports overlap (`exists_avoiding_family`).
* Then the phase of `D_n(b)` at the base coset is exactly `π` (`phase_eq_pi`).  So
  `‖D_n(b) - 1‖ ≥ 2` for every `n`, and the class of `b` in the corona is nontrivial
  (`coronaLamp_ne_one`, `exists_corona_separating`).
-/

namespace GroupApproximation.Full.NN06

open Matrix

noncomputable section

variable {G : Type} [Group G] {H : Subgroup G} {A : Type} [AddCommGroup A]

/-- A nonzero element of a torsion-free abelian group is sent to `π` by some additive
character to `ℝ` (tex line 2140). -/
theorem exists_hom_real_eq_pi [IsAddTorsionFree A] {a : A} (ha : a ≠ 0) :
    ∃ θ : A →+ ℝ, θ a = Real.pi := by
  have hinj : Function.Injective (zmultiplesHom A a) :=
    (injective_iff_map_eq_zero (zmultiplesHom A a)).mpr fun n hn => by
      have hn' : n • a = 0 := hn
      exact (IsAddTorsionFree.zsmul_eq_zero_iff_left ha).mp hn'
  obtain ⟨θ, hθ⟩ := Module.Baer.extension_property_addMonoidHom (Module.Baer.of_divisible ℝ)
    (zmultiplesHom A a) hinj (zmultiplesHom ℝ Real.pi)
  refine ⟨θ, ?_⟩
  have h : θ (zmultiplesHom A a 1) = zmultiplesHom ℝ Real.pi 1 := DFunLike.congr_fun hθ 1
  rwa [zmultiplesHom_apply, zmultiplesHom_apply, one_zsmul, one_zsmul] at h

/-- In a residually finite group, a finite set not containing `1` is avoided by some
finite-index subgroup. -/
theorem exists_finiteIndex_avoid (hG : IsResiduallyFinite G) (S : Finset G)
    (h1 : (1 : G) ∉ S) : ∃ L : Subgroup G, L.FiniteIndex ∧ ∀ s ∈ S, s ∉ L := by
  classical
  revert h1
  refine Finset.induction_on S ?_ ?_
  · intro _
    exact ⟨⊤, inferInstance, fun s hs => absurd hs (Finset.notMem_empty s)⟩
  · intro a T _ ih h1
    obtain ⟨L, hL, hLT⟩ := ih fun h => h1 (Finset.mem_insert_of_mem h)
    have ha1 : a ≠ 1 := by
      rintro rfl
      exact h1 (Finset.mem_insert_self 1 T)
    obtain ⟨M, hM, haM⟩ := isResiduallyFinite_iff.mp hG a ha1
    refine ⟨L ⊓ M, inferInstance, fun s hs hsLM => ?_⟩
    rcases Finset.mem_insert.mp hs with rfl | hsT
    · exact haM (Subgroup.mem_inf.mp hsLM).2
    · exact hLT s hsT (Subgroup.mem_inf.mp hsLM).1

/-- The finite set of elements `c⁻¹ x.out⁻¹ x₀.out`, where `x ≠ x₀` is in the support of `b`
and `c` is in the stage-`n` ball.  A finite-index subgroup avoiding it keeps the bumps
of the other sites away from the base coset. -/
def badSet (e : ℕ → G) (b : Lamp (Multiplicative A) (G ⧸ H)) (x₀ : G ⧸ H) (n : ℕ) : Set G :=
  Set.image2 (fun (x : G ⧸ H) (c : G) => c⁻¹ * (x.out⁻¹ * x₀.out))
    {x : G ⧸ H | b.toFun x ≠ 1 ∧ x ≠ x₀} (ball e n n)

theorem badSet_finite (e : ℕ → G) (b : Lamp (Multiplicative A) (G ⧸ H)) (x₀ : G ⧸ H)
    (n : ℕ) : (badSet e b x₀ n).Finite := by
  have hsupp : {x : G ⧸ H | b.toFun x ≠ 1 ∧ x ≠ x₀}.Finite :=
    (b.2 : {x : G ⧸ H | (b : G ⧸ H → Multiplicative A) x ≠ 1}.Finite).subset
      fun _ hx => hx.1
  exact Set.Finite.image2 (fun (x : G ⧸ H) (c : G) => c⁻¹ * (x.out⁻¹ * x₀.out)) hsupp
    (ball_finite e n n)

theorem one_notMem_badSet (e : ℕ → G) (he : ∀ j, e j ∈ H)
    (b : Lamp (Multiplicative A) (G ⧸ H)) (x₀ : G ⧸ H) (n : ℕ) :
    (1 : G) ∉ badSet e b x₀ n := by
  rintro ⟨x, ⟨_, hxne⟩, c, hc, hcx⟩
  have hcx' : c⁻¹ * (x.out⁻¹ * x₀.out) = 1 := hcx
  have hcH : c ∈ H := ball_subset e he n n hc
  have h2 : x₀.out = x.out * c :=
    calc x₀.out = x.out * c * (c⁻¹ * (x.out⁻¹ * x₀.out)) := by group
      _ = x.out * c := by rw [hcx', mul_one]
  have h3 : (QuotientGroup.mk (x.out * c) : G ⧸ H) = x :=
    (QuotientGroup.mk_mul_of_mem x.out hcH).trans (QuotientGroup.out_eq' x)
  exact hxne (h3.symm.trans (by rw [← h2, QuotientGroup.out_eq']))

/-- **The phase at the base coset is `π`** (tex lines 2141--2146).  Only the site `x₀`
contributes there, and it contributes `θ(b x₀) f_n(1) = π`. -/
theorem phase_eq_pi (θ : A →+ ℝ) (e : ℕ → G) {b : Lamp (Multiplicative A) (G ⧸ H)}
    {x₀ : G ⧸ H} (hθ : θ (Multiplicative.toAdd (b.toFun x₀)) = Real.pi) (n : ℕ)
    (K : Subgroup G) (hK : ∀ s ∈ badSet e b x₀ n, s ∉ K) :
    phase θ e n K b (QuotientGroup.mk x₀.out) = Real.pi := by
  have hzero : ∀ x : G ⧸ H, x ≠ x₀ →
      θ (Multiplicative.toAdd (b.toFun x)) *
        bump e n K (x.out⁻¹ • (QuotientGroup.mk x₀.out : G ⧸ K)) = 0 := by
    intro x hx
    by_cases hb : b.toFun x = 1
    · rw [hb, toAdd_one, map_zero, zero_mul]
    · refine mul_eq_zero_of_right _ (bump_eq_zero (n := n) (K := K)
        (y := x.out⁻¹ • (QuotientGroup.mk x₀.out : G ⧸ K)) e fun c hc hcy => ?_)
      have hcy' : (QuotientGroup.mk c : G ⧸ K) = QuotientGroup.mk (x.out⁻¹ * x₀.out) := hcy
      have hmem : c⁻¹ * (x.out⁻¹ * x₀.out) ∈ badSet e b x₀ n :=
        Set.mem_image2_of_mem (f := fun (x : G ⧸ H) (c : G) => c⁻¹ * (x.out⁻¹ * x₀.out))
          (s := {x : G ⧸ H | b.toFun x ≠ 1 ∧ x ≠ x₀}) (t := ball e n n)
          (show b.toFun x ≠ 1 ∧ x ≠ x₀ from ⟨hb, hx⟩) hc
      exact hK _ hmem (QuotientGroup.eq.mp hcy')
  show ∑ᶠ x : G ⧸ H, θ (Multiplicative.toAdd (b.toFun x)) *
      bump e n K (x.out⁻¹ • (QuotientGroup.mk x₀.out : G ⧸ K)) = Real.pi
  refine (finsum_eq_single _ x₀ hzero).trans ?_
  have hbase : x₀.out⁻¹ • (QuotientGroup.mk x₀.out : G ⧸ K) = QuotientGroup.mk (1 : G) := by
    show (QuotientGroup.mk (x₀.out⁻¹ * x₀.out) : G ⧸ K) = QuotientGroup.mk (1 : G)
    rw [inv_mul_cancel]
  show θ (Multiplicative.toAdd (b.toFun x₀)) *
      bump e n K (x₀.out⁻¹ • (QuotientGroup.mk x₀.out : G ⧸ K)) = Real.pi
  rw [hbase, bump_one, mul_one, hθ]

/-- **Nontriviality in the corona** (tex lines 2146--2150): if every `N n` avoids the bad
set and `θ(b x₀) = π`, then `‖D_n(b) - 1‖ ≥ 2` for all `n`, so `[D_n(b)] ≠ 1`. -/
theorem coronaLamp_ne_one (θ : A →+ ℝ) (e : ℕ → G) (N : ℕ → Subgroup G)
    [∀ n, (N n).FiniteIndex] {b : Lamp (Multiplicative A) (G ⧸ H)} {x₀ : G ⧸ H}
    (hθ : θ (Multiplicative.toAdd (b.toFun x₀)) = Real.pi)
    (hN : ∀ n, ∀ s ∈ badSet e b x₀ n, s ∉ N n) :
    coronaLamp θ e N b ≠ 1 := by
  intro h1
  have h1' : (QuotientGroup.mk (fun n => lampRep θ e n (N n) b) :
      NormMatrixCoronaUnitary (quotModels N)) = 1 := h1
  have hmem : (fun n => lampRep θ e n (N n) b) ∈ nullCofiniteOpSubgroup (quotModels N) :=
    (QuotientGroup.eq_one_iff (N := nullCofiniteOpSubgroup (quotModels N))
      (fun n => lampRep θ e n (N n) b)).mp h1'
  have hnull : IsNullCofiniteOpSeq (quotModels N) (fun n => lampRep θ e n (N n) b) := hmem
  obtain ⟨n, hn⟩ := (hnull 1 one_pos).exists
  have h2 : 2 ≤ opLength (quotModels N n)
      (diagUnitary (quotModels N n) (phase θ e n (N n) b)) :=
    two_le_opLength_diag (quotModels N n) (v := phase θ e n (N n) b)
      (QuotientGroup.mk x₀.out : G ⧸ N n) (phase_eq_pi θ e hθ n (N n) (hN n))
  have h4 : opLength (quotModels N n)
      (diagUnitary (quotModels N n) (phase θ e n (N n) b)) < 1 := hn
  linarith

/-- A family of finite-index subgroups avoiding every bad set. -/
theorem exists_avoiding_family (hG : IsResiduallyFinite G) (e : ℕ → G) (he : ∀ j, e j ∈ H)
    (b : Lamp (Multiplicative A) (G ⧸ H)) (x₀ : G ⧸ H) :
    ∃ N : ℕ → Subgroup G, (∀ n, (N n).FiniteIndex) ∧
      ∀ n, ∀ s ∈ badSet e b x₀ n, s ∉ N n := by
  have h : ∀ n : ℕ, ∃ L : Subgroup G, L.FiniteIndex ∧ ∀ s ∈ badSet e b x₀ n, s ∉ L := by
    intro n
    obtain ⟨L, hL, hLS⟩ := exists_finiteIndex_avoid hG (badSet_finite e b x₀ n).toFinset
      fun h1 => one_notMem_badSet e he b x₀ n ((badSet_finite e b x₀ n).mem_toFinset.mp h1)
    exact ⟨L, hL, fun s hs => hLS s ((badSet_finite e b x₀ n).mem_toFinset.mpr hs)⟩
  choose N hN hNS using h
  exact ⟨N, hN, hNS⟩

/-- **Separation of lamp configurations** (tex lines 2134--2150).  Let `G` be residually
finite, `A` torsion-free, and `e` an enumeration of `H`.  Then every nontrivial configuration
`b` survives some corona representation of `Lamp A (G ⧸ H) ⋊ G`. -/
theorem exists_corona_separating [IsAddTorsionFree A] (hG : IsResiduallyFinite G)
    (e : ℕ → G) (he : ∀ j, e j ∈ H) (hsurj : ∀ h ∈ H, ∃ j, e j = h)
    {b : Lamp (Multiplicative A) (G ⧸ H)} (hb : b ≠ 1) :
    ∃ X : ℕ → FiniteModel, (∀ n, 0 < Fintype.card (X n)) ∧
      ∃ rho : Wreath (Multiplicative A) G (G ⧸ H) →* NormMatrixCoronaUnitary X,
        rho (SemidirectProduct.inl b) ≠ 1 := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : G ⧸ H, b.toFun x₀ ≠ 1 := by
    by_contra hall
    refine hb (Lamp.ext fun x => ?_)
    rw [Lamp.one_apply]
    by_contra hx
    exact hall ⟨x, hx⟩
  have ha₀ : Multiplicative.toAdd (b.toFun x₀) ≠ 0 := fun h => hx₀ (toAdd_eq_zero.mp h)
  obtain ⟨θ, hθ⟩ := exists_hom_real_eq_pi ha₀
  obtain ⟨N, hN, hNS⟩ := exists_avoiding_family hG e he b x₀
  refine ⟨quotModels N, quotModels_card_pos N, coronaHom θ e N hsurj, ?_⟩
  exact fun h => coronaLamp_ne_one θ e N hθ hNS ((coronaHom_inl θ e N hsurj b).symm.trans h)

end

#audit_axioms exists_hom_real_eq_pi
#audit_axioms exists_finiteIndex_avoid
#audit_axioms one_notMem_badSet
#audit_axioms phase_eq_pi
#audit_axioms coronaLamp_ne_one
#audit_axioms exists_corona_separating

end GroupApproximation.Full.NN06

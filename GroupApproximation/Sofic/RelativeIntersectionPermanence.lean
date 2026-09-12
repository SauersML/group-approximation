import GroupApproximation.Sofic.IntersectionReduction
import Mathlib.Algebra.Group.PUnit

/-!
# Intersection permanence for relative quotient approximations

This file isolates the exact algebra behind intersection closure.  A group
property is packaged together with proofs that it passes to injective
subgroups and finite products.  Given two such properties, a relative
approximation witness consists of decreasing ambient subgroups and decreasing
ambient-normal kernels, with the two corresponding quotient properties.

The diagonal construction combines countably many witnesses.  No particular
approximation property and no external permanence theorem is assumed here:
all closure data are explicit fields of `SubproductClosedGroupProperty`.
-/

namespace GroupApproximation

/-- A property of groups equipped with its two exact permanence operations
used by diagonal intersection arguments. -/
structure SubproductClosedGroupProperty where
  holds : ∀ (G : Type) [Group G], Prop
  trivial : holds PUnit
  of_injective : ∀ {A B : Type} [Group A] [Group B]
    (f : A →* B), Function.Injective f → holds B → holds A
  finite_pi : ∀ {I : Type} [Fintype I] {A : I → Type}
    [∀ i, Group (A i)], (∀ i, holds (A i)) → holds (∀ i, A i)

/-- A subgroup bundled with a proof that it is normal in the fixed ambient
group. -/
structure AmbientNormalSubgroup (G : Type) [Group G] where
  toSubgroup : Subgroup G
  normal : toSubgroup.Normal

instance {G : Type} [Group G] (N : AmbientNormalSubgroup G) :
    N.toSubgroup.Normal := N.normal

noncomputable local instance relativeIInfNormal
    {G : Type} [Group G] {I : Type} (N : I → Subgroup G)
    [∀ i, (N i).Normal] : (⨅ i, N i).Normal :=
  Subgroup.normal_iInf_normal fun _ ↦ inferInstance

noncomputable local instance relativeNormalSubgroupOf
    {G : Type} [Group G] (N K : Subgroup G) [N.Normal] :
    (N.subgroupOf K).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer (by
    rw [N.normalizer_eq_top]
    exact le_top)

/-- A decreasing relative quotient approximation of `K ≤ G`. -/
structure RelativeQuotientApproximation
    {G : Type} [Group G]
    (C D : SubproductClosedGroupProperty) (K : Subgroup G) where
  upper : ℕ → Subgroup G
  lower : ℕ → AmbientNormalSubgroup G
  lower_le_upper : ∀ n, (lower n).toSubgroup ≤ upper n
  upper_antitone : Antitone upper
  lower_antitone : Antitone (fun n ↦ (lower n).toSubgroup)
  upper_iInf : ⨅ n, upper n = K
  ambient_quotient : ∀ n, C.holds (G ⧸ (lower n).toSubgroup)
  local_quotient : ∀ n,
    D.holds (↑(upper n) ⧸ (lower n).toSubgroup.subgroupOf (upper n))

/-- Existence of a relative quotient approximation. -/
def HasRelativeQuotientApproximation
    {G : Type} [Group G]
    (C D : SubproductClosedGroupProperty) (K : Subgroup G) : Prop :=
  Nonempty (RelativeQuotientApproximation C D K)

namespace RelativeQuotientApproximation

variable {G : Type} [Group G]
variable {C D : SubproductClosedGroupProperty}

/-- The ambient group itself has the constant relative approximation. -/
noncomputable def top (C D : SubproductClosedGroupProperty) :
    RelativeQuotientApproximation C D (⊤ : Subgroup G) where
  upper := fun _ ↦ ⊤
  lower := fun _ ↦ ⟨⊤, inferInstance⟩
  lower_le_upper := fun _ ↦ le_rfl
  upper_antitone := antitone_const
  lower_antitone := antitone_const
  upper_iInf := iInf_const
  ambient_quotient := fun _ ↦
    C.of_injective (1 : (G ⧸ (⊤ : Subgroup G)) →* PUnit)
      (fun x y _ ↦ by
        refine QuotientGroup.induction_on x fun gx ↦ ?_
        refine QuotientGroup.induction_on y fun gy ↦ ?_
        rw [QuotientGroup.eq]
        simp) C.trivial
  local_quotient := fun _ ↦
    D.of_injective
      (1 : (↑(⊤ : Subgroup G) ⧸
        (⊤ : Subgroup G).subgroupOf ⊤) →* PUnit)
      (fun x y _ ↦ by
        refine QuotientGroup.induction_on x fun gx ↦ ?_
        refine QuotientGroup.induction_on y fun gy ↦ ?_
        rw [QuotientGroup.eq]
        simp) D.trivial

/-- The finite diagonal upper subgroup at stage `n`. -/
noncomputable def diagonalUpper
    {K : ℕ → Subgroup G}
    (W : ∀ j, RelativeQuotientApproximation C D (K j)) (n : ℕ) :
    Subgroup G :=
  ⨅ j : Fin (n + 1), (W j).upper n

/-- The finite diagonal lower subgroup at stage `n`. -/
noncomputable def diagonalLower
    {K : ℕ → Subgroup G}
    (W : ∀ j, RelativeQuotientApproximation C D (K j)) (n : ℕ) :
    AmbientNormalSubgroup G where
  toSubgroup := ⨅ j : Fin (n + 1), ((W j).lower n).toSubgroup
  normal := Subgroup.normal_iInf_normal fun _ ↦ inferInstance

theorem diagonalLower_le_diagonalUpper
    {K : ℕ → Subgroup G}
    (W : ∀ j, RelativeQuotientApproximation C D (K j)) (n : ℕ) :
    (diagonalLower W n).toSubgroup ≤ diagonalUpper W n := by
  intro g hg
  change g ∈ ⨅ j : Fin (n + 1), ((W j).lower n).toSubgroup at hg
  change g ∈ ⨅ j : Fin (n + 1), (W j).upper n
  rw [Subgroup.mem_iInf] at hg ⊢
  intro j
  exact (W j).lower_le_upper n (hg j)

theorem diagonalUpper_antitone
    {K : ℕ → Subgroup G}
    (W : ∀ j, RelativeQuotientApproximation C D (K j)) :
    Antitone (diagonalUpper W) := by
  intro a b hab g hg
  change g ∈ ⨅ j : Fin (b + 1), (W j).upper b at hg
  change g ∈ ⨅ j : Fin (a + 1), (W j).upper a
  rw [Subgroup.mem_iInf] at hg ⊢
  intro j
  let j' : Fin (b + 1) := ⟨j, by omega⟩
  exact (W j).upper_antitone hab (hg j')

theorem diagonalLower_antitone
    {K : ℕ → Subgroup G}
    (W : ∀ j, RelativeQuotientApproximation C D (K j)) :
    Antitone (fun n ↦ (diagonalLower W n).toSubgroup) := by
  intro a b hab g hg
  change g ∈ ⨅ j : Fin (b + 1), ((W j).lower b).toSubgroup at hg
  change g ∈ ⨅ j : Fin (a + 1), ((W j).lower a).toSubgroup
  rw [Subgroup.mem_iInf] at hg ⊢
  intro j
  let j' : Fin (b + 1) := ⟨j, by omega⟩
  exact (W j).lower_antitone hab (hg j')

theorem iInf_diagonalUpper
    {K : ℕ → Subgroup G}
    (W : ∀ j, RelativeQuotientApproximation C D (K j)) :
    ⨅ n, diagonalUpper W n = ⨅ j, K j := by
  ext g
  rw [Subgroup.mem_iInf, Subgroup.mem_iInf]
  constructor
  · intro hg j
    have hall : ∀ n, g ∈ (W j).upper n := by
      intro n
      let m := max n j
      have hjm : j < m + 1 := by dsimp [m]; omega
      have hm : g ∈ (W j).upper m := by
        have hm' := hg m
        change g ∈ ⨅ k : Fin (m + 1), (W k).upper m at hm'
        exact (Subgroup.mem_iInf.mp hm') ⟨j, hjm⟩
      exact (W j).upper_antitone (Nat.le_max_left n j) hm
    rw [← (W j).upper_iInf]
    simpa only [Subgroup.mem_iInf] using hall
  · intro hg n
    change g ∈ ⨅ j : Fin (n + 1), (W j).upper n
    rw [Subgroup.mem_iInf]
    intro j
    have hj : g ∈ K j := hg j
    rw [← (W j).upper_iInf] at hj
    exact (Subgroup.mem_iInf.mp hj) n

theorem diagonal_ambient_quotient
    {K : ℕ → Subgroup G}
    (W : ∀ j, RelativeQuotientApproximation C D (K j)) (n : ℕ) :
    C.holds (G ⧸ (diagonalLower W n).toSubgroup) := by
  let N : Fin (n + 1) → Subgroup G :=
    fun j ↦ ((W j).lower n).toSubgroup
  have hfactor (j : Fin (n + 1)) : C.holds (G ⧸ N j) := by
    change C.holds (G ⧸ ((W (j : ℕ)).lower n).toSubgroup)
    exact (W (j : ℕ)).ambient_quotient n
  have hprod : C.holds (∀ j : Fin (n + 1), G ⧸ N j) :=
    C.finite_pi (I := Fin (n + 1)) (A := fun j ↦ G ⧸ N j) hfactor
  change C.holds (G ⧸ ⨅ j, N j)
  exact C.of_injective (Subgroup.quotientIInfHom N)
    (Subgroup.quotientIInfHom_injective N) hprod

theorem diagonal_local_quotient
    {K : ℕ → Subgroup G}
    (W : ∀ j, RelativeQuotientApproximation C D (K j)) (n : ℕ) :
    D.holds (↑(diagonalUpper W n) ⧸
      (diagonalLower W n).toSubgroup.subgroupOf (diagonalUpper W n)) := by
  let N : Fin (n + 1) → Subgroup G :=
    fun j ↦ ((W j).lower n).toSubgroup
  let P : Fin (n + 1) → Subgroup G :=
    fun j ↦ (W j).upper n
  have hfactor (j : Fin (n + 1)) :
      D.holds (↑(P j) ⧸ (N j).subgroupOf (P j)) := by
    change D.holds (↑((W (j : ℕ)).upper n) ⧸
      ((W (j : ℕ)).lower n).toSubgroup.subgroupOf
        ((W (j : ℕ)).upper n))
    exact (W (j : ℕ)).local_quotient n
  have hprod : D.holds
      (∀ j, ↑(P j) ⧸ (N j).subgroupOf (P j)) :=
    D.finite_pi (I := Fin (n + 1))
      (A := fun j ↦ ↑(P j) ⧸ (N j).subgroupOf (P j)) hfactor
  change D.holds (↑(⨅ j, P j) ⧸
    Subgroup.subgroupOf (⨅ j, N j) (⨅ j, P j))
  exact D.of_injective (Subgroup.quotientSubgroupIInfHom N P)
    (Subgroup.quotientSubgroupIInfHom_injective N P) hprod

/-- Countably many relative quotient approximations combine by the finite
diagonal construction. -/
noncomputable def diagonal
    {K : ℕ → Subgroup G}
    (W : ∀ j, RelativeQuotientApproximation C D (K j)) :
    RelativeQuotientApproximation C D (⨅ j, K j) where
  upper := diagonalUpper W
  lower := diagonalLower W
  lower_le_upper := diagonalLower_le_diagonalUpper W
  upper_antitone := diagonalUpper_antitone W
  lower_antitone := diagonalLower_antitone W
  upper_iInf := iInf_diagonalUpper W
  ambient_quotient := diagonal_ambient_quotient W
  local_quotient := diagonal_local_quotient W

/-- Countable intersection permanence, stated at the existence level. -/
theorem hasRelativeQuotientApproximation_iInf_nat
    {K : ℕ → Subgroup G}
    (hK : ∀ j, HasRelativeQuotientApproximation C D (K j)) :
    HasRelativeQuotientApproximation C D (⨅ j, K j) := by
  classical
  let W : ∀ j, RelativeQuotientApproximation C D (K j) :=
    fun j ↦ Classical.choice (hK j)
  exact ⟨diagonal W⟩

/-- Intersection permanence over an arbitrary countable index type. -/
theorem hasRelativeQuotientApproximation_iInf_countable
    {I : Type} [Countable I] {K : I → Subgroup G}
    (hK : ∀ i, HasRelativeQuotientApproximation C D (K i)) :
    HasRelativeQuotientApproximation C D (⨅ i, K i) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hI =>
      letI := hI
      simpa only [iInf_of_empty] using
        (show HasRelativeQuotientApproximation C D (⊤ : Subgroup G) from
          ⟨top C D⟩)
  | inr hI =>
      letI := hI
      obtain ⟨e, he⟩ := exists_surjective_nat I
      have hnat := hasRelativeQuotientApproximation_iInf_nat
        (K := fun n ↦ K (e n)) (fun n ↦ hK (e n))
      have heq : ⨅ n, K (e n) = ⨅ i, K i := by
        ext g
        simp only [Subgroup.mem_iInf]
        constructor
        · intro hg i
          obtain ⟨n, rfl⟩ := he i
          exact hg n
        · intro hg n
          exact hg (e n)
      simpa only [heq] using hnat

/-- Arbitrary intersection permanence in a countable ambient group. -/
theorem hasRelativeQuotientApproximation_iInf
    [Countable G] {I : Type} {K : I → Subgroup G}
    (hK : ∀ i, HasRelativeQuotientApproximation C D (K i)) :
    HasRelativeQuotientApproximation C D (⨅ i, K i) := by
  classical
  obtain ⟨J, hJ, hJiInf⟩ :=
    Subgroup.exists_countable_subfamily_iInf_eq K
  letI : Countable J := hJ.to_subtype
  have hcountable := hasRelativeQuotientApproximation_iInf_countable
    (K := fun j : J ↦ K j.1) (fun j ↦ hK j.1)
  simpa only [hJiInf] using hcountable

end RelativeQuotientApproximation
end GroupApproximation

import GroupApproximation.Algebra.PermutationalWreath
import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Simple lamps: one relation generates the whole invisible kernel

**Section 51** of the dossier.  When the lamp group is nonabelian simple and the
acting group is transitive on the sites, the entire lamp subgroup of the
permutational wreath product is the normal closure of a *single* nontrivial
one-site lamp.

Two ingredients:

* `Lamp.mem_closure_singles` — every finitely supported configuration is a
  product of one-site lamps.  The induction peels one site off the support at a
  time.
* `lamp_le_normalClosure_single` — simplicity of the lamp group makes the normal
  closure meet the one-site copy at the base site in all of `K`, and
  transitivity of the site action spreads that across every site.

The consequence recorded in the dossier is that adding the single relation
`r = 1` collapses the wreath product onto the acting group.
-/

namespace GroupApproximation

universe u v w

namespace Lamp

variable {K : Type u} [Group K] {X : Type v}

/-- The (finite) support of a lamp configuration. -/
noncomputable def support (f : Lamp K X) : Finset X :=
  (f.2 : {x : X | (f : X → K) x ≠ 1}.Finite).toFinset

theorem mem_support {f : Lamp K X} {x : X} :
    x ∈ f.support ↔ f.toFun x ≠ 1 :=
  Set.Finite.mem_toFinset _

theorem support_eq_empty_iff {f : Lamp K X} : f.support = ∅ ↔ f = 1 := by
  constructor
  · intro h
    refine ext fun x => ?_
    by_contra hx
    have hmem : x ∈ f.support := mem_support.mpr hx
    rw [h] at hmem
    simp at hmem
  · rintro rfl
    refine Finset.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    exact (mem_support.mp hx) rfl

variable [DecidableEq X]

/-- Peeling one site off a configuration. -/
theorem support_mul_single_inv_subset (f : Lamp K X) (x : X) :
    (f * (single x (f.toFun x))⁻¹).support ⊆ f.support.erase x := by
  intro y hy
  rw [mem_support] at hy
  have hne : y ≠ x := by
    rintro rfl
    exact hy (by rw [mul_apply, inv_apply, single_apply_self, mul_inv_cancel])
  refine Finset.mem_erase.mpr ⟨hne, mem_support.mpr ?_⟩
  intro hcon
  refine hy ?_
  rw [mul_apply, inv_apply, single_apply_of_ne hne, inv_one, mul_one, hcon]

/-- **Every configuration is a product of one-site lamps.** -/
theorem mem_closure_singles (f : Lamp K X) :
    f ∈ Subgroup.closure {g : Lamp K X | ∃ (x : X) (k : K), g = single x k} := by
  classical
  suffices h : ∀ n : ℕ, ∀ f : Lamp K X, f.support.card ≤ n →
      f ∈ Subgroup.closure {g : Lamp K X | ∃ (x : X) (k : K), g = single x k} by
    exact h f.support.card f le_rfl
  intro n
  induction n with
  | zero =>
      intro f hf
      have hempty : f.support = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hf)
      rw [support_eq_empty_iff.mp hempty]
      exact Subgroup.one_mem _
  | succ n ih =>
      intro f hf
      by_cases hempty : f.support = ∅
      · rw [support_eq_empty_iff.mp hempty]
        exact Subgroup.one_mem _
      · obtain ⟨x, hx⟩ := Finset.nonempty_of_ne_empty hempty
        have hcard : (f * (single x (f.toFun x))⁻¹).support.card ≤ n := by
          have hsub := Finset.card_le_card (support_mul_single_inv_subset f x)
          rw [Finset.card_erase_of_mem hx] at hsub
          omega
        have hrest := ih _ hcard
        have hsingle : single x (f.toFun x)
            ∈ Subgroup.closure {g : Lamp K X | ∃ (x : X) (k : K), g = single x k} :=
          Subgroup.subset_closure ⟨x, f.toFun x, rfl⟩
        have hsplit : f = (f * (single x (f.toFun x))⁻¹) * single x (f.toFun x) := by
          rw [inv_mul_cancel_right]
        rw [hsplit]
        exact Subgroup.mul_mem _ hrest hsingle

end Lamp

/-! ## The normal closure of a single lamp -/

section Simple

open SemidirectProduct

variable (K : Type u) [Group K] (G : Type w) [Group G] (X : Type v)
variable [MulAction G X] [DecidableEq X]

/-- Conjugating a one-site lamp by the acting group moves the site. -/
theorem conj_inl_single (g : G) (x : X) (k : K) :
    (inr g : Wreath K G X) * inl (Lamp.single x k) * (inr g)⁻¹
      = inl (Lamp.single (g • x) k) := by
  rw [← map_inv, ← inl_aut]
  exact congrArg inl (lampAut_single g x k)

end Simple

section SimpleClosure

open SemidirectProduct

/-- **Section 51.1.**  For a simple lamp group and a transitive site action the
whole lamp subgroup is the normal closure of one nontrivial one-site lamp. -/
theorem lamp_le_normalClosure_single {K : Type u} [Group K] {G : Type w}
    [Group G] {X : Type v} [MulAction G X] [DecidableEq X] [IsSimpleGroup K]
    (x₀ : X) (htrans : ∀ x : X, ∃ g : G, g • x₀ = x) {k₀ : K} (hk₀ : k₀ ≠ 1)
    (f : Lamp K X) :
    (inl f : Wreath K G X)
      ∈ Subgroup.normalClosure {(inl (Lamp.single x₀ k₀) : Wreath K G X)} := by
  classical
  set N : Subgroup (Wreath K G X) :=
    Subgroup.normalClosure {(inl (Lamp.single x₀ k₀) : Wreath K G X)} with hNdef
  haveI hNnormal : N.Normal := Subgroup.normalClosure_normal
  set ι : K →* Wreath K G X :=
    (inl : Lamp K X →* Wreath K G X).comp (Lamp.singleHom x₀) with hι
  -- the values realised at the base site form a normal subgroup of `K`
  set N₀ : Subgroup K := N.comap ι with hN₀
  have hk₀mem : k₀ ∈ N₀ := by
    rw [hN₀, Subgroup.mem_comap, hι]
    exact Subgroup.subset_normalClosure rfl
  haveI : N₀.Normal := by
    refine ⟨fun a ha b => ?_⟩
    rw [hN₀, Subgroup.mem_comap] at ha ⊢
    have hconj : ι (b * a * b⁻¹) = ι b * ι a * (ι b)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [hconj]
    exact hNnormal.conj_mem _ ha _
  have hNtop : N₀ = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N₀ inferInstance with h | h
    · exact absurd (h ▸ hk₀mem) (by simpa using hk₀)
    · exact h
  -- every one-site lamp lies in the normal closure
  have hsingle : ∀ (x : X) (k : K), (inl (Lamp.single x k) : Wreath K G X) ∈ N := by
    intro x k
    obtain ⟨g, rfl⟩ := htrans x
    have hbase : (inl (Lamp.single x₀ k) : Wreath K G X) ∈ N := by
      have : k ∈ N₀ := by rw [hNtop]; exact Subgroup.mem_top k
      rw [hN₀, Subgroup.mem_comap] at this
      exact this
    rw [← conj_inl_single K G X g x₀ k]
    exact hNnormal.conj_mem _ hbase _
  -- and configurations are products of one-site lamps
  have hcl : Subgroup.closure
      {g : Lamp K X | ∃ (x : X) (k : K), g = Lamp.single x k}
      ≤ N.comap (inl : Lamp K X →* Wreath K G X) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨x, k, rfl⟩
    exact hsingle x k
  exact hcl (Lamp.mem_closure_singles f)

end SimpleClosure

end GroupApproximation

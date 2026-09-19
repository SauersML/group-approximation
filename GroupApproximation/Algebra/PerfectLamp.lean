import GroupApproximation.Algebra.PermutationalWreathSimple
import GroupApproximation.Algebra.WreathSplitQuotient
import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Section 43.1: perfect lamps have no abelian shadow

Section 43.1 specialises the radical calculus to a *perfect* lamp group
`K = [K, K]`.  There the abelianization `K_ab` is trivial, the visible quotient
`P_K` of (41.2) collapses to the acting group, and (43.2) says the invisible
radical `R_K` is the **entire** lamp subgroup rather than the parity-per-height
subgroup that a general `K` leaves behind (compare 43.2, where `K = C₂` retains
exactly one bit per occupied height).

The step that is specific to perfectness, and the only one Section 43.1 adds to
Sections 41--42, is that no abelian invariant of the lamps survives.  That step
is proved here, unconditionally and with no approximation theory in sight:

* `Lamp.commutator_eq_top` -- a perfect lamp group has a perfect group of
  finitely supported configurations.  Perfectness passes to the configuration
  group one site at a time: `singleHom x` carries commutators to commutators, so
  each one-site lamp is a commutator, and the one-site lamps generate.
* `Lamp.eq_one_of_commGroup_hom`, `lampRange_le_commutator`,
  `lampRange_le_ker_of_commGroup` -- consequently every homomorphism of the
  wreath product into an abelian group kills the whole lamp subgroup.

This is the mechanism behind (43.1) `P_K = G_*`.  The remaining items 1--7 of
Theorem 43.1 are Sections 41--42 read with that identification and are already
formalised: the factorization and finite-index clauses in
`Algebra/VisibleQuotient`, the coincidence of the radicals in
`Sofic/ThreeRadicalsCoincide`, and the `Hom`-set form in
`Sofic/TargetEquivalence`.
-/

namespace GroupApproximation

universe u v w

/-- A homomorphism carries the commutator subgroup into the commutator
subgroup. -/
theorem map_commutator_le {A : Type u} [Group A] {B : Type v} [Group B]
    (f : A →* B) : (commutator A).map f ≤ commutator B := by
  rw [commutator_def, Subgroup.map_commutator]
  exact Subgroup.commutator_mono le_top le_top

namespace Lamp

variable {K : Type u} [Group K] {X : Type v} [DecidableEq X]

/-- A one-site lamp at a commutator value is a commutator of one-site lamps:
`singleHom x` is a homomorphism, so it carries `[K, K]` into the commutator
subgroup of the configuration group. -/
theorem single_mem_commutator (hK : commutator K = ⊤) (x : X) (k : K) :
    single x k ∈ commutator (Lamp K X) := by
  have hk : k ∈ commutator K := hK ▸ Subgroup.mem_top k
  have hmem := map_commutator_le (singleHom x) (Subgroup.mem_map_of_mem _ hk)
  simpa using hmem

/-- **Perfect lamps (43.1).**  If `K` is perfect then so is the group of
finitely supported `K`-configurations, for any site set. -/
theorem commutator_eq_top (hK : commutator K = ⊤) :
    commutator (Lamp K X) = ⊤ := by
  refine eq_top_iff.mpr fun f _ => ?_
  refine (Subgroup.closure_le _).mpr ?_ (mem_closure_singles f)
  rintro g ⟨x, k, rfl⟩
  exact single_mem_commutator hK x k

/-- Every configuration of a perfect lamp group is a product of commutators. -/
theorem mem_commutator_of_perfect (hK : commutator K = ⊤) (f : Lamp K X) :
    f ∈ commutator (Lamp K X) := by
  rw [commutator_eq_top hK]
  exact Subgroup.mem_top f

/-- Every configuration is a product of commutators, so every abelian invariant
of a perfect lamp group is trivial.  This is why `K_ab = 1` erases the whole
lamp subgroup rather than a proper part of it. -/
theorem eq_one_of_commGroup_hom (hK : commutator K = ⊤) {A : Type w} [CommGroup A]
    (φ : Lamp K X →* A) (f : Lamp K X) : φ f = 1 :=
  MonoidHom.mem_ker.mp
    (Abelianization.commutator_subset_ker φ (mem_commutator_of_perfect hK f))

end Lamp

/-! ## The same statement inside the wreath product -/

section Wreath

open SemidirectProduct

variable {K : Type u} [Group K] {G : Type w} [Group G] {X : Type v}
variable [MulAction G X] [DecidableEq X]

/-- For a perfect lamp group the whole lamp subgroup of the wreath product
consists of products of commutators. -/
theorem lampRange_le_commutator (hK : commutator K = ⊤) :
    (inl : Lamp K X →* Wreath K G X).range ≤ commutator (Wreath K G X) := by
  rintro w ⟨f, rfl⟩
  exact map_commutator_le inl
    (Subgroup.mem_map_of_mem _ (Lamp.mem_commutator_of_perfect hK f))

/-- **The abelian half of Theorem 43.1.**  Every homomorphism of the wreath
product into an abelian group kills the entire lamp subgroup -- equivalently,
the abelianized visible quotient of `W_K` is already a quotient of the acting
group.  No radical theory is used: this is perfectness alone. -/
theorem lampRange_le_ker_of_commGroup (hK : commutator K = ⊤) {A : Type*}
    [CommGroup A] (φ : Wreath K G X →* A) :
    (inl : Lamp K X →* Wreath K G X).range ≤ φ.ker :=
  (lampRange_le_commutator hK).trans (Abelianization.commutator_subset_ker φ)

/-- Restated on the projection: for a perfect lamp the kernel of the wreath
projection `W_K ↠ G` is invisible to every abelian target, which is (43.1)
`P_K = G_*` in the abelian case. -/
theorem ker_rightHom_le_ker_of_commGroup (hK : commutator K = ⊤) {A : Type*}
    [CommGroup A] (φ : Wreath K G X →* A) :
    (rightHom : Wreath K G X →* G).ker ≤ φ.ker := by
  rw [ker_rightHom_eq_lampRange]
  exact lampRange_le_ker_of_commGroup hK φ

end Wreath

end GroupApproximation

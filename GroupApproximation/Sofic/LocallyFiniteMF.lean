import GroupApproximation.Sofic.LEFSofic
import GroupApproximation.Sofic.OperatorMFPositiveControls
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finsupp.Fintype

/-!
# Locally finite groups are operator-MF

A group is *locally finite* when every finite subset of it is contained in a
finite subgroup.  This file records the positive permanence fact that sits
beside `isOperatorMF_of_residuallyFinite`: every countable locally finite
group is operator-MF in the literal cofinite norm-matrix-corona sense.

The route is the same one used for residually finite groups, and it is short
because local finiteness gives *exact* finite models rather than merely
approximate ones.  A finite test set `s` lies inside a finite subgroup `K`;
the left regular action of `K` on itself, transported to `Fin (card K)`, is a
genuine group embedding, so the resulting map is exactly multiplicative on `s`
and injective there.  That is precisely the data of `IsLEF`, and
`isWeakMF_of_isLEF` together with `IsWeakMF.isOperatorMF` finish the job.

No exhaustion, direct limit, or diagonal argument is needed: `IsLEF` is
already a purely local statement, one finite test set at a time, so the finite
subgroups never have to be assembled into an increasing chain.

The final section supplies positive controls.  Finite groups are locally
finite for trivial reasons, and -- so that the predicate is not accidentally
equivalent to finiteness -- the infinite locally finite group of finitely
supported functions `ℕ → ZMod 2` is exhibited as well.
-/

namespace GroupApproximation

universe u

variable {G : Type u} [Group G]

/-- **Every countable LEF group is operator-MF.**  Recorded here because the
two halves of this composition live in different files. -/
theorem isOperatorMF_of_isLEF [Countable G] (hG : IsLEF G) : IsOperatorMF G :=
  (isWeakMF_of_isLEF hG).isOperatorMF

/-- **Exhaustion by residually finite subgroups makes a countable group
operator-MF**, completing the LEF/sofic/MF conclusion package that the
telescope-core argument consumes. -/
theorem isOperatorMF_of_forall_finset_residuallyFinite [Countable G]
    (h : ∀ s : Finset G, ∃ H : Subgroup G,
      (∀ x ∈ s, x ∈ H) ∧ Group.ResiduallyFinite H) : IsOperatorMF G :=
  isOperatorMF_of_isLEF (isLEF_of_forall_finset_residuallyFinite h)

/-! ## The local finiteness predicate -/

/-- A group is locally finite when every finite subset lies in a finite
subgroup.  Mathlib has no such predicate for groups, so it is spelled out
here in the form the approximation arguments consume. -/
def IsLocallyFiniteGroup (G : Type u) [Group G] : Prop :=
  ∀ s : Finset G, ∃ H : Subgroup G, Finite H ∧ ∀ g ∈ s, g ∈ H

/-- Every finite group is locally finite: the whole group is the witness. -/
theorem isLocallyFiniteGroup_of_finite (G : Type u) [Group G] [Finite G] :
    IsLocallyFiniteGroup G :=
  fun _ ↦ ⟨⊤, Finite.of_injective _ Subtype.val_injective, fun _ _ ↦ trivial⟩

/-- Local finiteness passes to subgroups of the ambient group: intersect a
witnessing finite subgroup with the image of the smaller group. -/
theorem IsLocallyFiniteGroup.comap {H : Type*} [Group H]
    (hG : IsLocallyFiniteGroup G) (ι : H →* G) (hι : Function.Injective ι) :
    IsLocallyFiniteGroup H := by
  classical
  intro s
  obtain ⟨K, hKfin, hsK⟩ := hG (s.image ι)
  refine ⟨K.comap ι, ?_, fun g hg ↦ hsK (ι g) (Finset.mem_image_of_mem ι hg)⟩
  exact Finite.of_injective (fun x : K.comap ι ↦ (⟨ι x.1, x.2⟩ : K))
    (fun x y hxy ↦ Subtype.ext (hι (congrArg Subtype.val hxy)))

/-! ## Local finiteness gives exact finite models -/

/-- **Locally finite groups are LEF.**  On a finite test set the model is not
merely almost multiplicative but exactly multiplicative, since the test set
sits inside a finite subgroup and the model is that subgroup's left regular
representation. -/
theorem isLEF_of_locallyFinite (hG : IsLocallyFiniteGroup G) : IsLEF G := by
  classical
  intro s
  obtain ⟨K, hKfin, hsK⟩ := hG s
  letI : Fintype K := Fintype.ofFinite K
  let e : K ≃ Fin (Fintype.card K) := Fintype.equivFin K
  -- Retract `G` onto `K`, arbitrarily off `K`; on the test set this is the
  -- identity, which is all that `IsLEF` inspects.
  let r : G → K := fun g ↦ if h : g ∈ K then ⟨g, h⟩ else 1
  have hr : ∀ {g : G}, g ∈ K → (r g : G) = g := by
    intro g hg
    simp only [r, dif_pos hg]
  have hr_one : r 1 = 1 := by
    simp only [r, dif_pos K.one_mem]
    rfl
  have hr_mul : ∀ {x y : G}, x ∈ K → y ∈ K → r (x * y) = r x * r y := by
    intro x y hx hy
    apply Subtype.ext
    rw [hr (K.mul_mem hx hy)]
    show x * y = ((r x : G)) * ((r y : G))
    rw [hr hx, hr hy]
  let f : G → Equiv.Perm (Fin (Fintype.card K)) := fun g ↦
    e.permCongr (Equiv.mulLeft (r g))
  refine ⟨Fintype.card K, f, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have hxK : x ∈ K := hsK x (Finset.mem_coe.mp hx)
    have hyK : y ∈ K := hsK y (Finset.mem_coe.mp hy)
    have hp := Equiv.Perm.congr_fun hxy (e 1)
    have hrxy : r x = r y := by
      apply e.injective
      simpa [f, Equiv.permCongr_apply] using hp
    have := congrArg (Subtype.val) hrxy
    rwa [hr hxK, hr hyK] at this
  · ext z
    simp [f, hr_one, Equiv.permCongr_apply]
  · intro x hx y hy
    have hxK : x ∈ K := hsK x hx
    have hyK : y ∈ K := hsK y hy
    ext z
    simp [f, hr_mul hxK hyK, Equiv.permCongr_apply, Equiv.Perm.mul_apply]

/-- **Locally finite groups are weak-MF**, with separation constant `1`. -/
theorem isWeakMF_of_locallyFinite (hG : IsLocallyFiniteGroup G) : IsWeakMF G :=
  isWeakMF_of_isLEF (isLEF_of_locallyFinite hG)

/-- **Every countable locally finite group is operator-MF** in the literal
cofinite norm-matrix-corona sense, exactly as for countable residually finite
groups. -/
theorem isOperatorMF_of_locallyFinite :
    ∀ {K : Type u} [Group K] [Countable K],
      IsLocallyFiniteGroup K → IsOperatorMF K := by
  intro K _ _ hG
  exact (isWeakMF_of_locallyFinite hG).isOperatorMF

/-- Contrapositive form: a group that is not operator-MF and is countable
cannot be locally finite. -/
theorem not_isLocallyFiniteGroup_of_not_isOperatorMF [Countable G]
    (hG : ¬ IsOperatorMF G) : ¬ IsLocallyFiniteGroup G :=
  fun h ↦ hG (isOperatorMF_of_locallyFinite h)

/-! ## Positive controls

A finite witness alone would leave open that `IsLocallyFiniteGroup` is merely
a paraphrase of finiteness, in which case `isOperatorMF_of_locallyFinite`
would say nothing beyond `isOperatorMF_of_finite_standard`.  The second
control below is therefore an infinite group: the finitely supported
functions `ℕ → ZMod 2`, written multiplicatively.  Each finite test set uses
only finitely many coordinates, and the subgroup of functions supported in
those coordinates injects into a finite function type. -/

/-- The infinite elementary abelian `2`-group, written multiplicatively. -/
abbrev FinitarySquares : Type := Multiplicative (ℕ →₀ ZMod 2)

instance : Countable FinitarySquares :=
  inferInstanceAs (Countable (ℕ →₀ ZMod 2))

instance : Infinite FinitarySquares :=
  inferInstanceAs (Infinite (ℕ →₀ ZMod 2))

/-- The subgroup of `FinitarySquares` of elements vanishing outside a fixed
finite set of coordinates.  Vanishing is used rather than a containment of
supports so that the three closure conditions are pointwise computations. -/
def supportedSubgroup (T : Finset ℕ) : Subgroup FinitarySquares where
  carrier := {g | ∀ i, i ∉ T → Multiplicative.toAdd g i = 0}
  one_mem' := by intro i _; simp
  mul_mem' {a b} ha hb := by
    intro i hi
    show Multiplicative.toAdd a i + Multiplicative.toAdd b i = 0
    rw [ha i hi, hb i hi, add_zero]
  inv_mem' {a} ha := by
    intro i hi
    show -(Multiplicative.toAdd a i) = 0
    rw [ha i hi, neg_zero]

theorem mem_supportedSubgroup {T : Finset ℕ} {g : FinitarySquares} :
    g ∈ supportedSubgroup T ↔ ∀ i, i ∉ T → Multiplicative.toAdd g i = 0 :=
  Iff.rfl

theorem supportedSubgroup_finite (T : Finset ℕ) :
    Finite (supportedSubgroup T) := by
  classical
  refine Finite.of_injective
    (fun g ↦ (fun i : T ↦ Multiplicative.toAdd g.1 i)) ?_
  intro g h hgh
  refine Subtype.ext (Multiplicative.toAdd.injective (Finsupp.ext ?_))
  intro i
  by_cases hi : i ∈ T
  · exact congrFun hgh ⟨i, hi⟩
  · rw [mem_supportedSubgroup.mp g.2 i hi, mem_supportedSubgroup.mp h.2 i hi]

/-- Positive control: an infinite locally finite group. -/
theorem isLocallyFiniteGroup_finitarySquares :
    IsLocallyFiniteGroup FinitarySquares := by
  classical
  intro s
  refine ⟨supportedSubgroup (s.sup fun g ↦ (Multiplicative.toAdd g).support),
    supportedSubgroup_finite _, fun g hg i hi ↦ ?_⟩
  refine Finsupp.notMem_support_iff.mp fun hc ↦ hi ?_
  exact Finset.mem_of_subset
    (Finset.le_sup (f := fun g ↦ (Multiplicative.toAdd g).support) hg) hc

example (K : Type u) [Group K] [Finite K] : IsLocallyFiniteGroup K :=
  isLocallyFiniteGroup_of_finite K

example : IsLocallyFiniteGroup FinitarySquares ∧ Infinite FinitarySquares :=
  ⟨isLocallyFiniteGroup_finitarySquares, inferInstance⟩

example : IsLEF FinitarySquares :=
  isLEF_of_locallyFinite isLocallyFiniteGroup_finitarySquares

/-- The headline consequence, on a group that is infinite and locally
finite. -/
example : IsOperatorMF FinitarySquares :=
  isOperatorMF_of_locallyFinite isLocallyFiniteGroup_finitarySquares

end GroupApproximation

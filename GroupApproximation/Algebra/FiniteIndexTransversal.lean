import Mathlib.GroupTheory.Index
import Mathlib.Tactic

/-!
# Right transversals of a finite-index subgroup

Everything this repository wants to do with a finite-index subgroup --- induce a
representation across it (`Kazhdan/InducedRepresentation.lean`), read Schreier
generators off it (`Algebra/SchreierGenerators.lean`), rewrite relators through
it (`Algebra/ReidemeisterSchreier.lean`) --- needs one and the same piece of
combinatorics: a choice of representative for each *right* coset `Λγ`, together
with the bookkeeping that choice satisfies.

`RightTransversal Γ Λ` bundles that choice as a function `sec : Γ → Γ` picking
the representative of `Λγ`, subject to five conditions, and
`exists_rightTransversal` produces one from `Λ.FiniteIndex`.  Downstream modules
take a `RightTransversal` as data and never touch a quotient type again.

## Why right cosets

The word metric of `Algebra/WordMetric.lean` is *left* invariant, so generators
act on the right and paths in the Cayley graph are read by right multiplication.
The retraction `Γ → Λ` that survives that convention is `γ ↦ γ · sec(γ)⁻¹`, and
it is *left* `Λ`-equivariant (`retract_mul_left`), which is what makes the
Schreier estimate of `Algebra/SchreierGenerators.lean` an estimate about a
one-step move.  With left cosets the same formula acquires a `γ`-dependent
conjugation and the estimate dies.

## The five conditions

`sec_mem_reps` and `sec_eq_self` together say that `reps` is exactly the set of
chosen representatives and that `sec` fixes each of them --- so `sec` is
idempotent and `reps` is finite, which is where finiteness of the index enters.
`mul_inv_sec_mem` says the representative is in the right coset,
`sec_mul_left` says the choice depends only on the coset, and `sec_one`
normalises the choice at the trivial coset: `sec` sends every element of `Λ` to
`1`.  That last condition is not cosmetic --- it is what makes the base index
`1 ∈ reps` a fixed point of the `Λ`-action in
`Kazhdan/InducedRepresentation.lean`, and hence what turns an invariant vector
of an induced representation into an invariant vector of the original one.

## The action and the cocycle

The second half of the file packages the two derived objects every consumer
uses: the right action `c · g = sec(c·g)` of `Γ` on the finite set of
representatives (`act`, with `act_act` its associativity), and the `Λ`-valued
cocycle `cocycle γ g = γ · g · sec(γ·g)⁻¹` (with `cocycle_mul` the cocycle
identity).  Both laws reduce to the single rewriting step `sec_sec_mul`, which
says that replacing an element by its representative does not change the
representative of a right translate.  The Schreier generators of
`Algebra/SchreierGenerators.lean` are the values of `cocycle` on
`reps × S`, and the coordinates of the induced representation of
`Kazhdan/InducedRepresentation.lean` are indexed by `act`.
-/

namespace GroupApproximation
namespace FiniteIndex

universe u

/-- A **right transversal** of `Λ` in `Γ`: a choice `sec γ` of representative for
the right coset `Λγ`, normalised so that `sec` sends `Λ` to `1`, together with
the finite set `reps` of chosen representatives. -/
structure RightTransversal (Γ : Type u) [Group Γ] (Λ : Subgroup Γ) where
  /-- The chosen representative of the right coset of `γ`. -/
  sec : Γ → Γ
  /-- The (finite) set of chosen representatives. -/
  reps : Finset Γ
  /-- Every chosen representative is one of the listed ones. -/
  sec_mem_reps : ∀ γ : Γ, sec γ ∈ reps
  /-- Each listed representative is its own representative. -/
  sec_eq_self : ∀ c ∈ reps, sec c = c
  /-- The representative lies in the right coset of the element. -/
  mul_inv_sec_mem : ∀ γ : Γ, γ * (sec γ)⁻¹ ∈ Λ
  /-- The choice depends only on the right coset. -/
  sec_mul_left : ∀ a ∈ Λ, ∀ γ : Γ, sec (a * γ) = sec γ
  /-- The choice is normalised at the trivial coset. -/
  sec_one : sec 1 = 1

namespace RightTransversal

variable {Γ : Type u} [Group Γ] {Λ : Subgroup Γ} (tr : RightTransversal Γ Λ)

/-- The identity is a chosen representative. -/
theorem one_mem_reps : (1 : Γ) ∈ tr.reps := by
  have h := tr.sec_mem_reps 1
  rwa [tr.sec_one] at h

/-- `reps` is nonempty, because it contains the identity. -/
theorem reps_nonempty : tr.reps.Nonempty :=
  ⟨1, tr.one_mem_reps⟩

/-- The number of chosen representatives is positive. -/
theorem card_reps_pos : 0 < tr.reps.card :=
  Finset.card_pos.mpr tr.reps_nonempty

/-- **`sec` is idempotent.** -/
@[simp] theorem sec_sec (γ : Γ) : tr.sec (tr.sec γ) = tr.sec γ :=
  tr.sec_eq_self _ (tr.sec_mem_reps γ)

/-- Elements of `Λ` are sent to `1`. -/
@[simp] theorem sec_of_mem {a : Γ} (ha : a ∈ Λ) : tr.sec a = 1 := by
  have h := tr.sec_mul_left a ha 1
  rwa [mul_one, tr.sec_one] at h

/-- **The retraction** `Γ → Λ` attached to the transversal: `γ ↦ γ · sec(γ)⁻¹`. -/
def retract (γ : Γ) : Γ := γ * (tr.sec γ)⁻¹

/-- The retraction lands in `Λ`. -/
theorem retract_mem (γ : Γ) : tr.retract γ ∈ Λ :=
  tr.mul_inv_sec_mem γ

/-- The retraction and the representative recover the element. -/
@[simp] theorem retract_mul_sec (γ : Γ) : tr.retract γ * tr.sec γ = γ := by
  simp [retract]

/-- **The key rewriting step.**  Replacing an element by its representative does
not change the representative of a right translate.  Every computation with the
cocycle of `Kazhdan/InducedRepresentation.lean` and every Schreier rewriting
step is an instance of this. -/
theorem sec_sec_mul (γ g : Γ) : tr.sec (tr.sec γ * g) = tr.sec (γ * g) := by
  have hmem : tr.retract γ ∈ Λ := tr.retract_mem γ
  have h : tr.sec (tr.retract γ * (tr.sec γ * g)) = tr.sec (tr.sec γ * g) :=
    tr.sec_mul_left _ hmem _
  rw [← mul_assoc, tr.retract_mul_sec] at h
  exact h.symm

/-- The retraction is left `Λ`-equivariant. -/
theorem retract_mul_left {a : Γ} (ha : a ∈ Λ) (γ : Γ) :
    tr.retract (a * γ) = a * tr.retract γ := by
  simp [retract, tr.sec_mul_left a ha γ, mul_assoc]

/-- The retraction fixes `Λ` pointwise. -/
@[simp] theorem retract_of_mem {a : Γ} (ha : a ∈ Λ) : tr.retract a = a := by
  simp [retract, tr.sec_of_mem ha]

/-- The retraction of the identity is the identity. -/
@[simp] theorem retract_one : tr.retract (1 : Γ) = 1 :=
  tr.retract_of_mem (one_mem Λ)

/-- **The one-step formula.**  Moving one step to the right moves the retraction
by `sec γ · g · sec(sec γ · g)⁻¹`, an element that depends on `γ` only through
its representative.  This is the Schreier generator attached to the pair
`(sec γ, g)`, and the estimate of `Algebra/SchreierGenerators.lean` is this
identity read as a statement about word length. -/
theorem retract_mul_right (γ g : Γ) :
    tr.retract (γ * g) = tr.retract γ * (tr.sec γ * g * (tr.sec (tr.sec γ * g))⁻¹) := by
  rw [tr.sec_sec_mul γ g]
  simp only [retract]
  group

end RightTransversal

/-! ## Existence -/

/-- **A finite-index subgroup has a right transversal.**  The choice is made on
the quotient `Γ ⧸ Λ` --- through the inversion `γ ↦ γ⁻¹`, which converts right
cosets into left ones --- and then normalised at the trivial coset so that
`sec_one` holds. -/
theorem exists_rightTransversal {Γ : Type u} [Group Γ] (Λ : Subgroup Γ)
    [hΛ : Λ.FiniteIndex] : Nonempty (RightTransversal Γ Λ) := by
  classical
  have hfin : Finite (Γ ⧸ Λ) :=
    Subgroup.index_ne_zero_iff_finite.mp (Subgroup.finiteIndex_iff.mp hΛ)
  have hrep : ∀ c : Γ ⧸ Λ, ∃ a : Γ, (QuotientGroup.mk a : Γ ⧸ Λ) = c := by
    intro c
    exact Quotient.inductionOn c fun a => ⟨a, rfl⟩
  -- A representative for each coset, normalised at the trivial one.
  -- `Γ ⧸ Λ` carries no group structure here -- `Λ` need not be normal -- so the
  -- trivial coset is the class of `1`, not the numeral `1`.
  set pick : (Γ ⧸ Λ) → Γ :=
    fun c => if c = (QuotientGroup.mk (1 : Γ) : Γ ⧸ Λ) then 1 else ((hrep c).choose)⁻¹
    with hpickdef
  have hpick : ∀ c : Γ ⧸ Λ, (QuotientGroup.mk (pick c)⁻¹ : Γ ⧸ Λ) = c := by
    intro c
    by_cases hc : c = (QuotientGroup.mk (1 : Γ) : Γ ⧸ Λ)
    · simp [hpickdef, hc]
    · simp only [hpickdef, if_neg hc, inv_inv]
      exact (hrep c).choose_spec
  set sec : Γ → Γ := fun γ => pick (QuotientGroup.mk γ⁻¹) with hsecdef
  -- The coset of an element determines, and is determined by, its representative.
  have hsec_coset : ∀ γ : Γ, (QuotientGroup.mk (sec γ)⁻¹ : Γ ⧸ Λ) = QuotientGroup.mk γ⁻¹ := by
    intro γ
    exact hpick _
  have hmem : ∀ γ : Γ, γ * (sec γ)⁻¹ ∈ Λ := by
    intro γ
    have h := hsec_coset γ
    rw [QuotientGroup.eq] at h
    have h' : sec γ * γ⁻¹ ∈ Λ := by simpa using h
    have := Λ.inv_mem h'
    simpa [mul_inv_rev] using this
  have hleft : ∀ a ∈ Λ, ∀ γ : Γ, sec (a * γ) = sec γ := by
    intro a ha γ
    have hco : (QuotientGroup.mk (a * γ)⁻¹ : Γ ⧸ Λ) = QuotientGroup.mk γ⁻¹ := by
      rw [QuotientGroup.eq]
      have : ((a * γ)⁻¹)⁻¹ * γ⁻¹ = a := by group
      rw [this]
      exact ha
    simp only [hsecdef, hco]
  have hone : sec 1 = 1 := by simp [hsecdef, hpickdef]
  -- The chosen representatives form a finite set.
  have hrangefin : (Set.range pick).Finite := Set.finite_range pick
  refine ⟨{ sec := sec
            reps := hrangefin.toFinset
            sec_mem_reps := ?_
            sec_eq_self := ?_
            mul_inv_sec_mem := hmem
            sec_mul_left := hleft
            sec_one := hone }⟩
  · intro γ
    exact hrangefin.mem_toFinset.mpr ⟨QuotientGroup.mk γ⁻¹, rfl⟩
  · intro c hc
    obtain ⟨d, rfl⟩ := hrangefin.mem_toFinset.mp hc
    simp only [hsecdef]
    rw [hpick d]

/-- The transversal supplied by `exists_rightTransversal`, chosen once and for
all. -/
noncomputable def rightTransversal {Γ : Type u} [Group Γ] (Λ : Subgroup Γ)
    [Λ.FiniteIndex] : RightTransversal Γ Λ :=
  (exists_rightTransversal Λ).some

section Action

variable {Γ : Type u} [Group Γ] {Λ : Subgroup Γ}

/-! ## The index set, the action and the cocycle -/

/-- The index set of the induced representation: the chosen coset
representatives. -/
abbrev Index (tr : RightTransversal Γ Λ) : Type u := {c : Γ // c ∈ tr.reps}

/-- The base index, the representative `1` of the coset `Λ`. -/
def baseIndex (tr : RightTransversal Γ Λ) : Index tr :=
  ⟨1, tr.one_mem_reps⟩

/-- The right action of `Γ` on the chosen representatives. -/
def act (tr : RightTransversal Γ Λ) (c : Index tr) (g : Γ) : Index tr :=
  ⟨tr.sec (c.1 * g), tr.sec_mem_reps _⟩

@[simp] theorem act_coe (tr : RightTransversal Γ Λ) (c : Index tr) (g : Γ) :
    (act tr c g).1 = tr.sec (c.1 * g) := rfl

@[simp] theorem act_one (tr : RightTransversal Γ Λ) (c : Index tr) : act tr c 1 = c := by
  refine Subtype.ext ?_
  show tr.sec (c.1 * 1) = c.1
  rw [mul_one]
  exact tr.sec_eq_self c.1 c.2

theorem act_act (tr : RightTransversal Γ Λ) (c : Index tr) (g h : Γ) :
    act tr (act tr c g) h = act tr c (g * h) := by
  refine Subtype.ext ?_
  show tr.sec (tr.sec (c.1 * g) * h) = tr.sec (c.1 * (g * h))
  rw [tr.sec_sec_mul, mul_assoc]

/-- Each `g` permutes the chosen representatives. -/
def actEquiv (tr : RightTransversal Γ Λ) (g : Γ) : Index tr ≃ Index tr where
  toFun c := act tr c g
  invFun c := act tr c g⁻¹
  left_inv c := by simp only [act_act, mul_inv_cancel, act_one]
  right_inv c := by simp only [act_act, inv_mul_cancel, act_one]

@[simp] theorem actEquiv_apply (tr : RightTransversal Γ Λ) (g : Γ) (c : Index tr) :
    actEquiv tr g c = act tr c g := rfl

/-- The `Λ`-valued cocycle `γ · g · sec(γ·g)⁻¹` of the transversal. -/
def cocycle (tr : RightTransversal Γ Λ) (γ g : Γ) : Λ :=
  ⟨γ * g * (tr.sec (γ * g))⁻¹, tr.mul_inv_sec_mem _⟩

@[simp] theorem cocycle_coe (tr : RightTransversal Γ Λ) (γ g : Γ) :
    ((cocycle tr γ g : Λ) : Γ) = γ * g * (tr.sec (γ * g))⁻¹ := rfl

/-- At a representative the cocycle is trivial in the identity direction. -/
@[simp] theorem cocycle_one (tr : RightTransversal Γ Λ) (c : Index tr) :
    cocycle tr c.1 1 = 1 := by
  refine Subtype.ext ?_
  simp only [cocycle_coe, Subgroup.coe_one, mul_one]
  rw [tr.sec_eq_self c.1 c.2, mul_inv_cancel]

/-- **The cocycle identity.** -/
theorem cocycle_mul (tr : RightTransversal Γ Λ) (γ g h : Γ) :
    cocycle tr γ (g * h) = cocycle tr γ g * cocycle tr (tr.sec (γ * g)) h := by
  refine Subtype.ext ?_
  simp only [cocycle_coe, Subgroup.coe_mul, ← mul_assoc]
  rw [tr.sec_sec_mul]
  group

/-- At the base index the cocycle in a direction from `Λ` is that element
itself.  This is the consequence of `sec_one` that makes the induced
representation see `π` again. -/
theorem cocycle_baseIndex_of_mem (tr : RightTransversal Γ Λ) {a : Γ} (ha : a ∈ Λ) :
    cocycle tr (baseIndex tr).1 a = ⟨a, ha⟩ := by
  refine Subtype.ext ?_
  show (1 : Γ) * a * (tr.sec (1 * a))⁻¹ = a
  rw [one_mul, tr.sec_of_mem ha, inv_one, mul_one]

/-- The base index is fixed by `Λ`. -/
theorem act_baseIndex_of_mem (tr : RightTransversal Γ Λ) {a : Γ} (ha : a ∈ Λ) :
    act tr (baseIndex tr) a = baseIndex tr := by
  refine Subtype.ext ?_
  show tr.sec ((1 : Γ) * a) = 1
  rw [one_mul]
  exact tr.sec_of_mem ha

/-- A representative is recovered from the base index by acting with itself. -/
theorem act_baseIndex_self (tr : RightTransversal Γ Λ) (c : Index tr) :
    act tr (baseIndex tr) c.1 = c := by
  refine Subtype.ext ?_
  show tr.sec ((1 : Γ) * c.1) = c.1
  rw [one_mul]
  exact tr.sec_eq_self c.1 c.2

end Action

end FiniteIndex
end GroupApproximation

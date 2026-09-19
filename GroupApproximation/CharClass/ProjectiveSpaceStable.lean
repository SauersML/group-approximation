import GroupApproximation.CharClass.ChernEulerBundle
import GroupApproximation.CharClass.MayerVietorisSequence
import GroupApproximation.CharClass.MayerVietorisPullAmbient

/-!
# Stability of the degree-2 generator under `ℂP^d ⊆ ℂP^{d+1}`

The second half of item 1 of this lane's brief.  The generator `cpGen` is
canonical in each `ℂP^d` separately, because an `F₂`-line has exactly one nonzero
element; what has to be proved is that the hyperplane inclusion carries one to
the other, that is, that it is *essential* on `H^2`.

The proof factors the inclusion through the punctured space, which is the second
open set of the Mayer–Vietoris cover already used to compute `H^*(ℂP^{d+1})`:

```text
ℂP^d  --inclP-->  ℂP^{d+1} ∖ {pt}  --⊆-->  ℂP^{d+1}.
```

The second map is bijective on `H^2` for `d ≥ 1` by `bijective_resV`, since the
chart has no `H^2` and the intersection is a sphere of dimension `2d+1 ∉ {1,2}`.
The first is bijective because the retraction is a homotopy equivalence and
`retract ∘ inclP` is the identity *on the nose*, so pullback along `inclP` is the
inverse of a bijection.  A composite of bijections takes the nonzero class to a
nonzero class, and in a line that is the generator.

## Main declarations

* `cpInclP`, `punctIncl`, `cpIncl` — the two halves of the inclusion, and the
  hyperplane inclusion factored through them.
* `bijective_pull_cpIncl` — the hyperplane inclusion is bijective on `H^2`.
* `pull_cpIncl_cpGen` — **generator stability**.
* `pull_cpIncl_cupPowE` — the powers of the generator are stable too, which is
  what the ring statement consumes.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace CPn

open CategoryTheory TopologicalSpace
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

/-! ## 1. The inclusion, factored through the punctured space -/

/-- `ℂP^d` inside the punctured `ℂP^{d+1}`. -/
def cpInclP (d : ℕ) : CPtop d ⟶ punctSpace d := cmap (inclPMap d)

/-- The inclusion of the punctured space into `ℂP^{d+1}`.  Written out rather
than as `sInclusion` of a coerced open set, so that its source is *syntactically*
`punctSpace d` and no coercion has to be inverted during elaboration. -/
def punctIncl (d : ℕ) : punctSpace d ⟶ CPtop (d + 1) :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- **The hyperplane inclusion** `ℂP^d ⊆ ℂP^{d+1}`, as a morphism of spaces,
factored through the punctured space so that the Mayer–Vietoris restriction is
literally one of its two halves. -/
def cpIncl (d : ℕ) : CPtop d ⟶ CPtop (d + 1) := cpInclP d ≫ punctIncl d

@[simp] theorem cpIncl_apply (d : ℕ) (z : CP d) :
    (ConcreteCategory.hom (cpIncl d)) z = incl z := rfl

/-! ## 2. Both halves are bijective on `H^2` -/

/-- Pullback along `ℂP^d ⊆ ℂP^{d+1} ∖ {pt}` is bijective in every degree: it is
the inverse of the homotopy equivalence given by the retraction. -/
theorem bijective_pull_cpInclP (d n : ℕ) : Function.Bijective (pull (cpInclP d) n) :=
  (pullEquivOfHomotopyEquiv (punctOpenHomotopyEquiv d) n).symm.bijective

/-- The Mayer–Vietoris restriction to the punctured space is a pullback. -/
theorem resV_eq_pull (d n : ℕ) (a : Hmod2 (CPtop (d + 1)) n) :
    (mvSequence (chartOpen d) (punctOpen d) (chartOpen_sup_punctOpen d)).resV n a
      = pull (punctIncl d) n a := by
  show (mvResV (chartOpen d) (punctOpen d) (chartOpen_sup_punctOpen d) n).hom a = _
  rw [mvResV_eq_pull]
  rfl

/-- Restriction to the punctured space is bijective in degree 2, for `d ≥ 1`.
The chart has no `H^2`, and the intersection is a sphere of dimension `2d+1`,
which is neither `1` nor `2`. -/
theorem bijective_resV_two (d : ℕ) (hd : 1 ≤ d) :
    Function.Bijective
      ((mvSequence (chartOpen d) (punctOpen d) (chartOpen_sup_punctOpen d)).resV 2) := by
  refine MVSequence.bijective_resV _ 1 ?_ ?_ ?_
  · exact fun a => (hasPointCohomology_chartSpace d).2 2 (by omega) a
  · exact fun w => (hasSphereCohomology_interSpace d).2.2 1 (by omega) (by omega) w
  · exact fun w => (hasSphereCohomology_interSpace d).2.2 2 (by omega) (by omega) w

theorem bijective_pull_punctIncl_two (d : ℕ) (hd : 1 ≤ d) :
    Function.Bijective (pull (punctIncl d) 2) := by
  have hb := bijective_resV_two d hd
  have heq : ⇑((mvSequence (chartOpen d) (punctOpen d) (chartOpen_sup_punctOpen d)).resV 2)
      = pull (punctIncl d) 2 :=
    funext (resV_eq_pull d 2)
  rwa [heq] at hb

/-- **The hyperplane inclusion is bijective on `H^2`**, for `d ≥ 1`. -/
theorem bijective_pull_cpIncl (d : ℕ) (hd : 1 ≤ d) :
    Function.Bijective (pull (cpIncl d) 2) := by
  have hfun : pull (cpIncl d) 2
      = (pull (cpInclP d) 2) ∘ (pull (punctIncl d) 2) :=
    funext fun a => pull_comp _ _ 2 a
  rw [hfun]
  exact Function.Bijective.comp (bijective_pull_cpInclP d 2)
    (bijective_pull_punctIncl_two d hd)

/-! ## 3. Stability -/

/-- **Stability of the degree-2 generator.**  The hyperplane inclusion pulls the
generator of `H^2(ℂP^{d+1}; F₂)` back to the generator of `H^2(ℂP^d; F₂)`.  No
orientation enters: a line over `F₂` has one nonzero element, so the only thing
to prove is that the pullback is not zero. -/
theorem pull_cpIncl_cpGen (d : ℕ) (hd : 1 ≤ d) :
    pull (cpIncl d) 2 (cpGen (d + 1) (by omega)) = cpGen d hd := by
  refine eq_cpGen_of_ne_zero hd ?_
  intro hzero
  refine cpGen_ne_zero (d + 1) (by omega) ?_
  refine (bijective_pull_cpIncl d hd).1 ?_
  rw [hzero, pull_zero]

/-- The powers of the generator are stable too. -/
theorem pull_cpIncl_cupPowE (d : ℕ) (hd : 1 ≤ d) (m : ℕ) :
    pull (cpIncl d) (2 * m) (cupPowE (cpGen (d + 1) (by omega)) m)
      = cupPowE (cpGen d hd) m := by
  rw [pull_cupPowE, pull_cpIncl_cpGen d hd]

end

end CPn
end CharClass
end GroupApproximation

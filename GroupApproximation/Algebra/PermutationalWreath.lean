import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.SemidirectProduct
import GroupApproximation.Algebra.FiniteResidual

/-!
# Permutational wreath products with arbitrary lamp groups

The dossier's terminal layer needs `K^{(X)} ⋊ G` for an arbitrary — in
particular nonabelian — lamp group `K`, whereas the repository's existing lamp
constructions are mod-two or Clifford specific.  This file supplies the general
object.

* `lampSubgroup K X` is the restricted direct product inside `X → K`: the
  functions with finite support.  Its `Group` instance is inherited, so no
  algebraic boilerplate is needed.
* `Lamp K X` is that subgroup as a type, `Lamp.single x k` the lamp with value
  `k` at the site `x`.
* `lampAut` is the coordinate-permutation action of a group acting on the site
  set, and `Wreath K G X` the resulting semidirect product.

The two facts the collapse argument consumes are proved here:
`Lamp.single_commute` (lamps at distinct sites commute, which is what makes a
one-site lamp a *commuting-orbit* witness even for nonabelian `K`) and
`Lamp.conj_single` (conjugating a one-site lamp by the acting group moves the
site and keeps the value).
-/

namespace GroupApproximation

universe u v w

/-! ## The restricted direct product -/

variable (K : Type u) [Group K] (X : Type v)

/-- The finitely supported functions `X → K`, as a subgroup of the full
product. -/
def lampSubgroup : Subgroup (X → K) where
  carrier := {f | {x : X | f x ≠ 1}.Finite}
  one_mem' := by
    simp only [Set.mem_setOf_eq, Pi.one_apply, ne_eq, not_true_eq_false,
      Set.setOf_false]
    exact Set.finite_empty
  mul_mem' := by
    intro f g hf hg
    refine Set.Finite.subset (hf.union hg) ?_
    intro x hx
    simp only [Set.mem_setOf_eq, Pi.mul_apply] at hx
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
    exact hx (by rw [hcon.1, hcon.2, one_mul])
  inv_mem' := by
    intro f hf
    refine Set.Finite.subset hf ?_
    intro x hx
    simp only [Set.mem_setOf_eq, Pi.inv_apply, ne_eq, inv_eq_one] at hx
    exact hx

/-- The lamp group: finitely supported configurations of `K` over the sites
`X`. -/
abbrev Lamp : Type (max u v) := ↥(lampSubgroup K X)

namespace Lamp

variable {K X}

/-- The underlying configuration of a lamp. -/
def toFun (f : Lamp K X) : X → K := (f : X → K)

@[simp] theorem mul_apply (f g : Lamp K X) (x : X) :
    (f * g : Lamp K X).toFun x = f.toFun x * g.toFun x := rfl

@[simp] theorem one_apply (x : X) : (1 : Lamp K X).toFun x = 1 := rfl

@[simp] theorem inv_apply (f : Lamp K X) (x : X) :
    (f⁻¹ : Lamp K X).toFun x = (f.toFun x)⁻¹ := rfl

theorem ext {f g : Lamp K X} (h : ∀ x, f.toFun x = g.toFun x) : f = g :=
  Subtype.ext (funext h)

variable [DecidableEq X]

/-- The lamp with value `k` at the site `x` and the identity elsewhere. -/
def single (x : X) (k : K) : Lamp K X :=
  ⟨fun y => if y = x then k else 1, by
    refine Set.Finite.subset (Set.finite_singleton x) ?_
    intro y hy
    simp only [Set.mem_setOf_eq] at hy
    by_contra hne
    exact hy (if_neg hne)⟩

@[simp] theorem single_apply_self (x : X) (k : K) :
    (single x k).toFun x = k := if_pos rfl

@[simp] theorem single_apply_of_ne {x y : X} (h : y ≠ x) (k : K) :
    (single x k).toFun y = 1 := if_neg h

theorem single_one (x : X) : single x (1 : K) = 1 := by
  refine ext fun y => ?_
  by_cases h : y = x
  · subst h; simp
  · simp [single_apply_of_ne h]

theorem single_mul (x : X) (k l : K) :
    single x (k * l) = single x k * single x l := by
  refine ext fun y => ?_
  by_cases h : y = x
  · subst h; simp
  · simp [single_apply_of_ne h]

/-- Placing a value at a fixed site is a homomorphism. -/
def singleHom (x : X) : K →* Lamp K X where
  toFun := single x
  map_one' := single_one x
  map_mul' := single_mul x

@[simp] theorem singleHom_apply (x : X) (k : K) : singleHom x k = single x k := rfl

/-- Conjugating a one-site lamp by an arbitrary configuration keeps it at the
same site.  In particular each coordinate copy is normal. -/
theorem conj_single (f : Lamp K X) (x : X) (k : K) :
    f * single x k * f⁻¹ = single x (f.toFun x * k * (f.toFun x)⁻¹) := by
  refine ext fun y => ?_
  by_cases h : y = x
  · subst h; simp
  · simp [single_apply_of_ne h]

/-- **Lamps at distinct sites commute**, whatever the lamp group.  This is what
makes a one-site lamp a commuting-orbit witness even when `K` is nonabelian. -/
theorem single_commute {x y : X} (h : x ≠ y) (k l : K) :
    single x k * single y l = single y l * single x k := by
  refine ext fun z => ?_
  simp only [mul_apply]
  by_cases hzx : z = x
  · have hzy : z ≠ y := by rw [hzx]; exact h
    rw [single_apply_of_ne hzy l, mul_one, one_mul]
  · rw [single_apply_of_ne hzx k, one_mul, mul_one]

end Lamp

/-! ## The coordinate-permutation action -/

section Action

variable {K X} {G : Type w} [Group G] [MulAction G X]

/-- Translating a lamp configuration along the site action. -/
def lampAut (g : G) : Lamp K X ≃* Lamp K X where
  toFun f := ⟨fun y => (f : X → K) (g⁻¹ • y), by
    show {y : X | (f : X → K) (g⁻¹ • y) ≠ 1}.Finite
    have hset : {y : X | (f : X → K) (g⁻¹ • y) ≠ 1}
        = (fun y : X => g⁻¹ • y) ⁻¹' {x : X | (f : X → K) x ≠ 1} := rfl
    rw [hset]
    exact Set.Finite.preimage (MulAction.injective g⁻¹).injOn f.2⟩
  invFun f := ⟨fun y => (f : X → K) (g • y), by
    show {y : X | (f : X → K) (g • y) ≠ 1}.Finite
    have hset : {y : X | (f : X → K) (g • y) ≠ 1}
        = (fun y : X => g • y) ⁻¹' {x : X | (f : X → K) x ≠ 1} := rfl
    rw [hset]
    exact Set.Finite.preimage (MulAction.injective g).injOn f.2⟩
  left_inv := fun f => Lamp.ext fun y => by simp [Lamp.toFun]
  right_inv := fun f => Lamp.ext fun y => by simp [Lamp.toFun]
  map_mul' := fun f h => Lamp.ext fun y => rfl

@[simp] theorem lampAut_apply (g : G) (f : Lamp K X) (y : X) :
    (lampAut (K := K) g f).toFun y = f.toFun (g⁻¹ • y) := rfl

/-- The coordinate-permutation action as a homomorphism into the automorphism
group of the lamp group. -/
def lampActionHom : G →* MulAut (Lamp K X) where
  toFun := lampAut
  map_one' := by
    refine MulEquiv.ext fun f => Lamp.ext fun y => ?_
    simp
  map_mul' := fun g h => by
    refine MulEquiv.ext fun f => Lamp.ext fun y => ?_
    simp [mul_smul]

/-- The permutational wreath product `K^{(X)} ⋊ G`. -/
abbrev Wreath (K : Type u) [Group K] (G : Type w) [Group G] (X : Type v)
    [MulAction G X] : Type (max u v w) :=
  Lamp K X ⋊[lampActionHom (K := K) (X := X) (G := G)] G

variable [DecidableEq X]

/-- Conjugating a one-site lamp by the acting group moves the site and keeps
the value. -/
theorem lampAut_single (g : G) (x : X) (k : K) :
    lampAut (K := K) g (Lamp.single x k) = Lamp.single (g • x) k := by
  refine Lamp.ext fun y => ?_
  by_cases h : y = g • x
  · subst h
    simp [Lamp.single_apply_self, inv_smul_smul]
  · have h' : g⁻¹ • y ≠ x := by
      intro hcon
      exact h (by rw [← hcon, smul_inv_smul])
    rw [lampAut_apply, Lamp.single_apply_of_ne h', Lamp.single_apply_of_ne h]

end Action


/-! ## The compression witness facts -/

section Witness

variable {K : Type u} [Group K] {X : Type v} [DecidableEq X]
variable {G : Type w} [Group G] [MulAction G X]

/-- **Section 36.4.**  The conjugates of a one-site lamp by the acting group
commute pairwise, *even when the lamp group is nonabelian*: two such conjugates
either sit at distinct sites, where the restricted direct product makes them
commute, or they are literally the same element. -/
theorem conj_single_commute (g h : G) (x₀ : X) (k : K) :
    lampAut (K := K) g (Lamp.single x₀ k) * lampAut (K := K) h (Lamp.single x₀ k)
      = lampAut (K := K) h (Lamp.single x₀ k) *
        lampAut (K := K) g (Lamp.single x₀ k) := by
  rw [lampAut_single, lampAut_single]
  by_cases hxy : g • x₀ = h • x₀
  · rw [hxy]
  · exact Lamp.single_commute hxy k k

/-- **The lamp defect is nontrivial at distinct sites.**  This is what makes the
collapse witness produce a nonidentity element of the MF radical. -/
theorem single_mul_single_inv_ne_one {x y : X} (hxy : x ≠ y) {k : K}
    (hk : k ≠ 1) : Lamp.single x k * Lamp.single y k⁻¹ ≠ (1 : Lamp K X) := by
  intro hcon
  have hval : (Lamp.single x k * Lamp.single y k⁻¹ : Lamp K X).toFun x
      = (1 : Lamp K X).toFun x := by rw [hcon]
  rw [Lamp.mul_apply, Lamp.single_apply_self, Lamp.single_apply_of_ne hxy,
    Lamp.one_apply, mul_one] at hval
  exact hk hval

end Witness

/-! ## Coordinate evaluation and residual finiteness -/

section Eval

variable {K : Type u} [Group K] {X : Type v}

/-- Evaluation of a lamp configuration at a site. -/
def evalHom (x : X) : Lamp K X →* K where
  toFun f := (f : X → K) x
  map_one' := rfl
  map_mul' := fun _ _ => rfl

@[simp] theorem evalHom_apply (x : X) (f : Lamp K X) :
    evalHom x f = (f : X → K) x := rfl

/-- **The lamp group over a finite lamp group is residually finite.**  A
nonidentity configuration is nontrivial at some site, and evaluation there is a
homomorphism onto a finite group.  In particular the lamp group is intrinsically
very easy to approximate; what fails in the wreath product is extending those
models through the compressed action. -/
theorem lamp_isResiduallyFinite [Finite K] :
    IsResiduallyFinite (Lamp K X) := by
  classical
  rw [isResiduallyFinite_iff]
  intro f hf
  have hex : ∃ x : X, (f : X → K) x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hf (Subtype.ext (funext hcon))
  obtain ⟨x, hx⟩ := hex
  haveI : Finite (K ⧸ (⊥ : Subgroup K)) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective (⊥ : Subgroup K))
  haveI hker : ((⊥ : Subgroup K).comap (evalHom (K := K) x)).FiniteIndex :=
    finiteIndex_comap_of_normal (evalHom (K := K) x) ⊥
  refine ⟨(evalHom (K := K) x).ker, ?_, ?_⟩
  · rw [← MonoidHom.comap_bot]
    exact hker
  · intro hmem
    exact hx (MonoidHom.mem_ker.mp hmem)

end Eval


/-! ## Local finiteness of the lamp group -/

section LocallyFinite

variable {K : Type u} [Group K] {X : Type v}

/-- The configurations supported inside a fixed finite set of sites. -/
def suppIn (S : Finset X) : Subgroup (Lamp K X) where
  carrier := {f | ∀ x : X, x ∉ S → (f : X → K) x = 1}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro f g hf hg x hx
    show (f : X → K) x * (g : X → K) x = 1
    rw [hf x hx, hg x hx, one_mul]
  inv_mem' := by
    intro f hf x hx
    show ((f : X → K) x)⁻¹ = 1
    rw [hf x hx, inv_one]

theorem mem_suppIn {S : Finset X} {f : Lamp K X} :
    f ∈ suppIn (K := K) S ↔ ∀ x : X, x ∉ S → (f : X → K) x = 1 := Iff.rfl

/-- **The lamp group over a finite lamp group is locally finite.**  Every
finitely generated subgroup is supported on a finite set of sites, hence embeds
in a finite product of copies of the lamp group.

Together with `lamp_isResiduallyFinite` this says the invisible radical of the
wreath construction is intrinsically as tame as possible: locally finite and
residually finite.  What fails is extending its models through the compressed
action, not approximating it on its own. -/
theorem suppIn_finite [Finite K] (S : Finset X) :
    Finite ↥(suppIn (K := K) S) := by
  classical
  have hinj : Function.Injective
      (fun f : ↥(suppIn (K := K) S) => fun x : {x : X // x ∈ S} =>
        ((f : Lamp K X) : X → K) (x : X)) := by
    intro f g hfg
    refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    by_cases hx : x ∈ S
    · exact congrFun hfg ⟨x, hx⟩
    · rw [(mem_suppIn.mp f.2) x hx, (mem_suppIn.mp g.2) x hx]
  exact Finite.of_injective _ hinj

end LocallyFinite

end GroupApproximation

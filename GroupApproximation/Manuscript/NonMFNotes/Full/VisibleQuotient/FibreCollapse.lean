import GroupApproximation.Algebra.WreathLampPushforward
import GroupApproximation.Algebra.PermutationalWreathSimple
import GroupApproximation.Meta.AxiomGuard

/-!
# Collapsing lamps along fibres, through the abelianization

**thm:notes-visible-quotient**, the algebraic step of the proof.  After the
spectral-motion step, a normal subgroup `R` of the wreath product
`K^{(X)} ⋊ G` contains every difference of equal lamp values at two sites of
the same fibre of a site map `q : X → Y`.  If every fibre has at least two
sites, `R` contains the whole kernel of the map

`K^{(X)} ⋊ G → (K_ab)^{(Y)} ⋊ G`,

which abelianizes the lamp values and multiplies them along the fibres of `q`.

The argument is the one in the notes.  Modulo `R`, lamps at two sites of the
same fibre agree.  Each fibre has a second site, and lamps at distinct sites
commute, so the lamp values at any one site commute modulo `R`.  Hence
commutator values die, and only the abelianized fibre products survive.  The
formal proof inducts on the size of the support.

* `lampValueHom`, `wreathValueHom` -- applying a homomorphism to lamp values.
* `lampValueHom_surjective` -- surjective when the value map is.
* `pushHom_surjective` -- the fibre product is onto when `q` is.
* `map_eq_one_of_pushHom_eq_one` -- the lamp-level collapse, into any group.
* `ker_pushWreath_comp_le` -- the wreath-level collapse into a normal subgroup.
-/

namespace GroupApproximation.Full.NN04

open SemidirectProduct GroupApproximation.WreathLampPushforward
open scoped commutatorElement

universe u v w x

section Values

variable {K : Type u} [Group K] {A : Type w} [Group A] {X : Type v}

/-- Apply a homomorphism of lamp groups to every lamp value. -/
def lampValueHom (φ : K →* A) : Lamp K X →* Lamp A X where
  toFun f := ⟨fun y => φ (f.toFun y), by
    show {y : X | φ (f.toFun y) ≠ 1}.Finite
    refine Set.Finite.subset (show {y : X | f.toFun y ≠ 1}.Finite from f.2) ?_
    intro y hy
    simp only [Set.mem_setOf_eq] at hy ⊢
    intro hfy
    exact hy (by rw [hfy, map_one])⟩
  map_one' := Lamp.ext fun _ => map_one φ
  map_mul' f g := Lamp.ext fun y => map_mul φ (f.toFun y) (g.toFun y)

@[simp] theorem lampValueHom_apply (φ : K →* A) (f : Lamp K X) (y : X) :
    (lampValueHom φ f).toFun y = φ (f.toFun y) := rfl

theorem lampValueHom_single [DecidableEq X] (φ : K →* A) (y : X) (k : K) :
    lampValueHom φ (Lamp.single y k) = Lamp.single y (φ k) := by
  refine Lamp.ext fun z => ?_
  rw [lampValueHom_apply]
  by_cases h : z = y
  · rw [h, Lamp.single_apply_self, Lamp.single_apply_self]
  · rw [Lamp.single_apply_of_ne h, Lamp.single_apply_of_ne h, map_one]

theorem lampValueHom_lampAut {G : Type x} [Group G] [MulAction G X] (φ : K →* A)
    (g : G) (f : Lamp K X) :
    lampValueHom φ (lampAut g f) = lampAut g (lampValueHom φ f) :=
  Lamp.ext fun _ => rfl

/-- A surjective value map gives a surjective map of lamp groups. -/
theorem lampValueHom_surjective {φ : K →* A} (hφ : Function.Surjective φ) :
    Function.Surjective (lampValueHom (X := X) φ) := by
  classical
  intro f
  have hle : Subgroup.closure {g : Lamp A X | ∃ (y : X) (a : A), g = Lamp.single y a}
      ≤ (lampValueHom (X := X) φ).range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨y, a, rfl⟩
    obtain ⟨k, rfl⟩ := hφ a
    rw [SetLike.mem_coe, MonoidHom.mem_range]
    exact ⟨Lamp.single y k, lampValueHom_single φ y k⟩
  exact MonoidHom.mem_range.mp (hle (Lamp.mem_closure_singles f))

/-- Apply a homomorphism to the lamp values of a permutational wreath product,
keeping the acting group. -/
def wreathValueHom {G : Type x} [Group G] [MulAction G X] (φ : K →* A) :
    Wreath K G X →* Wreath A G X :=
  SemidirectProduct.map (lampValueHom φ) (MonoidHom.id G) (by
    intro g
    refine MonoidHom.ext fun f => ?_
    show lampValueHom φ (lampAut g f) = lampAut g (lampValueHom φ f)
    exact lampValueHom_lampAut φ g f)

@[simp] theorem wreathValueHom_left {G : Type x} [Group G] [MulAction G X]
    (φ : K →* A) (w : Wreath K G X) :
    (wreathValueHom φ w).left = lampValueHom φ w.left := rfl

@[simp] theorem wreathValueHom_right {G : Type x} [Group G] [MulAction G X]
    (φ : K →* A) (w : Wreath K G X) :
    (wreathValueHom φ w).right = w.right := rfl

end Values

section Push

variable {A : Type u} [CommGroup A] {X : Type v} {Y : Type w}

/-- The fibre product is onto when the site map is. -/
theorem pushHom_surjective {q : X → Y} (hq : Function.Surjective q) :
    Function.Surjective (pushHom (K := A) q) := by
  classical
  intro f
  have hle : Subgroup.closure {g : Lamp A Y | ∃ (y : Y) (a : A), g = Lamp.single y a}
      ≤ (pushHom (K := A) q).range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨y, a, rfl⟩
    obtain ⟨z, rfl⟩ := hq y
    rw [SetLike.mem_coe, MonoidHom.mem_range]
    exact ⟨Lamp.single z a, push_single q z a⟩
  exact MonoidHom.mem_range.mp (hle (Lamp.mem_closure_singles f))

end Push

section Collapse

variable {K : Type u} [Group K] {X : Type v} [DecidableEq X] {Y : Type w}
variable {H : Type x} [Group H]

/-- If the lamp values at each single site commute in the image, then every
commutator value at that site dies. -/
theorem map_single_eq_one_of_of_eq_one (ψ : Lamp K X →* H) (y : X)
    (hcomm : ∀ k l : K, Commute (ψ (Lamp.single y k)) (ψ (Lamp.single y l)))
    {c : K} (hc : Abelianization.of c = 1) : ψ (Lamp.single y c) = 1 := by
  have hcm : c ∈ commutator K := by
    rw [← Abelianization.ker_of]
    exact MonoidHom.mem_ker.mpr hc
  have hle : commutator K ≤ (ψ.comp (Lamp.singleHom y)).ker := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro _ ⟨a, b, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_commute]
    exact hcomm a b
  exact MonoidHom.mem_ker.mp (hle hcm)

/-- **thm:notes-visible-quotient, the lamp-level collapse.**  Suppose a
homomorphism `ψ` on the lamp group identifies equal lamp values at two sites of
the same fibre of `q`, and every fibre has a second site.  Then `ψ` kills every
configuration whose abelianized fibre products are all trivial. -/
theorem map_eq_one_of_pushHom_eq_one (ψ : Lamp K X →* H) (q : X → Y)
    (h1 : ∀ (y y' : X) (k : K), q y = q y' →
      ψ (Lamp.single y k) = ψ (Lamp.single y' k))
    (hfib : ∀ y : X, ∃ y' : X, y' ≠ y ∧ q y' = q y)
    {f : Lamp K X} (hf : pushHom q (lampValueHom Abelianization.of f) = 1) :
    ψ f = 1 := by
  classical
  have hcomm : ∀ (y : X) (k l : K),
      Commute (ψ (Lamp.single y k)) (ψ (Lamp.single y l)) := by
    intro y k l
    obtain ⟨y', hne, hq⟩ := hfib y
    rw [h1 y y' l hq.symm]
    exact (show Commute (Lamp.single y k) (Lamp.single y' l) from
      Lamp.single_commute hne.symm k l).map ψ
  have hCsingle : ∀ (z : X) (c : K),
      pushHom q (lampValueHom Abelianization.of (Lamp.single z c))
        = Lamp.single (q z) (Abelianization.of c) := by
    intro z c
    rw [lampValueHom_single]
    exact push_single q z (Abelianization.of c)
  have key : ∀ (n : ℕ) (f : Lamp K X), f.support.card ≤ n →
      pushHom q (lampValueHom Abelianization.of f) = 1 → ψ f = 1 := by
    intro n
    induction n with
    | zero =>
        intro f hcard _
        rw [Lamp.support_eq_empty_iff.mp
          (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)), map_one]
    | succ n ih =>
        intro f hcard hker
        by_cases hempty : f.support = ∅
        · rw [Lamp.support_eq_empty_iff.mp hempty, map_one]
        obtain ⟨y, hy⟩ := Finset.nonempty_of_ne_empty hempty
        obtain ⟨k, hk⟩ : ∃ k : K, k = f.toFun y := ⟨_, rfl⟩
        obtain ⟨g, hg⟩ : ∃ g : Lamp K X, g = f * (Lamp.single y k)⁻¹ := ⟨_, rfl⟩
        have hgsub : g.support ⊆ f.support.erase y := by
          rw [hg, hk]
          exact Lamp.support_mul_single_inv_subset f y
        have hcardg : g.support.card ≤ n := by
          have hle := Finset.card_le_card hgsub
          rw [Finset.card_erase_of_mem hy] at hle
          omega
        have hfg : f = g * Lamp.single y k := by
          rw [hg, inv_mul_cancel_right]
        have hCf : pushHom q (lampValueHom Abelianization.of g)
            * Lamp.single (q y) (Abelianization.of k) = 1 := by
          have h2 := hker
          rw [hfg, map_mul, map_mul, hCsingle] at h2
          exact h2
        by_cases hA : ∃ y' ∈ g.support, q y' = q y
        · -- another site of the same fibre carries a lamp: move the value there
          obtain ⟨y', hy', hqy'⟩ := hA
          have hsub' : (g * Lamp.single y' k).support ⊆ g.support := by
            intro z hz
            by_cases hzy : z = y'
            · rw [hzy]
              exact hy'
            · rw [Lamp.mem_support, Lamp.mul_apply, Lamp.single_apply_of_ne hzy,
                mul_one] at hz
              exact Lamp.mem_support.mpr hz
          have hcard' : (g * Lamp.single y' k).support.card ≤ n :=
            le_trans (Finset.card_le_card hsub') hcardg
          have hψ : ψ (g * Lamp.single y' k) = ψ f := by
            rw [hfg, map_mul, map_mul, h1 y' y k hqy']
          have hC : pushHom q (lampValueHom Abelianization.of
              (g * Lamp.single y' k)) = 1 := by
            rw [map_mul, map_mul, hCsingle, hqy']
            exact hCf
          rw [← hψ]
          exact ih _ hcard' hC
        · -- the value at `y` is alone in its fibre, so it is a commutator
          have hA' : ∀ z ∈ g.support, q z ≠ q y := fun z hz hqz => hA ⟨z, hz, hqz⟩
          have hCg : (pushHom q (lampValueHom Abelianization.of g)).toFun (q y)
              = 1 := by
            show pushFun q (lampValueHom Abelianization.of g) (q y) = 1
            rw [pushFun]
            refine Finset.prod_eq_one fun z hz => ?_
            rw [Finset.mem_filter] at hz
            exfalso
            refine hA' z ?_ hz.2
            rw [Lamp.mem_support]
            intro hgz
            exact (mem_supp.mp hz.1) (by rw [lampValueHom_apply, hgz, map_one])
          have hofk : Abelianization.of k = 1 := by
            have h2 : (pushHom q (lampValueHom Abelianization.of g)
                * Lamp.single (q y) (Abelianization.of k)).toFun (q y)
                = (1 : Lamp (Abelianization K) Y).toFun (q y) := by
              rw [hCf]
            rw [Lamp.mul_apply, Lamp.single_apply_self, Lamp.one_apply, hCg,
              one_mul] at h2
            exact h2
          have hψs : ψ (Lamp.single y k) = 1 :=
            map_single_eq_one_of_of_eq_one ψ y (hcomm y) hofk
          have hCg1 : pushHom q (lampValueHom Abelianization.of g) = 1 := by
            have h2 := hCf
            rw [hofk, Lamp.single_one, mul_one] at h2
            exact h2
          rw [hfg, map_mul, hψs, mul_one]
          exact ih g hcardg hCg1
  exact key _ f le_rfl hf

/-- **thm:notes-visible-quotient, the wreath-level collapse.**  A normal
subgroup containing every equal-value lamp difference along the fibres of an
equivariant site map `q` contains the whole kernel of the map that abelianizes
the lamp values and multiplies them along the fibres, provided every fibre has
a second site. -/
theorem ker_pushWreath_comp_le {G : Type x} [Group G] [MulAction G X]
    [MulAction G Y] (R : Subgroup (Wreath K G X)) [R.Normal] (q : X → Y)
    (hq : ∀ (g : G) (y : X), q (g • y) = g • q y)
    (h1 : ∀ (y y' : X) (k : K), q y = q y' →
      (inl (Lamp.single y k * (Lamp.single y' k)⁻¹) : Wreath K G X) ∈ R)
    (hfib : ∀ y : X, ∃ y' : X, y' ≠ y ∧ q y' = q y) :
    ((pushWreath (K := Abelianization K) q hq).comp
      (wreathValueHom (G := G) (X := X) Abelianization.of)).ker ≤ R := by
  intro w hw
  rw [MonoidHom.mem_ker] at hw
  have hright : w.right = 1 := congrArg SemidirectProduct.right hw
  have hleft : pushHom q (lampValueHom Abelianization.of w.left) = 1 :=
    congrArg SemidirectProduct.left hw
  have hw' : w = inl w.left := SemidirectProduct.ext rfl hright
  have hψ1 : ∀ (y y' : X) (k : K), q y = q y' →
      ((QuotientGroup.mk' R).comp (inl : Lamp K X →* Wreath K G X))
          (Lamp.single y k)
        = ((QuotientGroup.mk' R).comp (inl : Lamp K X →* Wreath K G X))
          (Lamp.single y' k) := by
    intro y y' k hqy
    have h2 : ((QuotientGroup.mk' R).comp (inl : Lamp K X →* Wreath K G X))
        (Lamp.single y k * (Lamp.single y' k)⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff (N := R)
        (inl (Lamp.single y k * (Lamp.single y' k)⁻¹))).mpr (h1 y y' k hqy)
    rw [map_mul, map_inv, mul_inv_eq_one] at h2
    exact h2
  have hone := map_eq_one_of_pushHom_eq_one
    ((QuotientGroup.mk' R).comp (inl : Lamp K X →* Wreath K G X)) q hψ1 hfib hleft
  rw [hw']
  exact (QuotientGroup.eq_one_iff (N := R) (inl w.left)).mp hone

#audit_axioms lampValueHom_surjective
#audit_axioms pushHom_surjective
#audit_axioms map_single_eq_one_of_of_eq_one
#audit_axioms map_eq_one_of_pushHom_eq_one
#audit_axioms ker_pushWreath_comp_le

end Collapse

end GroupApproximation.Full.NN04

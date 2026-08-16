import GroupApproximation.Algebra.PermutationalWreath

/-!
# Section 37.1: pushforward of finitely supported lamps

For an abelian lamp group and any map of sites `q : X → Y`, a finitely supported
configuration pushes forward by multiplying along the fibres,

`(q_* f)(y) = ∏_{x ∈ q⁻¹(y)} f(x)`,

a finite product because `f` has finite support.  Commutativity of the lamp
group is what makes the order immaterial.  The pushforward is a homomorphism,
and it is equivariant whenever `q` is, so it extends to the permutational wreath
products with the identity on the acting group -- the map the telescope tower of
Section 37 iterates.
-/

namespace GroupApproximation

namespace LampPushforward

universe u v w

variable {K : Type u} [CommGroup K] {X : Type v} {Y : Type w}

/-- The support of a configuration, as a finite set. -/
noncomputable def supp (f : Lamp K X) : Finset X :=
  (f.2 : {x : X | f.toFun x ≠ 1}.Finite).toFinset

theorem mem_supp {f : Lamp K X} {x : X} : x ∈ supp f ↔ f.toFun x ≠ 1 :=
  Set.Finite.mem_toFinset _

open scoped Classical in
/-- The fibrewise product defining the pushforward. -/
noncomputable def pushFun (q : X → Y) (f : Lamp K X) : Y → K :=
  fun y => ∏ x ∈ (supp f).filter (fun x => q x = y), f.toFun x

open scoped Classical in
/-- The pushforward may be computed over any finite set containing the
support. -/
theorem pushFun_eq_of_subset (q : X → Y) (f : Lamp K X) {T : Finset X}
    (hT : supp f ⊆ T) (y : Y) :
    pushFun q f y = ∏ x ∈ T.filter (fun x => q x = y), f.toFun x := by
  classical
  rw [pushFun]
  refine Finset.prod_subset (Finset.filter_subset_filter _ hT) fun x hx hxn => ?_
  rw [Finset.mem_filter] at hx
  have hnot : x ∉ supp f := by
    intro hcon
    exact hxn (Finset.mem_filter.mpr ⟨hcon, hx.2⟩)
  by_contra hne
  exact hnot (mem_supp.mpr hne)

theorem pushFun_ne_one (q : X → Y) (f : Lamp K X) {y : Y}
    (hy : pushFun q f y ≠ 1) : ∃ x ∈ supp f, q x = y := by
  classical
  by_contra hcon
  push Not at hcon
  apply hy
  rw [pushFun, Finset.filter_eq_empty_iff.mpr (fun x hx => hcon x hx),
    Finset.prod_empty]

/-- The pushforward of a finitely supported configuration. -/
noncomputable def push (q : X → Y) (f : Lamp K X) : Lamp K Y := by
  classical
  refine ⟨pushFun q f, ?_⟩
  show {y : Y | pushFun q f y ≠ 1}.Finite
  refine Set.Finite.subset (Set.Finite.image q (supp f).finite_toSet) ?_
  intro y hy
  obtain ⟨x, hx, hxy⟩ := pushFun_ne_one q f hy
  exact ⟨x, hx, hxy⟩

@[simp] theorem push_apply (q : X → Y) (f : Lamp K X) (y : Y) :
    (push q f).toFun y = pushFun q f y := rfl

theorem push_mul (q : X → Y) (f g : Lamp K X) :
    push q (f * g) = push q f * push q g := by
  classical
  refine Lamp.ext fun y => ?_
  rw [push_apply, Lamp.mul_apply, push_apply, push_apply]
  set T : Finset X := supp f ∪ supp g ∪ supp (f * g) with hT
  have hf : supp f ⊆ T :=
    Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left
  have hg : supp g ⊆ T :=
    Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left
  have hfg : supp (f * g) ⊆ T := Finset.subset_union_right
  rw [pushFun_eq_of_subset q f hf, pushFun_eq_of_subset q g hg,
    pushFun_eq_of_subset q (f * g) hfg, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun x _ => Lamp.mul_apply f g x

/-- The pushforward as a homomorphism of lamp groups. -/
noncomputable def pushHom (q : X → Y) : Lamp K X →* Lamp K Y where
  toFun := push q
  map_one' := by
    classical
    refine Lamp.ext fun y => ?_
    rw [push_apply, pushFun, Lamp.one_apply]
    refine Finset.prod_eq_one fun x hx => ?_
    exact Lamp.one_apply x
  map_mul' := push_mul q

/-! ## Equivariance and the wreath-level map -/

section Equivariant

variable {G : Type*} [Group G] [MulAction G X] [MulAction G Y]

theorem supp_lampAut [DecidableEq X] (g : G) (f : Lamp K X) :
    supp (lampAut (K := K) g f) = (supp f).image (fun x => g • x) := by
  classical
  ext x
  rw [mem_supp, Finset.mem_image]
  constructor
  · intro hx
    refine ⟨g⁻¹ • x, mem_supp.mpr ?_, by rw [smul_inv_smul]⟩
    rw [lampAut_apply] at hx
    exact hx
  · rintro ⟨x', hx', rfl⟩
    rw [lampAut_apply, inv_smul_smul]
    exact mem_supp.mp hx'

/-- The pushforward is equivariant along an equivariant map of sites. -/
theorem push_lampAut (q : X → Y) (hq : ∀ (g : G) (x : X), q (g • x) = g • q x)
    (g : G) (f : Lamp K X) :
    push q (lampAut (K := K) g f) = lampAut g (push q f) := by
  classical
  refine Lamp.ext fun y => ?_
  rw [push_apply, lampAut_apply, push_apply, pushFun, pushFun, supp_lampAut]
  have hfilter : ((supp f).image (fun x => g • x)).filter (fun x => q x = y)
      = ((supp f).filter (fun x => q x = g⁻¹ • y)).image (fun x => g • x) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨x', hx', rfl⟩, hq'⟩
      refine ⟨x', ⟨hx', ?_⟩, rfl⟩
      rw [hq] at hq'
      rw [← hq', inv_smul_smul]
    · rintro ⟨x', ⟨hx', hq'⟩, rfl⟩
      refine ⟨⟨x', hx', rfl⟩, ?_⟩
      rw [hq, hq', smul_inv_smul]
  rw [hfilter, Finset.prod_image (fun a _ b _ hab => by
    simpa using congrArg (fun z => g⁻¹ • z) hab)]
  exact Finset.prod_congr rfl fun x _ => by rw [lampAut_apply, inv_smul_smul]

/-- **Section 37.1.**  The pushforward extends to the permutational wreath
products, acting as the identity on the acting group. -/
noncomputable def pushWreath (q : X → Y)
    (hq : ∀ (g : G) (x : X), q (g • x) = g • q x) :
    Wreath K G X →* Wreath K G Y :=
  SemidirectProduct.map (pushHom q) (MonoidHom.id G) (by
    intro g
    refine MonoidHom.ext fun f => ?_
    show push q (lampAut g f) = lampAut g (push q f)
    exact push_lampAut q hq g f)

@[simp] theorem pushWreath_left (q : X → Y)
    (hq : ∀ (g : G) (x : X), q (g • x) = g • q x) (w : Wreath K G X) :
    (pushWreath q hq w).left = push q w.left := rfl

@[simp] theorem pushWreath_right (q : X → Y)
    (hq : ∀ (g : G) (x : X), q (g • x) = g • q x) (w : Wreath K G X) :
    (pushWreath q hq w).right = w.right := rfl

end Equivariant

end LampPushforward

end GroupApproximation

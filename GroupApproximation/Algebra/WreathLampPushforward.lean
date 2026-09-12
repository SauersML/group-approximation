import GroupApproximation.Algebra.PermutationalWreath
import Mathlib.Tactic.Group

/-!
# Section 37.1: pushforward of finitely supported wreath lamps

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

namespace WreathLampPushforward

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

/-! ## The kernel of the pushforward -/

section Kernel

variable [DecidableEq X] [DecidableEq Y] [DecidableEq K]

theorem supp_single (x : X) (k : K) :
    supp (Lamp.single x k) = if k = 1 then (∅ : Finset X) else {x} := by
  classical
  ext z
  rw [mem_supp]
  by_cases hk : k = 1
  · rw [if_pos hk]
    simp only [Finset.notMem_empty, iff_false, not_not]
    by_cases hz : z = x
    · rw [hz, Lamp.single_apply_self, hk]
    · rw [Lamp.single_apply_of_ne hz]
  · rw [if_neg hk, Finset.mem_singleton]
    constructor
    · intro hz
      by_contra hne
      exact hz (Lamp.single_apply_of_ne hne k)
    · rintro rfl
      rw [Lamp.single_apply_self]
      exact hk

theorem push_single (q : X → Y) (x : X) (k : K) :
    push q (Lamp.single x k) = Lamp.single (q x) k := by
  classical
  refine Lamp.ext fun y => ?_
  rw [push_apply, pushFun, supp_single]
  by_cases hk : k = 1
  · rw [if_pos hk, Finset.filter_empty, Finset.prod_empty, hk, Lamp.single_one]
    rfl
  · rw [if_neg hk]
    by_cases hy : y = q x
    · rw [hy, Finset.filter_singleton, if_pos rfl, Finset.prod_singleton,
        Lamp.single_apply_self, Lamp.single_apply_self]
    · rw [Finset.filter_singleton, if_neg (fun hcon => hy hcon.symm),
        Finset.prod_empty, Lamp.single_apply_of_ne hy]

/-- The same-fibre differences: the relations the pushforward imposes. -/
def fiberDiffs (q : X → Y) : Set (Lamp K X) :=
  {w | ∃ (x x' : X) (k : K), q x = q x' ∧
    w = Lamp.single x k * (Lamp.single x' k)⁻¹}

theorem fiberDiffs_le_ker (q : X → Y) :
    Subgroup.closure (fiberDiffs (K := K) q) ≤ (pushHom q).ker := by
  rw [Subgroup.closure_le]
  rintro w ⟨x, x', k, hq, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv]
  show push q (Lamp.single x k) * (push q (Lamp.single x' k))⁻¹ = 1
  rw [push_single, push_single, hq, mul_inv_cancel]

theorem mem_closure_fiberDiffs_of_mem_ker (q : X → Y) :
    ∀ (n : ℕ) (f : Lamp K X), (supp f).card ≤ n → pushHom q f = 1 →
      f ∈ Subgroup.closure (fiberDiffs (K := K) q) := by
  classical
  intro n
  induction n with
  | zero =>
      intro f hcard _
      have hempty : supp f = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      have hone : f = 1 := by
        refine Lamp.ext fun x => ?_
        by_contra hne
        have hmem : x ∈ supp f := mem_supp.mpr hne
        rw [hempty] at hmem
        exact absurd hmem (Finset.notMem_empty x)
      rw [hone]
      exact one_mem _
  | succ n ih =>
      intro f hcard hker
      by_cases hempty : supp f = ∅
      · have hone : f = 1 := by
          refine Lamp.ext fun x => ?_
          by_contra hne
          have hmem : x ∈ supp f := mem_supp.mpr hne
          rw [hempty] at hmem
          exact absurd hmem (Finset.notMem_empty x)
        rw [hone]
        exact one_mem _
      obtain ⟨x, hx⟩ := Finset.nonempty_of_ne_empty hempty
      have hfib : ∏ z ∈ (supp f).filter (fun z => q z = q x), f.toFun z = 1 := by
        have h1 := congrArg (fun w : Lamp K Y => w.toFun (q x)) hker
        simp only [pushHom, MonoidHom.coe_mk, OneHom.coe_mk, push_apply,
          pushFun, Lamp.one_apply] at h1
        rw [Finset.filter_congr_decidable] at h1
        exact h1
      obtain ⟨x', hx', hqx', hne⟩ : ∃ x' ∈ supp f, q x' = q x ∧ x' ≠ x := by
        by_contra hcon
        push Not at hcon
        have hsingle : (supp f).filter (fun z => q z = q x) = {x} := by
          ext z
          rw [Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨hz, hqz⟩
            by_contra hzx
            exact hzx (by simpa using hcon z hz hqz)
          · rintro rfl
            exact ⟨hx, rfl⟩
        rw [hsingle, Finset.prod_singleton] at hfib
        exact (mem_supp.mp hx) hfib
      set k : K := f.toFun x with hk
      set w : Lamp K X := Lamp.single x k * (Lamp.single x' k)⁻¹ with hw
      have hwmem : w ∈ fiberDiffs (K := K) q := ⟨x, x', k, hqx'.symm, rfl⟩
      set g : Lamp K X := f * w⁻¹ with hg
      have hgval : ∀ z : X, g.toFun z
          = f.toFun z * ((Lamp.single x' k).toFun z
            * ((Lamp.single x k).toFun z)⁻¹) := by
        intro z
        rw [hg, hw, Lamp.mul_apply, Lamp.inv_apply, Lamp.mul_apply,
          Lamp.inv_apply]
        group
      have hgx : g.toFun x = 1 := by
        rw [hgval x, Lamp.single_apply_of_ne hne.symm, Lamp.single_apply_self,
          hk]
        group
      have hsuppg : supp g ⊆ (supp f).erase x := by
        intro z hz
        rw [Finset.mem_erase]
        refine ⟨?_, ?_⟩
        · intro hzx
          rw [hzx] at hz
          exact (mem_supp.mp hz) hgx
        · by_contra hnotf
          have hfz : f.toFun z = 1 := by
            by_contra hne'
            exact hnotf (mem_supp.mpr hne')
          have hzx : z ≠ x := by
            intro hzx
            rw [hzx] at hnotf
            exact hnotf hx
          have hzx' : z ≠ x' := by
            intro hzx'
            rw [hzx'] at hnotf
            exact hnotf hx'
          have hgz : g.toFun z = 1 := by
            rw [hgval z, hfz, one_mul, Lamp.single_apply_of_ne hzx',
              Lamp.single_apply_of_ne hzx]
            group
          exact (mem_supp.mp hz) hgz
      have hcardg : (supp g).card ≤ n := by
        have hlt : (supp g).card < (supp f).card :=
          lt_of_le_of_lt (Finset.card_le_card hsuppg)
            (Finset.card_erase_lt_of_mem hx)
        omega
      have hkerg : pushHom q g = 1 := by
        rw [hg, map_mul, map_inv, hker, one_mul, inv_eq_one]
        exact MonoidHom.mem_ker.mp
          (fiberDiffs_le_ker q (Subgroup.subset_closure hwmem))
      have hgmem := ih g hcardg hkerg
      have hfactor : f = g * w := by
        rw [hg]
        group
      rw [hfactor]
      exact mul_mem hgmem (Subgroup.subset_closure hwmem)

/-- **Lemma 37.2, algebraic half.**  The kernel of the pushforward is generated
by the same-fibre differences. -/
theorem ker_pushHom (q : X → Y) :
    (pushHom (K := K) q).ker = Subgroup.closure (fiberDiffs (K := K) q) := by
  refine le_antisymm (fun f hf => ?_) (fiberDiffs_le_ker q)
  exact mem_closure_fiberDiffs_of_mem_ker q (supp f).card f (le_refl _)
    (MonoidHom.mem_ker.mp hf)

end Kernel

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

end WreathLampPushforward

end GroupApproximation

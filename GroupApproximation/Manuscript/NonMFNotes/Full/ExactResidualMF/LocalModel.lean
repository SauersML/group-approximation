import GroupApproximation.Sofic.Sofic
import GroupApproximation.Sofic.WeakMFNonsoficDouble
import Mathlib.GroupTheory.ResiduallyFinite
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Prod
import Mathlib.Algebra.Group.End
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sum
import Mathlib.Data.Finset.Prod

/-!
# Finite local models of the symmetric double

Source: `non_mf_group_notes.tex`, proof of `thm:exact-mf-residual`
(l.1826), following Shulman (arXiv:2603.13564), Theorem 10.

For a residually finite group `G`, a subgroup `Γ` and a finite set `B` of elements of the
symmetric double `G *_Γ G`, we build a finite set `Y` with two actions of `G` (one per copy)
and a map `ι : G *_Γ G → Y` which is injective on `B` and intertwines left multiplication by
either copy of `G` whenever both endpoints lie in `B`.

Construction.  For each copy `b`, every element `x` of the double is written as
`x = inDouble b (h_b x) * r_b x`, where `r_b x` is a canonical representative of the orbit
of `x` under left multiplication by the copy `b` of `G`.  The finite model for copy `b` is
`Option T × G ⧸ K`, where `T` is the (finite) set of representatives of `B` and `K` is a
finite-index subgroup avoiding the finitely many nontrivial differences of coordinates,
supplied by residual finiteness.  The two copies are glued on the disjoint union with a
permutation matching the two embeddings of `B`.
-/

namespace GroupApproximation.Full.NN01b.LocalModel

open GroupApproximation

/-- A finite-index subgroup avoiding finitely many nontrivial elements. -/
theorem exists_finiteIndex_avoid (G : Type) [Group G] [Group.ResiduallyFinite G]
    (S : Finset G) :
    ∃ K : Subgroup G, K.FiniteIndex ∧ ∀ s ∈ S, s ≠ 1 → s ∉ K := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨⊤, inferInstance, fun s hs => absurd hs (Finset.notMem_empty s)⟩
  | insert a S _ ih =>
    obtain ⟨K, _, hKS⟩ := ih
    by_cases ha1 : a = 1
    · refine ⟨K, inferInstance, fun s hs hs1 => ?_⟩
      rcases Finset.mem_insert.mp hs with hsa | hs'
      · exact absurd (hsa.trans ha1) hs1
      · exact hKS s hs' hs1
    · obtain ⟨L, _, haL⟩ :=
        Group.residuallyFinite_iff_exists_finiteIndex.mp ‹Group.ResiduallyFinite G› a ha1
      refine ⟨K ⊓ L, inferInstance, fun s hs hs1 hmem => ?_⟩
      rcases Finset.mem_insert.mp hs with hsa | hs'
      · apply haL
        rw [← hsa]
        exact (Subgroup.mem_inf.mp hmem).2
      · exact hKS s hs' hs1 (Subgroup.mem_inf.mp hmem).1

/-- `r` lies in the orbit of `x` under left multiplication by the copy `b` of `G`. -/
def copyOrbit (G : Type) [Group G] (Γ : Subgroup G) (b : Bool)
    (x r : SymmetricDouble G Γ) : Prop :=
  ∃ g : G, inDouble G Γ b g * r = x

theorem copyOrbit_mul (G : Type) [Group G] (Γ : Subgroup G) (b : Bool) (g : G)
    (x : SymmetricDouble G Γ) :
    copyOrbit G Γ b (inDouble G Γ b g * x) = copyOrbit G Γ b x := by
  funext r
  apply propext
  show (∃ k : G, inDouble G Γ b k * r = inDouble G Γ b g * x) ↔
    ∃ k : G, inDouble G Γ b k * r = x
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨g⁻¹ * k, by rw [map_mul, mul_assoc, hk, map_inv, inv_mul_cancel_left]⟩
  · rintro ⟨k, hk⟩
    exact ⟨g * k, by rw [map_mul, mul_assoc, hk]⟩

/-- Canonical representative of the orbit of `x` under the copy `b` of `G`. -/
noncomputable def copyRep (G : Type) [Group G] (Γ : Subgroup G) (b : Bool)
    (x : SymmetricDouble G Γ) : SymmetricDouble G Γ :=
  @Classical.epsilon (SymmetricDouble G Γ) ⟨1⟩ (copyOrbit G Γ b x)

theorem copyRep_spec (G : Type) [Group G] (Γ : Subgroup G) (b : Bool)
    (x : SymmetricDouble G Γ) :
    ∃ g : G, inDouble G Γ b g * copyRep G Γ b x = x :=
  Classical.epsilon_spec_aux (Nonempty.intro (1 : SymmetricDouble G Γ)) (copyOrbit G Γ b x)
    ⟨x, show ∃ g : G, inDouble G Γ b g * x = x from ⟨1, by rw [map_one, one_mul]⟩⟩

theorem copyRep_mul (G : Type) [Group G] (Γ : Subgroup G) (b : Bool) (g : G)
    (x : SymmetricDouble G Γ) :
    copyRep G Γ b (inDouble G Γ b g * x) = copyRep G Γ b x :=
  congrArg (fun p => @Classical.epsilon (SymmetricDouble G Γ) ⟨1⟩ p)
    (copyOrbit_mul G Γ b g x)

/-- Coordinate of `x` along the copy `b`: `x = inDouble b (copyCoord b x) * copyRep b x`. -/
noncomputable def copyCoord (G : Type) [Group G] (Γ : Subgroup G) (b : Bool)
    (x : SymmetricDouble G Γ) : G :=
  Classical.choose (copyRep_spec G Γ b x)

theorem copyCoord_spec (G : Type) [Group G] (Γ : Subgroup G) (b : Bool)
    (x : SymmetricDouble G Γ) :
    inDouble G Γ b (copyCoord G Γ b x) * copyRep G Γ b x = x :=
  Classical.choose_spec (copyRep_spec G Γ b x)

theorem copyCoord_mul (G : Type) [Group G] (Γ : Subgroup G) (b : Bool) (g : G)
    (x : SymmetricDouble G Γ) :
    copyCoord G Γ b (inDouble G Γ b g * x) = g * copyCoord G Γ b x := by
  apply inDouble_injective G Γ b
  apply mul_right_cancel (b := copyRep G Γ b x)
  calc inDouble G Γ b (copyCoord G Γ b (inDouble G Γ b g * x)) * copyRep G Γ b x
      = inDouble G Γ b (copyCoord G Γ b (inDouble G Γ b g * x)) *
          copyRep G Γ b (inDouble G Γ b g * x) := by rw [copyRep_mul]
    _ = inDouble G Γ b g * x := copyCoord_spec G Γ b _
    _ = inDouble G Γ b g * (inDouble G Γ b (copyCoord G Γ b x) * copyRep G Γ b x) := by
        rw [copyCoord_spec G Γ b x]
    _ = inDouble G Γ b (g * copyCoord G Γ b x) * copyRep G Γ b x := by
        rw [map_mul, mul_assoc]

open scoped Classical in
/-- Tag of a representative inside a finite set of representatives. -/
noncomputable def copyTag (G : Type) [Group G] (Γ : Subgroup G)
    (T : Finset (SymmetricDouble G Γ)) (r : SymmetricDouble G Γ) : Option T :=
  if hr : r ∈ T then some ⟨r, hr⟩ else none

theorem copyTag_of_mem (G : Type) [Group G] (Γ : Subgroup G)
    {T : Finset (SymmetricDouble G Γ)} {r : SymmetricDouble G Γ} (hr : r ∈ T) :
    copyTag G Γ T r = some ⟨r, hr⟩ := by
  unfold copyTag
  exact dif_pos hr

/-- The action of `G` on `Option T × G ⧸ K` by left multiplication on the second factor. -/
noncomputable def copyAct (G : Type) [Group G] (Γ : Subgroup G)
    (T : Finset (SymmetricDouble G Γ)) (K : Subgroup G) :
    G →* Equiv.Perm (Option T × (G ⧸ K)) where
  toFun g := Equiv.prodCongr (Equiv.refl (Option T)) (MulAction.toPerm g : Equiv.Perm (G ⧸ K))
  map_one' := Equiv.ext fun p => Prod.ext rfl (one_smul G p.2)
  map_mul' g h := Equiv.ext fun p => Prod.ext rfl (mul_smul g h p.2)

/-- The embedding of the double into the finite model for copy `b`. -/
noncomputable def copyEmbed (G : Type) [Group G] (Γ : Subgroup G) (b : Bool)
    (T : Finset (SymmetricDouble G Γ)) (K : Subgroup G) (x : SymmetricDouble G Γ) :
    Option T × (G ⧸ K) :=
  (copyTag G Γ T (copyRep G Γ b x), (QuotientGroup.mk (copyCoord G Γ b x) : G ⧸ K))

theorem copyAct_embed (G : Type) [Group G] (Γ : Subgroup G) (b : Bool)
    (T : Finset (SymmetricDouble G Γ)) (K : Subgroup G) (g : G) (x : SymmetricDouble G Γ) :
    copyAct G Γ T K g (copyEmbed G Γ b T K x) =
      copyEmbed G Γ b T K (inDouble G Γ b g * x) := by
  have h1 := copyRep_mul G Γ b g x
  have h2 := copyCoord_mul G Γ b g x
  calc copyAct G Γ T K g (copyEmbed G Γ b T K x)
      = (copyTag G Γ T (copyRep G Γ b x),
          (QuotientGroup.mk (g * copyCoord G Γ b x) : G ⧸ K)) := rfl
    _ = copyEmbed G Γ b T K (inDouble G Γ b g * x) := by rw [copyEmbed, h1, h2]

theorem copyEmbed_injOn (G : Type) [Group G] (Γ : Subgroup G) (b : Bool)
    (B T : Finset (SymmetricDouble G Γ)) (K : Subgroup G)
    (hT : ∀ x ∈ B, copyRep G Γ b x ∈ T)
    (hK : ∀ x ∈ B, ∀ y ∈ B, (copyCoord G Γ b x)⁻¹ * copyCoord G Γ b y ≠ 1 →
      (copyCoord G Γ b x)⁻¹ * copyCoord G Γ b y ∉ K) :
    Set.InjOn (copyEmbed G Γ b T K) (B : Set (SymmetricDouble G Γ)) := by
  intro x hx y hy hxy
  have hx' : x ∈ B := Finset.mem_coe.mp hx
  have hy' : y ∈ B := Finset.mem_coe.mp hy
  have htag : copyTag G Γ T (copyRep G Γ b x) = copyTag G Γ T (copyRep G Γ b y) :=
    congrArg Prod.fst hxy
  rw [copyTag_of_mem G Γ (hT x hx'), copyTag_of_mem G Γ (hT y hy')] at htag
  have hrep : copyRep G Γ b x = copyRep G Γ b y :=
    congrArg Subtype.val (Option.some.inj htag)
  have hcoord : (QuotientGroup.mk (copyCoord G Γ b x) : G ⧸ K) =
      (QuotientGroup.mk (copyCoord G Γ b y) : G ⧸ K) :=
    congrArg Prod.snd hxy
  have hc : copyCoord G Γ b x = copyCoord G Γ b y := by
    by_contra hne
    exact hK x hx' y hy' (fun h => hne (inv_mul_eq_one.mp h)) (QuotientGroup.eq.mp hcoord)
  calc x = inDouble G Γ b (copyCoord G Γ b x) * copyRep G Γ b x :=
        (copyCoord_spec G Γ b x).symm
    _ = inDouble G Γ b (copyCoord G Γ b y) * copyRep G Γ b y := by rw [hrep, hc]
    _ = y := copyCoord_spec G Γ b y

/-- A finite model for one copy of `G`, exact on all of the double and injective on `B`. -/
theorem exists_copyModel (G : Type) [Group G] [Group.ResiduallyFinite G] (Γ : Subgroup G)
    (b : Bool) (B : Finset (SymmetricDouble G Γ)) :
    ∃ (Z : Type) (_ : Finite Z) (act : G →* Equiv.Perm Z) (ι : SymmetricDouble G Γ → Z),
      Set.InjOn ι (B : Set (SymmetricDouble G Γ)) ∧
      ∀ (g : G) (x : SymmetricDouble G Γ), act g (ι x) = ι (inDouble G Γ b g * x) := by
  classical
  obtain ⟨K, _, hK⟩ := exists_finiteIndex_avoid G
    ((B ×ˢ B).image fun p : SymmetricDouble G Γ × SymmetricDouble G Γ =>
      (copyCoord G Γ b p.1)⁻¹ * copyCoord G Γ b p.2)
  refine ⟨Option (B.image (copyRep G Γ b)) × (G ⧸ K), inferInstance,
    copyAct G Γ (B.image (copyRep G Γ b)) K, copyEmbed G Γ b (B.image (copyRep G Γ b)) K,
    copyEmbed_injOn G Γ b B (B.image (copyRep G Γ b)) K
      (fun x hx => Finset.mem_image_of_mem (copyRep G Γ b) hx) ?_,
    fun g x => copyAct_embed G Γ b (B.image (copyRep G Γ b)) K g x⟩
  intro x hx y hy hne
  exact hK ((copyCoord G Γ b x)⁻¹ * copyCoord G Γ b y)
    (Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩) hne

/-- Extend an action on `Z` trivially to `Z ⊕ W`. -/
def sumLeftHom {G : Type} [Group G] {Z W : Type} (a : G →* Equiv.Perm Z) :
    G →* Equiv.Perm (Z ⊕ W) where
  toFun g := Equiv.Perm.sumCongr (a g) 1
  map_one' := by
    show Equiv.Perm.sumCongr (a 1) (1 : Equiv.Perm W) = 1
    rw [map_one, Equiv.Perm.sumCongr_one]
  map_mul' g h := by
    show Equiv.Perm.sumCongr (a (g * h)) (1 : Equiv.Perm W) =
      Equiv.Perm.sumCongr (a g) 1 * Equiv.Perm.sumCongr (a h) 1
    rw [Equiv.Perm.sumCongr_mul, map_mul, one_mul]

/-- Extend an action on `W` trivially to `Z ⊕ W`. -/
def sumRightHom {G : Type} [Group G] {Z W : Type} (a : G →* Equiv.Perm W) :
    G →* Equiv.Perm (Z ⊕ W) where
  toFun g := Equiv.Perm.sumCongr 1 (a g)
  map_one' := by
    show Equiv.Perm.sumCongr (1 : Equiv.Perm Z) (a 1) = 1
    rw [map_one, Equiv.Perm.sumCongr_one]
  map_mul' g h := by
    show Equiv.Perm.sumCongr (1 : Equiv.Perm Z) (a (g * h)) =
      Equiv.Perm.sumCongr 1 (a g) * Equiv.Perm.sumCongr 1 (a h)
    rw [Equiv.Perm.sumCongr_mul, map_mul, one_mul]

/-- Conjugate an action by a permutation. -/
def conjHom {G : Type} [Group G] {Y : Type} (σ : Equiv.Perm Y) (a : G →* Equiv.Perm Y) :
    G →* Equiv.Perm Y where
  toFun g := σ * a g * σ⁻¹
  map_one' := by
    show σ * a 1 * σ⁻¹ = 1
    rw [map_one, mul_one, mul_inv_cancel]
  map_mul' g h := by
    show σ * a (g * h) * σ⁻¹ = σ * a g * σ⁻¹ * (σ * a h * σ⁻¹)
    rw [map_mul]
    simp only [mul_assoc, inv_mul_cancel_left]

theorem sumLeftHom_apply_inl {G : Type} [Group G] {Z W : Type} (a : G →* Equiv.Perm Z)
    (g : G) (z : Z) :
    sumLeftHom (W := W) a g (Sum.inl z) = Sum.inl (a g z) :=
  rfl

theorem sumRightHom_apply_inr {G : Type} [Group G] {Z W : Type} (a : G →* Equiv.Perm W)
    (g : G) (w : W) :
    sumRightHom (Z := Z) a g (Sum.inr w) = Sum.inr (a g w) :=
  rfl

theorem conjHom_apply {G : Type} [Group G] {Y : Type} (σ : Equiv.Perm Y)
    (a : G →* Equiv.Perm Y) (g : G) (y : Y) :
    conjHom σ a g y = σ (a g (σ⁻¹ y)) :=
  rfl

end GroupApproximation.Full.NN01b.LocalModel

namespace GroupApproximation.Full.NN01b

open GroupApproximation GroupApproximation.Full.NN01b.LocalModel

/-- Finite local models of the symmetric double of a residually finite group
(`thm:exact-mf-residual`, local step). -/
theorem exists_localModel
    (G : Type) [Group G] [Group.ResiduallyFinite G] (Γ : Subgroup G)
    (B : Finset (SymmetricDouble G Γ)) :
    ∃ (Y : FiniteModel) (act : Bool → G →* Equiv.Perm Y) (ι : SymmetricDouble G Γ → Y),
      Set.InjOn ι (B : Set (SymmetricDouble G Γ)) ∧
      ∀ (b : Bool) (g : G) (x : SymmetricDouble G Γ), x ∈ B → inDouble G Γ b g * x ∈ B →
        act b g (ι x) = ι (inDouble G Γ b g * x) := by
  obtain ⟨Zf, _, actF, ιf, hinjF, heqF⟩ := exists_copyModel G Γ false B
  obtain ⟨Zt, _, actT, ιt, hinjT, heqT⟩ := exists_copyModel G Γ true B
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun x : B => (Sum.inl (ιf x.1) : Zf ⊕ Zt)) (fun x : B => (Sum.inr (ιt x.1) : Zf ⊕ Zt))
    (fun x y h => Subtype.ext
      (hinjF (Finset.mem_coe.mpr x.2) (Finset.mem_coe.mpr y.2) (Sum.inl_injective h)))
    (fun x y h => Subtype.ext
      (hinjT (Finset.mem_coe.mpr x.2) (Finset.mem_coe.mpr y.2) (Sum.inr_injective h)))
  have hσ' : ∀ x ∈ B, σ (Sum.inl (ιf x)) = Sum.inr (ιt x) := fun x hx => hσ ⟨x, hx⟩
  have hσinv : ∀ x ∈ B, σ⁻¹ (Sum.inr (ιt x)) = Sum.inl (ιf x) := fun x hx =>
    Equiv.Perm.inv_eq_iff_eq.mpr (hσ' x hx).symm
  refine ⟨⟨Zf ⊕ Zt, Fintype.ofFinite _, Classical.decEq _⟩,
    fun b => cond b (sumRightHom (Z := Zf) actT) (conjHom σ (sumLeftHom (W := Zt) actF)),
    fun x => (Sum.inr (ιt x) : Zf ⊕ Zt),
    fun x hx y hy h => hinjT hx hy (Sum.inr_injective h), ?_⟩
  intro b
  cases b with
  | false =>
    intro g x hx hgx
    calc conjHom σ (sumLeftHom (W := Zt) actF) g (Sum.inr (ιt x))
        = σ (sumLeftHom (W := Zt) actF g (σ⁻¹ (Sum.inr (ιt x)))) :=
          conjHom_apply σ (sumLeftHom (W := Zt) actF) g _
      _ = σ (sumLeftHom (W := Zt) actF g (Sum.inl (ιf x))) := by rw [hσinv x hx]
      _ = σ (Sum.inl (ιf (inDouble G Γ false g * x))) := by
          rw [sumLeftHom_apply_inl, heqF]
      _ = Sum.inr (ιt (inDouble G Γ false g * x)) := hσ' _ hgx
  | true =>
    intro g x _ _
    exact (sumRightHom_apply_inr (Z := Zf) actT g (ιt x)).trans
      (congrArg (Sum.inr : Zt → Zf ⊕ Zt) (heqT g x))

end GroupApproximation.Full.NN01b

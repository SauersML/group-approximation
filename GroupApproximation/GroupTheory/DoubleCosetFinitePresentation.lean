import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Finiteness
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.End
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# Finite presentation from finitely many double cosets

Hyde–Lodha prove their simple groups finitely presented by Brown's criterion,
applied to the action on the simplicial complex whose simplices are the finite
subsets of a set `X`.  That complex is contractible, so only the cells of
dimension at most two matter for finite presentability: vertex stabilizers must be
finitely presented, edge stabilizers finitely generated, and there must be finitely
many orbits of vertices, edges and triangles.

On one orbit `X = G/H` this is a statement about the subgroup `H` alone, and
this module proves it in that form, with no complexes:

**`isFinitelyPresented_of_doubleCosets`.**  Let `H ≤ G` be finitely presented,
`T ⊆ G` a finite set with `G = ⋃_{t ∈ T} H t H`, such that `H ∩ t H t⁻¹` is
finitely generated for every `t ∈ T`, and such that for all `t', t ∈ T` the double
coset space `(H ∩ t'⁻¹ H t') \ H / (H ∩ t H t⁻¹)` is finite.  Then `G` is finitely
presented.

The three hypotheses are the vertex, edge and triangle conditions.  The proof
builds the presentation on the letters of `H` and of `T` with five finite families of
relators: the relators of `H`, conjugation along each edge
(`t · (t⁻¹ e t) · t⁻¹ = e`), `t = h` for `t ∈ T ∩ H`, one expression of each `t⁻¹`,
and one expression of each triangle word `t' a₀ t`.  In the presented group every element has the
normal form `σ(a) · t · σ(b)` (`q_mul_mem_NF`), and a normal form mapping to `1`
in `G` is `1`, so the presentation map is injective.
-/

namespace GroupApproximation
namespace DoubleCosetPresentation

/-! ## Edge stabilizers -/

section EdgeStab

variable {G : Type*} [Group G]

/-- `H ∩ t H t⁻¹`, as a subgroup of `H`: the `h ∈ H` with `t⁻¹ h t ∈ H`. -/
def edgeStab (H : Subgroup G) (t : G) : Subgroup H where
  carrier := {h | t⁻¹ * (h : G) * t ∈ H}
  one_mem' := by
    show t⁻¹ * ((1 : H) : G) * t ∈ H
    simp
  mul_mem' := by
    intro a b ha hb
    show t⁻¹ * ((a * b : H) : G) * t ∈ H
    have h : t⁻¹ * ((a * b : H) : G) * t = (t⁻¹ * (a : G) * t) * (t⁻¹ * (b : G) * t) := by
      rw [Subgroup.coe_mul]
      group
    rw [h]
    exact H.mul_mem ha hb
  inv_mem' := by
    intro a ha
    show t⁻¹ * ((a⁻¹ : H) : G) * t ∈ H
    have h : t⁻¹ * ((a⁻¹ : H) : G) * t = (t⁻¹ * (a : G) * t)⁻¹ := by
      rw [Subgroup.coe_inv]
      group
    rw [h]
    exact H.inv_mem ha

theorem mem_edgeStab {H : Subgroup G} {t : G} {h : H} :
    h ∈ edgeStab H t ↔ t⁻¹ * (h : G) * t ∈ H := Iff.rfl

/-- Conjugation `h ↦ t⁻¹ h t` from `H ∩ t H t⁻¹` into `H`. -/
def conjHom (H : Subgroup G) (t : G) : edgeStab H t →* H where
  toFun h := ⟨t⁻¹ * ((h : H) : G) * t, h.2⟩
  map_one' := by
    apply Subtype.ext
    show t⁻¹ * (((1 : edgeStab H t) : H) : G) * t = ((1 : H) : G)
    simp
  map_mul' a b := by
    apply Subtype.ext
    show t⁻¹ * (((a * b : edgeStab H t) : H) : G) * t =
      (t⁻¹ * ((a : H) : G) * t) * (t⁻¹ * ((b : H) : G) * t)
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    group

@[simp] theorem coe_conjHom (H : Subgroup G) (t : G) (h : edgeStab H t) :
    ((conjHom H t h : H) : G) = t⁻¹ * ((h : H) : G) * t := rfl

/-- `t c t⁻¹ ∈ H` for `c ∈ H ∩ t⁻¹ H t`. -/
def leftConj (H : Subgroup G) (t : G) (c : edgeStab H t⁻¹) : H :=
  ⟨t * ((c : H) : G) * t⁻¹, by
    have hc := c.2
    rwa [mem_edgeStab, inv_inv] at hc⟩

end EdgeStab

/-! ## The presentation -/

section Presentation

variable {G : Type*} [Group G] (H : Subgroup G) {n : ℕ} {s : Set (FreeGroup (Fin n))}
  (e : H ≃* PresentedGroup s) (T : Finset G)

/-- The candidate generators `Fin n ⊔ T` and their images in `G`. -/
def phi : FreeGroup (Fin n ⊕ T) →* G :=
  FreeGroup.lift (Sum.elim (fun i => ((e.symm (PresentedGroup.of i) : H) : G)) (fun t => (t : G)))

/-- The letters of `H`. -/
def iota : FreeGroup (Fin n) →* FreeGroup (Fin n ⊕ T) := FreeGroup.map Sum.inl

/-- The presentation map of `H`. -/
def piH : FreeGroup (Fin n) →* H := e.symm.toMonoidHom.comp (PresentedGroup.mk s)

theorem piH_surjective : Function.Surjective (piH H e) :=
  e.symm.surjective.comp (PresentedGroup.mk_surjective s)

@[simp] theorem phi_of_inr (t : T) : phi H e T (FreeGroup.of (Sum.inr t)) = (t : G) := by
  simp [phi]

theorem phi_iota (w : FreeGroup (Fin n)) : phi H e T (iota T w) = (piH H e w : G) := by
  have h : (phi H e T).comp (iota T) = H.subtype.comp (piH H e) := by
    refine FreeGroup.ext_hom _ _ (fun i => ?_)
    simp [phi, iota, piH, PresentedGroup.of]
  exact congrArg (fun f => f w) h

/-- The finite choices the presentation is built from. -/
structure Data where
  /-- A word for each element of `H`. -/
  wd : H → FreeGroup (Fin n)
  wd_spec : ∀ h, piH H e (wd h) = h
  /-- Generators of each edge stabilizer. -/
  E : (t : T) → Finset (edgeStab H (t : G))
  E_spec : ∀ t, Subgroup.closure (E t : Set (edgeStab H (t : G))) = ⊤
  /-- An expression `t⁻¹ = a · t₁ · b`. -/
  invL : T → H
  invT : T → T
  invR : T → H
  inv_spec : ∀ t : T, (t : G)⁻¹ = (invL t : G) * (invT t : G) * (invR t : G)
  /-- Representatives of the triangle double cosets. -/
  A : T → T → Finset H
  decC : (t' t : T) → H → edgeStab H ((t' : G)⁻¹)
  decD : (t' t : T) → H → edgeStab H (t : G)
  dec0 : T → T → H → H
  dec_mem : ∀ t' t a, dec0 t' t a ∈ A t' t
  dec_spec : ∀ t' t a, a = (decC t' t a : H) * dec0 t' t a * (decD t' t a : H)
  /-- An expression `t' a t = a' t'' b'`. -/
  outL : T → T → H → H
  outT : T → T → H → T
  outR : T → T → H → H
  out_spec : ∀ t' t (a : H), (t' : G) * (a : G) * (t : G) =
    (outL t' t a : G) * (outT t' t a : G) * (outR t' t a : G)

variable {H e T}

/-- The five finite families of relators. -/
def relators (D : Data H e T) : Set (FreeGroup (Fin n ⊕ T)) :=
  iota T '' s ∪
  (⋃ t : T, (fun x : edgeStab H (t : G) =>
    FreeGroup.of (Sum.inr t) * iota T (D.wd (conjHom H t x)) * (FreeGroup.of (Sum.inr t))⁻¹ *
      (iota T (D.wd (x : H)))⁻¹) '' (D.E t : Set (edgeStab H (t : G)))) ∪
  Set.range (fun t : T => if ht : (t : G) ∈ H then
    FreeGroup.of (Sum.inr t) * (iota T (D.wd ⟨t, ht⟩))⁻¹ else 1) ∪
  Set.range (fun t : T => (FreeGroup.of (Sum.inr t))⁻¹ *
    (iota T (D.wd (D.invL t)) * FreeGroup.of (Sum.inr (D.invT t)) *
      iota T (D.wd (D.invR t)))⁻¹) ∪
  (⋃ t' : T, ⋃ t : T, (fun a : H => FreeGroup.of (Sum.inr t') * iota T (D.wd a) *
    FreeGroup.of (Sum.inr t) * (iota T (D.wd (D.outL t' t a)) *
      FreeGroup.of (Sum.inr (D.outT t' t a)) * iota T (D.wd (D.outR t' t a)))⁻¹) ''
        (D.A t' t : Set H))

theorem relators_finite (D : Data H e T) (hs : s.Finite) : (relators D).Finite := by
  unfold relators
  refine ((((hs.image _).union ?_).union (Set.finite_range _)).union (Set.finite_range _)).union ?_
  · exact Set.finite_iUnion fun t => (D.E t).finite_toSet.image _
  · exact Set.finite_iUnion fun t' => Set.finite_iUnion fun t => (D.A t' t).finite_toSet.image _

theorem mem_relators_H (D : Data H e T) {r : FreeGroup (Fin n)} (hr : r ∈ s) :
    iota T r ∈ relators D := by
  unfold relators
  exact Or.inl (Or.inl (Or.inl (Or.inl ⟨r, hr, rfl⟩)))

theorem mem_relators_edge (D : Data H e T) (t : T) {x : edgeStab H (t : G)} (hx : x ∈ D.E t) :
    FreeGroup.of (Sum.inr t) * iota T (D.wd (conjHom H t x)) * (FreeGroup.of (Sum.inr t))⁻¹ *
      (iota T (D.wd (x : H)))⁻¹ ∈ relators D := by
  unfold relators
  exact Or.inl (Or.inl (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨t, x, Finset.mem_coe.mpr hx, rfl⟩))))

theorem mem_relators_id (D : Data H e T) (t : T) :
    (if ht : (t : G) ∈ H then FreeGroup.of (Sum.inr t) * (iota T (D.wd ⟨t, ht⟩))⁻¹ else 1) ∈
      relators D := by
  unfold relators
  exact Or.inl (Or.inl (Or.inr ⟨t, rfl⟩))

theorem mem_relators_inv (D : Data H e T) (t : T) :
    (FreeGroup.of (Sum.inr t))⁻¹ * (iota T (D.wd (D.invL t)) * FreeGroup.of (Sum.inr (D.invT t)) *
      iota T (D.wd (D.invR t)))⁻¹ ∈ relators D := by
  unfold relators
  exact Or.inl (Or.inr ⟨t, rfl⟩)

theorem mem_relators_tri (D : Data H e T) (t' t : T) {a : H} (ha : a ∈ D.A t' t) :
    FreeGroup.of (Sum.inr t') * iota T (D.wd a) * FreeGroup.of (Sum.inr t) *
      (iota T (D.wd (D.outL t' t a)) * FreeGroup.of (Sum.inr (D.outT t' t a)) *
        iota T (D.wd (D.outR t' t a)))⁻¹ ∈ relators D := by
  unfold relators
  exact Or.inr (Set.mem_iUnion.mpr ⟨t', Set.mem_iUnion.mpr ⟨t, a, Finset.mem_coe.mpr ha, rfl⟩⟩)

theorem relators_subset_ker (D : Data H e T) : relators D ⊆ ((phi H e T).ker : Set _) := by
  intro w hw
  unfold relators at hw
  rcases hw with ((((⟨r, hr, rfl⟩ | hw) | ⟨t, rfl⟩) | ⟨t, rfl⟩) | hw)
  · show phi H e T (iota T r) = 1
    rw [phi_iota]
    have hr1 : PresentedGroup.mk s r = 1 :=
      PresentedGroup.mk_eq_one_iff.mpr (Subgroup.subset_normalClosure hr)
    simp [piH, hr1]
  · obtain ⟨t, x, -, rfl⟩ := by simpa only [Set.mem_iUnion, Set.mem_image] using hw
    show phi H e T _ = 1
    simp only [map_mul, map_inv, phi_iota, D.wd_spec, phi_of_inr, coe_conjHom]
    group
  · show phi H e T _ = 1
    by_cases ht : (t : G) ∈ H
    · rw [dif_pos ht, map_mul, map_inv, phi_iota, D.wd_spec, phi_of_inr]
      exact mul_inv_cancel _
    · rw [dif_neg ht, map_one]
  · show phi H e T _ = 1
    simp only [map_mul, map_inv, phi_iota, D.wd_spec, phi_of_inr]
    rw [← D.inv_spec t]
    group
  · obtain ⟨t', t, a, -, rfl⟩ := by simpa only [Set.mem_iUnion, Set.mem_image] using hw
    show phi H e T _ = 1
    simp only [map_mul, map_inv, phi_iota, D.wd_spec, phi_of_inr]
    rw [← D.out_spec t' t a]
    group

/-- The normal closure of the relators. -/
abbrev K (D : Data H e T) : Subgroup (FreeGroup (Fin n ⊕ T)) := Subgroup.normalClosure (relators D)

/-- The presented group. -/
abbrev P (D : Data H e T) := FreeGroup (Fin n ⊕ T) ⧸ K D

/-- The quotient map onto the presented group. -/
def q (D : Data H e T) : FreeGroup (Fin n ⊕ T) →* P D := QuotientGroup.mk' (K D)

theorem q_eq_one_of_mem (D : Data H e T) {w : FreeGroup (Fin n ⊕ T)} (hw : w ∈ relators D) :
    q D w = 1 :=
  (QuotientGroup.eq_one_iff w).mpr (Subgroup.subset_normalClosure hw)

theorem lift_letters_eq (D : Data H e T) :
    FreeGroup.lift (fun i : Fin n => q D (FreeGroup.of (Sum.inl i))) = (q D).comp (iota T) :=
  FreeGroup.ext_hom _ _ (fun i => by simp [iota])

/-- The image of `H` in the presented group, through the presentation of `H`. -/
def sigma0 (D : Data H e T) : PresentedGroup s →* P D :=
  PresentedGroup.toGroup (f := fun i : Fin n => q D (FreeGroup.of (Sum.inl i))) (fun r hr => by
    rw [lift_letters_eq, MonoidHom.comp_apply]
    exact q_eq_one_of_mem D (mem_relators_H D hr))

/-- `H` inside the presented group. -/
def sigma (D : Data H e T) : H →* P D := (sigma0 D).comp e.toMonoidHom

theorem sigma0_mk (D : Data H e T) (w : FreeGroup (Fin n)) :
    sigma0 D (PresentedGroup.mk s w) = q D (iota T w) := by
  show FreeGroup.lift (fun i : Fin n => q D (FreeGroup.of (Sum.inl i))) w = _
  rw [lift_letters_eq, MonoidHom.comp_apply]

theorem q_iota (D : Data H e T) (w : FreeGroup (Fin n)) :
    q D (iota T w) = sigma D (piH H e w) := by
  show q D (iota T w) = sigma0 D (e (e.symm (PresentedGroup.mk s w)))
  rw [MulEquiv.apply_symm_apply, sigma0_mk]

theorem q_wd (D : Data H e T) (h : H) : q D (iota T (D.wd h)) = sigma D h := by
  rw [q_iota, D.wd_spec]

theorem q_inl (D : Data H e T) (i : Fin n) :
    q D (FreeGroup.of (Sum.inl i)) = sigma D (piH H e (FreeGroup.of i)) := by
  rw [← q_iota]
  simp [iota]

/-- The map from the presented group back to `G`. -/
def psi (D : Data H e T) : P D →* G :=
  QuotientGroup.lift (K D) (phi H e T) (Subgroup.normalClosure_le_normal (relators_subset_ker D))

@[simp] theorem psi_q (D : Data H e T) (w : FreeGroup (Fin n ⊕ T)) :
    psi D (q D w) = phi H e T w := rfl

theorem psi_sigma (D : Data H e T) (h : H) : psi D (sigma D h) = h := by
  obtain ⟨w, rfl⟩ := piH_surjective H e h
  rw [← q_iota, psi_q, phi_iota]

/-! ### The relations, read in the presented group -/

theorem edge (D : Data H e T) (t : T) (x : edgeStab H (t : G)) :
    q D (FreeGroup.of (Sum.inr t)) * sigma D (conjHom H t x) * (q D (FreeGroup.of (Sum.inr t)))⁻¹ =
      sigma D x := by
  have hhom : (MulAut.conj (q D (FreeGroup.of (Sum.inr t)))).toMonoidHom.comp
      ((sigma D).comp (conjHom H t)) = (sigma D).comp (edgeStab H (t : G)).subtype := by
    refine MonoidHom.eq_of_eqOn_dense (D.E_spec t) (fun y hy => ?_)
    have hrel := q_eq_one_of_mem D (mem_relators_edge D t (Finset.mem_coe.mp hy))
    simp only [map_mul, map_inv, q_wd] at hrel
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.coe_subtype]
    exact mul_inv_eq_one.mp hrel
  have h := congrArg (fun f => f x) hhom
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    Subgroup.coe_subtype] using h

theorem right_move (D : Data H e T) (t : T) (d : edgeStab H (t : G)) :
    sigma D d * q D (FreeGroup.of (Sum.inr t)) =
      q D (FreeGroup.of (Sum.inr t)) * sigma D (conjHom H t d) := by
  rw [← edge D t d]
  group

theorem left_move (D : Data H e T) (t : T) (c : edgeStab H ((t : G)⁻¹)) :
    q D (FreeGroup.of (Sum.inr t)) * sigma D c =
      sigma D (leftConj H t c) * q D (FreeGroup.of (Sum.inr t)) := by
  have hx : leftConj H t c ∈ edgeStab H (t : G) := by
    rw [mem_edgeStab]
    show (t : G)⁻¹ * ((t : G) * ((c : H) : G) * (t : G)⁻¹) * (t : G) ∈ H
    have h1 : (t : G)⁻¹ * ((t : G) * ((c : H) : G) * (t : G)⁻¹) * (t : G) = ((c : H) : G) := by
      group
    rw [h1]
    exact (c : H).2
  have hconj : conjHom H t ⟨leftConj H t c, hx⟩ = (c : H) := by
    apply Subtype.ext
    show (t : G)⁻¹ * ((t : G) * ((c : H) : G) * (t : G)⁻¹) * (t : G) = ((c : H) : G)
    group
  have h := edge D t ⟨leftConj H t c, hx⟩
  rw [hconj] at h
  rw [← h]
  group

theorem gen_of_mem (D : Data H e T) (t : T) (ht : (t : G) ∈ H) :
    q D (FreeGroup.of (Sum.inr t)) = sigma D ⟨t, ht⟩ := by
  have hrel := q_eq_one_of_mem D (mem_relators_id D t)
  rw [dif_pos ht] at hrel
  simp only [map_mul, map_inv, q_wd] at hrel
  exact mul_inv_eq_one.mp hrel

theorem gen_inv (D : Data H e T) (t : T) :
    (q D (FreeGroup.of (Sum.inr t)))⁻¹ =
      sigma D (D.invL t) * q D (FreeGroup.of (Sum.inr (D.invT t))) * sigma D (D.invR t) := by
  have hrel := q_eq_one_of_mem D (mem_relators_inv D t)
  simp only [map_mul, map_inv, q_wd] at hrel
  exact mul_inv_eq_one.mp hrel

theorem tri (D : Data H e T) (t' t : T) (a : H) (ha : a ∈ D.A t' t) :
    q D (FreeGroup.of (Sum.inr t')) * sigma D a * q D (FreeGroup.of (Sum.inr t)) =
      sigma D (D.outL t' t a) * q D (FreeGroup.of (Sum.inr (D.outT t' t a))) *
        sigma D (D.outR t' t a) := by
  have hrel := q_eq_one_of_mem D (mem_relators_tri D t' t ha)
  simp only [map_mul, map_inv, q_wd] at hrel
  exact mul_inv_eq_one.mp hrel

/-! ### Normal forms -/

/-- The normal forms `σ(a) · t · σ(b)`. -/
def NF (D : Data H e T) : Set (P D) :=
  {p | ∃ t : T, ∃ a b : H, p = sigma D a * q D (FreeGroup.of (Sum.inr t)) * sigma D b}

theorem NF_sigma_mul (D : Data H e T) {p : P D} (hp : p ∈ NF D) (h : H) :
    sigma D h * p ∈ NF D := by
  obtain ⟨t, a, b, rfl⟩ := hp
  exact ⟨t, h * a, b, by rw [map_mul]; simp only [mul_assoc]⟩

theorem NF_gen_mul (D : Data H e T) {p : P D} (hp : p ∈ NF D) (t' : T) :
    q D (FreeGroup.of (Sum.inr t')) * p ∈ NF D := by
  obtain ⟨t, a, b, rfl⟩ := hp
  have ha := D.dec_spec t' t a
  have hL := left_move D t' (D.decC t' t a)
  have hR := right_move D t (D.decD t' t a)
  have hT := tri D t' t (D.dec0 t' t a) (D.dec_mem t' t a)
  refine ⟨D.outT t' t (D.dec0 t' t a),
    leftConj H t' (D.decC t' t a) * D.outL t' t (D.dec0 t' t a),
    D.outR t' t (D.dec0 t' t a) * conjHom H t (D.decD t' t a) * b, ?_⟩
  calc q D (FreeGroup.of (Sum.inr t')) * (sigma D a * q D (FreeGroup.of (Sum.inr t)) * sigma D b)
      = (q D (FreeGroup.of (Sum.inr t')) * sigma D (D.decC t' t a)) * sigma D (D.dec0 t' t a) *
          (sigma D (D.decD t' t a) * q D (FreeGroup.of (Sum.inr t))) * sigma D b := by
        conv_lhs => rw [ha]
        simp only [map_mul, mul_assoc]
    _ = (sigma D (leftConj H t' (D.decC t' t a)) * q D (FreeGroup.of (Sum.inr t'))) *
          sigma D (D.dec0 t' t a) *
          (q D (FreeGroup.of (Sum.inr t)) * sigma D (conjHom H t (D.decD t' t a))) * sigma D b := by
        rw [hL, hR]
    _ = sigma D (leftConj H t' (D.decC t' t a)) *
          (q D (FreeGroup.of (Sum.inr t')) * sigma D (D.dec0 t' t a) *
            q D (FreeGroup.of (Sum.inr t))) *
          sigma D (conjHom H t (D.decD t' t a)) * sigma D b := by
        simp only [mul_assoc]
    _ = sigma D (leftConj H t' (D.decC t' t a)) *
          (sigma D (D.outL t' t (D.dec0 t' t a)) *
            q D (FreeGroup.of (Sum.inr (D.outT t' t (D.dec0 t' t a)))) *
            sigma D (D.outR t' t (D.dec0 t' t a))) *
          sigma D (conjHom H t (D.decD t' t a)) * sigma D b := by
        rw [hT]
    _ = sigma D (leftConj H t' (D.decC t' t a) * D.outL t' t (D.dec0 t' t a)) *
          q D (FreeGroup.of (Sum.inr (D.outT t' t (D.dec0 t' t a)))) *
          sigma D (D.outR t' t (D.dec0 t' t a) * conjHom H t (D.decD t' t a) * b) := by
        simp only [map_mul, mul_assoc]

theorem NF_genInv_mul (D : Data H e T) {p : P D} (hp : p ∈ NF D) (t : T) :
    (q D (FreeGroup.of (Sum.inr t)))⁻¹ * p ∈ NF D := by
  rw [gen_inv, mul_assoc, mul_assoc]
  exact NF_sigma_mul D (NF_gen_mul D (NF_sigma_mul D hp _) _) _

/-- **Every element of the presented group has a normal form.** -/
theorem q_mul_mem_NF (D : Data H e T) (w : FreeGroup (Fin n ⊕ T)) :
    ∀ p ∈ NF D, q D w * p ∈ NF D := by
  induction w using FreeGroup.induction_on with
  | C1 =>
      intro p hp
      simpa using hp
  | of x =>
      intro p hp
      rcases x with i | t
      · rw [q_inl]
        exact NF_sigma_mul D hp _
      · exact NF_gen_mul D hp t
  | inv_of x _ =>
      intro p hp
      rw [map_inv]
      rcases x with i | t
      · rw [q_inl, ← map_inv]
        exact NF_sigma_mul D hp _
      · exact NF_genInv_mul D hp t
  | mul x y ihx ihy =>
      intro p hp
      rw [map_mul, mul_assoc]
      exact ihx _ (ihy p hp)

theorem one_mem_NF (D : Data H e T) (hT0 : ∃ t0 : T, (t0 : G) ∈ H) : (1 : P D) ∈ NF D := by
  obtain ⟨t0, ht0⟩ := hT0
  refine ⟨t0, (⟨t0, ht0⟩ : H)⁻¹, 1, ?_⟩
  rw [gen_of_mem D t0 ht0, map_one, mul_one, ← map_mul, inv_mul_cancel, map_one]

theorem ker_le (D : Data H e T) (hT0 : ∃ t0 : T, (t0 : G) ∈ H) : (phi H e T).ker ≤ K D := by
  intro w hw
  have hNF : q D w ∈ NF D := by simpa using q_mul_mem_NF D w 1 (one_mem_NF D hT0)
  obtain ⟨t, a, b, hwq⟩ := hNF
  have hG : (a : G) * (t : G) * (b : G) = 1 := by
    have h1 := congrArg (psi D) hwq
    rw [psi_q, MonoidHom.mem_ker.mp hw, map_mul, map_mul, psi_sigma, psi_sigma, psi_q,
      phi_of_inr] at h1
    exact h1.symm
  have ht : (t : G) ∈ H := by
    have h2 : (t : G) = (a : G)⁻¹ * (b : G)⁻¹ := by
      calc (t : G) = (a : G)⁻¹ * ((a : G) * (t : G) * (b : G)) * (b : G)⁻¹ := by group
        _ = (a : G)⁻¹ * (b : G)⁻¹ := by rw [hG]; group
    rw [h2]
    exact H.mul_mem (H.inv_mem a.2) (H.inv_mem b.2)
  have hH : a * ⟨t, ht⟩ * b = 1 := Subtype.ext (by simpa using hG)
  have hq1 : q D w = 1 := by
    rw [hwq, gen_of_mem D t ht, ← map_mul, ← map_mul, hH, map_one]
  exact (QuotientGroup.eq_one_iff w).mp hq1

theorem phi_surjective (D : Data H e T)
    (hcover : ∀ g : G, ∃ t ∈ T, ∃ a b : H, g = (a : G) * t * b) :
    Function.Surjective (phi H e T) := by
  intro g
  obtain ⟨t, htT, a, b, rfl⟩ := hcover g
  refine ⟨iota T (D.wd a) * FreeGroup.of (Sum.inr ⟨t, htT⟩) * iota T (D.wd b), ?_⟩
  rw [map_mul, map_mul, phi_iota, phi_iota, D.wd_spec, D.wd_spec, phi_of_inr]

theorem isFinitelyPresented_of_data (hs : s.Finite)
    (hcover : ∀ g : G, ∃ t ∈ T, ∃ a b : H, g = (a : G) * t * b) (D : Data H e T) :
    Group.IsFinitelyPresented G := by
  have hT0 : ∃ t0 : T, (t0 : G) ∈ H := by
    obtain ⟨t, htT, a, b, hab⟩ := hcover 1
    refine ⟨⟨t, htT⟩, ?_⟩
    have h2 : t = (a : G)⁻¹ * (b : G)⁻¹ := by
      calc t = (a : G)⁻¹ * ((a : G) * t * (b : G)) * (b : G)⁻¹ := by group
        _ = (a : G)⁻¹ * (b : G)⁻¹ := by rw [← hab]; group
    show t ∈ H
    rw [h2]
    exact H.mul_mem (H.inv_mem a.2) (H.inv_mem b.2)
  have hker : Subgroup.normalClosure (relators D) = (phi H e T).ker :=
    le_antisymm (Subgroup.normalClosure_le_normal (relators_subset_ker D)) (ker_le D hT0)
  exact Group.IsFinitelyPresented.of_surjective (phi H e T) (phi_surjective D hcover)
    ⟨relators D, relators_finite D hs, hker⟩

end Presentation

/-! ## The criterion -/

/-- **Finite presentation from finitely many double cosets** (the 2-dimensional case of
Brown's criterion, for the simplex on `G/H`).  If `H ≤ G` is finitely presented, `G` is a
finite union of double cosets `H t H` (`t ∈ T`), every `H ∩ t H t⁻¹` (`t ∈ T`) is finitely
generated, and every double coset space `(H ∩ t'⁻¹ H t') \ H / (H ∩ t H t⁻¹)` (`t', t ∈ T`)
is finite, then `G` is finitely presented. -/
theorem isFinitelyPresented_of_doubleCosets {G : Type*} [Group G] (H : Subgroup G)
    [Group.IsFinitelyPresented H] (T : Finset G)
    (hcover : ∀ g : G, ∃ t ∈ T, ∃ a b : H, g = (a : G) * t * b)
    (hedge : ∀ t ∈ T, Group.FG (edgeStab H t))
    (htri : ∀ t' ∈ T, ∀ t ∈ T, ∃ A : Finset H, ∀ a : H,
      ∃ c : edgeStab H t'⁻¹, ∃ d : edgeStab H t, ∃ a₀ ∈ A, a = (c : H) * a₀ * d) :
    Group.IsFinitelyPresented G := by
  classical
  obtain ⟨n, s, hs, ⟨e⟩⟩ := Group.IsFinitelyPresented.exists_mulEquiv_presentedGroup (G := H)
  choose wd hwd using piH_surjective H e
  choose E hEclosure hEfin using fun t : T => Group.fg_iff.mp (hedge t t.2)
  choose invT hinvT invL invR hinv using fun t : T => hcover ((t : G)⁻¹)
  choose A hA using fun t' t : T => htri t' t'.2 t t.2
  choose decC decD dec0 hdec0 hdec using hA
  choose outT houtT outL outR hout using
    fun (t' t : T) (a : H) => hcover ((t' : G) * (a : G) * (t : G))
  exact isFinitelyPresented_of_data hs hcover
    { wd := wd
      wd_spec := hwd
      E := fun t => (hEfin t).toFinset
      E_spec := fun t => by rw [Set.Finite.coe_toFinset]; exact hEclosure t
      invL := invL
      invT := fun t => ⟨invT t, hinvT t⟩
      invR := invR
      inv_spec := hinv
      A := A
      decC := decC
      decD := decD
      dec0 := dec0
      dec_mem := hdec0
      dec_spec := hdec
      outL := outL
      outT := fun t' t a => ⟨outT t' t a, houtT t' t a⟩
      outR := outR
      out_spec := hout }

#audit_axioms GroupApproximation.DoubleCosetPresentation.isFinitelyPresented_of_doubleCosets

end DoubleCosetPresentation
end GroupApproximation

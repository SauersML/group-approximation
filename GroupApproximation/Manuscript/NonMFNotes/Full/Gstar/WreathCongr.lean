import GroupApproximation.Algebra.PermutationalWreath
import GroupApproximation.Sofic.ActualCoronaMFRadical
import GroupApproximation.Meta.AxiomGuard

/-!
# Functoriality of permutational wreath products

Manuscript `non_mf_group_notes.tex`, `cor:notes-a5-relation` (tex lines 2052--2073).  The
printed group `W_{A₅} = A₅^(X) ⋊ G_*` lives over `X = G_*/Γ_*`, while the repository proves its
properties for the wreath product over the coset space of the isomorphic vertical group.  To
move the corollary across, one needs that an isomorphism of acting groups together with an
equivariant bijection of site sets induces an isomorphism of wreath products, and that the
genuine-corona MF radical is carried along isomorphisms.

Main declarations:

* `lampCongr` — a bijection of sites `X ≃ Y` induces `K^(X) ≃* K^(Y)`, with `lampCongr_single`;
* `wreathCongr` — `e : G ≃* H` and an `e`-equivariant `c : X ≃ Y` induce
  `K^(X) ⋊ G ≃* K^(Y) ⋊ H`, with `wreathCongr_inl`, `wreathCongr_inr`, `wreathCongr_right`;
* `map_actualCoronaMFResidual_mulEquiv` — `e(Rad_MF G) = Rad_MF H`;
* `mem_iff_of_map_eq` — membership transport along an isomorphism.
-/

namespace GroupApproximation.Full.NN05

section Lamps

variable (K : Type*) [Group K] {X Y : Type*}

/-- Relabelling the sites along a bijection `c : X ≃ Y`: `f ↦ f ∘ c⁻¹`. -/
def lampCongr (c : X ≃ Y) : Lamp K X ≃* Lamp K Y where
  toFun f := ⟨fun y => (f : X → K) (c.symm y), by
    show {y : Y | (f : X → K) (c.symm y) ≠ 1}.Finite
    have hset : {y : Y | (f : X → K) (c.symm y) ≠ 1}
        = (fun y : Y => c.symm y) ⁻¹' {x : X | (f : X → K) x ≠ 1} := rfl
    rw [hset]
    exact Set.Finite.preimage c.symm.injective.injOn f.2⟩
  invFun f := ⟨fun x => (f : Y → K) (c x), by
    show {x : X | (f : Y → K) (c x) ≠ 1}.Finite
    have hset : {x : X | (f : Y → K) (c x) ≠ 1}
        = (fun x : X => c x) ⁻¹' {y : Y | (f : Y → K) y ≠ 1} := rfl
    rw [hset]
    exact Set.Finite.preimage c.injective.injOn f.2⟩
  left_inv := fun f => Lamp.ext fun x => by
    show (f : X → K) (c.symm (c x)) = (f : X → K) x
    rw [Equiv.symm_apply_apply]
  right_inv := fun f => Lamp.ext fun y => by
    show (f : Y → K) (c (c.symm y)) = (f : Y → K) y
    rw [Equiv.apply_symm_apply]
  map_mul' := fun _ _ => Lamp.ext fun _ => rfl

theorem lampCongr_apply (c : X ≃ Y) (f : Lamp K X) (y : Y) :
    (lampCongr K c f).toFun y = f.toFun (c.symm y) := rfl

/-- Relabelling moves a one-site lamp to the relabelled site. -/
theorem lampCongr_single [DecidableEq X] [DecidableEq Y] (c : X ≃ Y) (x : X) (k : K) :
    lampCongr K c (Lamp.single x k) = Lamp.single (c x) k := by
  refine Lamp.ext fun y => ?_
  rw [lampCongr_apply]
  by_cases h : y = c x
  · subst h
    rw [Equiv.symm_apply_apply, Lamp.single_apply_self, Lamp.single_apply_self]
  · have h' : c.symm y ≠ x := by
      intro hcon
      exact h (by rw [← hcon, Equiv.apply_symm_apply])
    rw [Lamp.single_apply_of_ne h', Lamp.single_apply_of_ne h]

end Lamps

section Wreaths

variable (K : Type*) [Group K] {X Y : Type*} {G H : Type*} [Group G] [Group H]
  [MulAction G X] [MulAction H Y]

theorem symm_smul_of_equivariant (e : G ≃* H) (c : X ≃ Y)
    (hc : ∀ (g : G) (x : X), c (g • x) = e g • c x) (g : G) (y : Y) :
    c.symm ((e g)⁻¹ • y) = g⁻¹ • c.symm y := by
  apply c.injective
  rw [Equiv.apply_symm_apply, hc, map_inv, Equiv.apply_symm_apply]

/-- **Wreath products are functorial.**  An isomorphism `e : G ≃* H` of acting groups and an
`e`-equivariant bijection `c : X ≃ Y` of site sets induce `K^(X) ⋊ G ≃* K^(Y) ⋊ H`. -/
def wreathCongr (e : G ≃* H) (c : X ≃ Y)
    (hc : ∀ (g : G) (x : X), c (g • x) = e g • c x) : Wreath K G X ≃* Wreath K H Y :=
  SemidirectProduct.congr (lampCongr K c) e (fun g => MulEquiv.ext fun f => Lamp.ext fun y => by
    show (f : X → K) (g⁻¹ • c.symm y) = (f : X → K) (c.symm ((e g)⁻¹ • y))
    rw [symm_smul_of_equivariant e c hc g y])

variable (e : G ≃* H) (c : X ≃ Y) (hc : ∀ (g : G) (x : X), c (g • x) = e g • c x)

theorem wreathCongr_inl (f : Lamp K X) :
    wreathCongr K e c hc (SemidirectProduct.inl f) =
      SemidirectProduct.inl (lampCongr K c f) := by
  apply SemidirectProduct.ext
  · rfl
  · exact map_one e

theorem wreathCongr_inr (g : G) :
    wreathCongr K e c hc (SemidirectProduct.inr g) = SemidirectProduct.inr (e g) := by
  apply SemidirectProduct.ext
  · exact map_one (lampCongr K c)
  · rfl

theorem wreathCongr_right (w : Wreath K G X) :
    (wreathCongr K e c hc w).right = e w.right := rfl

end Wreaths

section Transport

variable {G H : Type*} [Group G] [Group H]

/-- Membership transport along an isomorphism carrying `S` onto `T`. -/
theorem mem_iff_of_map_eq (e : G ≃* H) {S : Subgroup G} {T : Subgroup H}
    (h : S.map e.toMonoidHom = T) (x : G) : x ∈ S ↔ e x ∈ T := by
  rw [← h, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

/-- The genuine-corona MF radical is carried onto itself by isomorphisms. -/
theorem map_actualCoronaMFResidual_mulEquiv (e : G ≃* H) :
    (actualCoronaMFResidual G).map e.toMonoidHom = actualCoronaMFResidual H := by
  refine le_antisymm (map_actualCoronaMFResidual_le e.toMonoidHom) fun y hy => ?_
  exact Subgroup.mem_map.mpr ⟨e.symm y,
    map_actualCoronaMFResidual_le e.symm.toMonoidHom (Subgroup.mem_map_of_mem _ hy),
    e.apply_symm_apply y⟩

end Transport

#audit_axioms lampCongr_single
#audit_axioms wreathCongr
#audit_axioms wreathCongr_inl
#audit_axioms wreathCongr_inr
#audit_axioms mem_iff_of_map_eq
#audit_axioms map_actualCoronaMFResidual_mulEquiv

end GroupApproximation.Full.NN05

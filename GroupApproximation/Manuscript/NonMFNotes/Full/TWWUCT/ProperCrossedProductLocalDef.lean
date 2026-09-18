import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.CrossedProductDef
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.ProperCrossedProductIdealAction

/-!
# The local algebras `B_L` of a slice and their finite-group actions

Lane TWWUCT-E5 (WO-TWWUCT-E-5), manuscript label `thm:fixed-radical-membership` (UCT input,
`non_mf_group_notes.tex` L1370--1378).  In the Higson--Kasparov/Tu proof that `A(H) ⋊_r G` lies in
the bootstrap class (Tu, K-Theory 17 (1999), §10; Higson--Kasparov, Invent. Math. 144 (2001), §9),
the exhaustion is broken into local pieces.  Fix a slice `U` at a point `z` with finite stabiliser
`F = stab z`, and a locally closed `F`-invariant set `L ⊆ U`.  The local piece is the restriction
`B_L` of the ideal `I_U` to `L`.  When `L` is relatively closed in `U`, `B_L` is the quotient
`I_U / I_{U \ L}`, and `F` acts on it.  This file builds these objects without quotients of
non-unital algebras: `B_L` is the closure, in `L →ᵇ C`, of the image of `I_U` under restriction.

* `AffineIsometricAction.restrictHKT C L`: restriction `A(H) → (L →ᵇ C)`, a ⋆-homomorphism.
* `restrictHKT_eq_zero_iff`: on `I_U` its kernel is `I_{U \ L}`.
* `AffineIsometricAction.LocalDatum b`: a subgroup `F` and `F`-invariant sets `U`, `L`.
  `LocalDatum.ofSlice` gives one from a slice, with `F = stab z` finite (`finite_ofSlice`).
* `LocalDatum.localSubalgebra C D`: the closed ⋆-subalgebra `B_L`, carried by
  `LocalAlgebraOf C D`, a `NonUnitalCStarAlgebra`.  It is separable when `A(H)` is.
* `LocalDatum.localAction C D : D.F →* (B_L ≃⋆ₐ[ℂ] B_L)`, with
  `(k · φ)(x) = orth(π_k) (φ (k⁻¹ · x))`, and the instance `GCStarAlgebra D.F (LocalAlgebraOf C D)`.
  Restriction intertwines it with the HKT action (`restrictHKT_hktAction`).
-/

namespace GroupApproximation.Full.TWWUCT

noncomputable section

universe u v w

namespace AffineIsometricAction

variable {G : Type u} [Group G] {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {C : Type w} [CStarAlgebra C] [CliffordSystem H C]

variable (C) in
/-- **Restriction to `L`**, `A(H) → (L →ᵇ C)`, `f ↦ f|_L`.  On `I_U` its kernel is `I_{U \ L}`, so
it presents the local piece `B_L = I_U / I_{U \ L}` of `thm:fixed-radical-membership`
(UCT input; Tu 1999, §10). -/
def restrictHKT (L : Set (ℝ × H)) : HKTAlgebraOf H C →⋆ₙₐ[ℂ] (L →ᵇ C) where
  toFun f := (f : ℝ × H →ᵇ C).compContinuous ⟨Subtype.val, continuous_subtype_val⟩
  map_smul' _ _ := BoundedContinuousFunction.ext fun _ => rfl
  map_zero' := BoundedContinuousFunction.ext fun _ => rfl
  map_add' _ _ := BoundedContinuousFunction.ext fun _ => rfl
  map_mul' _ _ := BoundedContinuousFunction.ext fun _ => rfl
  map_star' _ := BoundedContinuousFunction.ext fun _ => rfl

theorem restrictHKT_apply (L : Set (ℝ × H)) (f : HKTAlgebraOf H C) (x : L) :
    restrictHKT C L f x = (f : ℝ × H →ᵇ C) x :=
  rfl

variable (C) in
/-- Restriction to `L` is continuous (`thm:fixed-radical-membership`, UCT input). -/
theorem continuous_restrictHKT (L : Set (ℝ × H)) : Continuous (restrictHKT C L) := by
  show Continuous fun f : HKTAlgebraOf H C =>
    (f : ℝ × H →ᵇ C).compContinuous ⟨Subtype.val, continuous_subtype_val⟩
  exact Continuous.comp
    (g := fun F : ℝ × H →ᵇ C => F.compContinuous ⟨Subtype.val, continuous_subtype_val⟩)
    (BoundedContinuousFunction.continuous_compContinuous _) continuous_subtype_val

/-- **The kernel of restriction on `I_U`**: for `f ∈ I_U`, `f|_L = 0` iff `f ∈ I_{U \ L}`.  Thus
the local piece `B_L` is `I_U / I_{U \ L}` (`thm:fixed-radical-membership`, UCT input;
Tu 1999, §10). -/
theorem restrictHKT_eq_zero_iff {U L : Set (ℝ × H)} {f : HKTAlgebraOf H C}
    (hf : f ∈ hktIdeal C U) : restrictHKT C L f = 0 ↔ f ∈ hktIdeal C (U \ L) := by
  have hf' : VanishesOff U f := mem_hktIdeal.1 hf
  constructor
  · intro h
    refine mem_hktIdeal.2 fun x hx => ?_
    by_cases hxL : x ∈ L
    · have hx' := congrArg (fun φ : L →ᵇ C => φ ⟨x, hxL⟩) h
      exact hx'
    · exact hf' x fun hxU => hx ⟨hxU, hxL⟩
  · intro h
    have h' : VanishesOff (U \ L) f := mem_hktIdeal.1 h
    ext ⟨x, hxL⟩
    exact h' x fun hx => hx.2 hxL

variable (b : AffineIsometricAction G H)

/-- **Local data** for `thm:fixed-radical-membership` (UCT input; Tu 1999, §10): a subgroup `F`
of `G` and two subsets `U`, `L` of `ℝ × H`, both invariant under `F` for the action
`(t, h) ↦ (t, g • h)`.  The intended case is `LocalDatum.ofSlice`. -/
structure LocalDatum where
  /-- The finite group, typically the stabiliser `stab z` of a point. -/
  F : Subgroup G
  /-- The open set, typically a slice at `z`. -/
  U : Set (ℝ × H)
  /-- The locally closed piece. -/
  L : Set (ℝ × H)
  act_mem_U : ∀ k ∈ F, ∀ x ∈ U, b.lineAction.act k x ∈ U
  act_mem_L : ∀ k ∈ F, ∀ x ∈ L, b.lineAction.act k x ∈ L

variable {b}

/-- The local datum of a slice `U` at `z` and an `F`-invariant `L`, with `F = stab z`
(`thm:fixed-radical-membership`, UCT input; Tu 1999, §10). -/
def LocalDatum.ofSlice {z : ℝ × H} {U : Set (ℝ × H)} (hU : b.lineAction.IsSliceAt z U)
    (L : Set (ℝ × H)) (hL : ∀ k ∈ b.lineAction.stab z, ∀ x ∈ L, b.lineAction.act k x ∈ L) :
    LocalDatum b where
  F := b.lineAction.stab z
  U := U
  L := L
  act_mem_U := hU.2.2.1
  act_mem_L := hL

/-- For a metrically proper action the group `F = stab z` of `LocalDatum.ofSlice` is finite
(`thm:fixed-radical-membership`, UCT input). -/
theorem LocalDatum.finite_ofSlice (hb : b.IsMetricallyProper) {z : ℝ × H} {U : Set (ℝ × H)}
    (hU : b.lineAction.IsSliceAt z U) (L : Set (ℝ × H))
    (hL : ∀ k ∈ b.lineAction.stab z, ∀ x ∈ L, b.lineAction.act k x ∈ L) :
    Finite (LocalDatum.ofSlice hU L hL).F :=
  (DiscreteAction.finite_stab (isProper_lineAction hb) z).to_subtype

namespace LocalDatum

variable (D : LocalDatum b)

/-- `α_k` preserves `I_U` for `k ∈ F` (`thm:fixed-radical-membership`, UCT input). -/
theorem hktAction_mem_hktIdeal_U (k : D.F) {f : HKTAlgebraOf H C} (hf : f ∈ hktIdeal C D.U) :
    b.hktAction C (k : G) f ∈ hktIdeal C D.U := by
  have hf' : VanishesOff D.U f := mem_hktIdeal.1 hf
  refine mem_hktIdeal.2 fun x hx => ?_
  have hnot : b.lineAction.act (k : G)⁻¹ x ∉ D.U := fun h => hx (by
    have h' := D.act_mem_U (k : G) k.2 _ h
    rwa [b.lineAction.act_act_inv] at h')
  show CliffordSystem.orth (C := C) (b.linearPart (k : G))
    ((f : ℝ × H →ᵇ C) (b.lineAction.act (k : G)⁻¹ x)) = 0
  rw [hf' _ hnot, map_zero]

/-- The point `k⁻¹ · x` of `L` (`thm:fixed-radical-membership`, UCT input). -/
def invPoint (k : D.F) (x : D.L) : D.L :=
  ⟨b.lineAction.act (k : G)⁻¹ x, D.act_mem_L _ (inv_mem k.2) _ x.2⟩

theorem coe_invPoint (k : D.F) (x : D.L) :
    (D.invPoint k x : ℝ × H) = b.lineAction.act (k : G)⁻¹ x :=
  rfl

theorem continuous_invPoint (k : D.F) : Continuous (D.invPoint k) :=
  ((b.lineAction.continuous_act _).comp continuous_subtype_val).subtype_mk _

theorem invPoint_mul (k k' : D.F) (x : D.L) :
    D.invPoint (k * k') x = D.invPoint k' (D.invPoint k x) := by
  apply Subtype.ext
  show b.lineAction.act ((k : G) * k')⁻¹ x =
    b.lineAction.act (k' : G)⁻¹ (b.lineAction.act (k : G)⁻¹ x)
  rw [mul_inv_rev, b.lineAction.act_mul]

theorem invPoint_one (x : D.L) : D.invPoint 1 x = x := by
  apply Subtype.ext
  show b.lineAction.act ((1 : D.F) : G)⁻¹ x = x
  rw [Subgroup.coe_one, inv_one, b.lineAction.act_one]

/-- The action on `L →ᵇ C`: `(k · φ)(x) = orth(π_k) (φ (k⁻¹ · x))`
(`thm:fixed-radical-membership`, UCT input; HK 2001, §9). -/
def localMap (k : D.F) (φ : D.L →ᵇ C) : D.L →ᵇ C :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x : D.L => CliffordSystem.orth (C := C) (b.linearPart (k : G)) (φ (D.invPoint k x)))
    ((StarAlgEquiv.isometry (CliffordSystem.orth (C := C) (b.linearPart (k : G)))).continuous.comp
      (φ.continuous.comp (D.continuous_invPoint k))) ‖φ‖
    (fun x => by
      show ‖CliffordSystem.orth (C := C) (b.linearPart (k : G)) (φ (D.invPoint k x))‖ ≤ ‖φ‖
      rw [StarAlgEquiv.norm_map]
      exact φ.norm_coe_le_norm _)

theorem localMap_apply (k : D.F) (φ : D.L →ᵇ C) (x : D.L) :
    D.localMap k φ x = CliffordSystem.orth (C := C) (b.linearPart (k : G)) (φ (D.invPoint k x)) :=
  rfl

theorem localMap_mul (k k' : D.F) (φ : D.L →ᵇ C) :
    D.localMap (k * k') φ = D.localMap k (D.localMap k' φ) := by
  ext x
  rw [localMap_apply, localMap_apply, localMap_apply, D.invPoint_mul, Subgroup.coe_mul,
    b.linearPart_mul_eq, CliffordSystem.orth_mul]

theorem localMap_one (φ : D.L →ᵇ C) : D.localMap 1 φ = φ := by
  ext x
  rw [localMap_apply, D.invPoint_one, Subgroup.coe_one, b.linearPart_one_eq,
    CliffordSystem.orth_one]

/-- **Restriction is equivariant**: `(α_k f)|_L = k · (f|_L)` for `k ∈ F`
(`thm:fixed-radical-membership`, UCT input). -/
theorem restrictHKT_hktAction (k : D.F) (f : HKTAlgebraOf H C) :
    restrictHKT C D.L (b.hktAction C (k : G) f) = D.localMap k (restrictHKT C D.L f) := by
  ext x
  rfl

variable (C) in
/-- The action of `k ∈ F` on `L →ᵇ C` as a ⋆-automorphism (`thm:fixed-radical-membership`,
UCT input). -/
def localAct (k : D.F) : (D.L →ᵇ C) ≃⋆ₐ[ℂ] (D.L →ᵇ C) where
  toFun := D.localMap k
  invFun := D.localMap k⁻¹
  left_inv φ := by
    show D.localMap k⁻¹ (D.localMap k φ) = φ
    rw [← D.localMap_mul, inv_mul_cancel, D.localMap_one]
  right_inv φ := by
    show D.localMap k (D.localMap k⁻¹ φ) = φ
    rw [← D.localMap_mul, mul_inv_cancel, D.localMap_one]
  map_mul' φ ψ := by
    ext x
    exact map_mul (CliffordSystem.orth (C := C) (b.linearPart (k : G))) (φ (D.invPoint k x))
      (ψ (D.invPoint k x))
  map_add' φ ψ := by
    ext x
    exact map_add (CliffordSystem.orth (C := C) (b.linearPart (k : G))) (φ (D.invPoint k x))
      (ψ (D.invPoint k x))
  map_star' φ := by
    ext x
    exact map_star (CliffordSystem.orth (C := C) (b.linearPart (k : G))) (φ (D.invPoint k x))
  map_smul' c φ := by
    ext x
    exact map_smul (CliffordSystem.orth (C := C) (b.linearPart (k : G))) c (φ (D.invPoint k x))

theorem localAct_apply (k : D.F) (φ : D.L →ᵇ C) : D.localAct C k φ = D.localMap k φ :=
  rfl

variable (C) in
/-- **The local algebra** `B_L`: the closure in `L →ᵇ C` of the restrictions to `L` of the
elements of `I_U`.  By `restrictHKT_eq_zero_iff` it is `I_U / I_{U \ L}` when `L` is relatively
closed in `U` (`thm:fixed-radical-membership`, UCT input; Tu 1999, §10). -/
def localSubalgebra : NonUnitalStarSubalgebra ℂ (D.L →ᵇ C) :=
  ((hktIdeal C D.U).map (restrictHKT C D.L)).topologicalClosure

theorem restrictHKT_mem_localSubalgebra {f : HKTAlgebraOf H C} (hf : f ∈ hktIdeal C D.U) :
    restrictHKT C D.L f ∈ D.localSubalgebra C :=
  NonUnitalStarSubalgebra.le_topologicalClosure _
    (NonUnitalStarSubalgebra.mem_map.2 ⟨f, hf, rfl⟩)

instance isClosed_localSubalgebra : IsClosed (D.localSubalgebra C : Set (D.L →ᵇ C)) :=
  NonUnitalStarSubalgebra.isClosed_topologicalClosure _

variable (C) in
/-- The carrier of `B_L` (`thm:fixed-radical-membership`, UCT input). -/
abbrev LocalAlgebraOf :=
  ↥(D.localSubalgebra C)

/-- `B_L` is a non-unital C⋆-algebra (`thm:fixed-radical-membership`, UCT input). -/
noncomputable instance instNonUnitalCStarAlgebraLocalAlgebraOf :
    NonUnitalCStarAlgebra (D.LocalAlgebraOf C) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra (D.localSubalgebra C)
    (h_closed := NonUnitalStarSubalgebra.isClosed_topologicalClosure _)

/-- `B_L` is separable when `A(H)` is: it is the closure of a continuous image of a subset of
`A(H)` (`thm:fixed-radical-membership`, UCT input). -/
instance instSeparableSpaceLocalAlgebraOf [TopologicalSpace.SeparableSpace (HKTAlgebraOf H C)] :
    TopologicalSpace.SeparableSpace (D.LocalAlgebraOf C) := by
  have h1 : TopologicalSpace.IsSeparable (hktIdeal C D.U : Set (HKTAlgebraOf H C)) :=
    TopologicalSpace.IsSeparable.of_separableSpace _
  have h2 : TopologicalSpace.IsSeparable
      (((hktIdeal C D.U).map (restrictHKT C D.L) : NonUnitalStarSubalgebra ℂ (D.L →ᵇ C)) :
        Set (D.L →ᵇ C)) := by
    rw [NonUnitalStarSubalgebra.coe_map]
    exact h1.image (continuous_restrictHKT C D.L)
  have h3 : TopologicalSpace.IsSeparable (D.localSubalgebra C : Set (D.L →ᵇ C)) :=
    h2.closure
  exact h3.separableSpace

/-- `k ∈ F` maps `B_L` into itself (`thm:fixed-radical-membership`, UCT input). -/
theorem localSubalgebra_le_comap (k : D.F) :
    D.localSubalgebra C ≤ (D.localSubalgebra C).comap (D.localAct C k) := by
  refine NonUnitalStarSubalgebra.topologicalClosure_minimal _ ?_ ?_
  · intro φ hφ
    obtain ⟨f, hf, rfl⟩ := NonUnitalStarSubalgebra.mem_map.1 hφ
    rw [NonUnitalStarSubalgebra.mem_comap, localAct_apply, ← D.restrictHKT_hktAction]
    exact D.restrictHKT_mem_localSubalgebra (D.hktAction_mem_hktIdeal_U k hf)
  · exact IsClosed.preimage (StarAlgEquiv.isometry (D.localAct C k)).continuous
      (NonUnitalStarSubalgebra.isClosed_topologicalClosure _)

theorem localMap_mem (k : D.F) {φ : D.L →ᵇ C} (hφ : φ ∈ D.localSubalgebra C) :
    D.localMap k φ ∈ D.localSubalgebra C := by
  have h := (NonUnitalStarSubalgebra.mem_comap _ _ _).1 (D.localSubalgebra_le_comap k hφ)
  rwa [localAct_apply] at h

variable (C) in
/-- The automorphism of `B_L` given by `k ∈ F` (`thm:fixed-radical-membership`, UCT input). -/
def localActionEquiv (k : D.F) : D.LocalAlgebraOf C ≃⋆ₐ[ℂ] D.LocalAlgebraOf C where
  toFun φ := ⟨D.localMap k φ, D.localMap_mem k φ.2⟩
  invFun φ := ⟨D.localMap k⁻¹ φ, D.localMap_mem k⁻¹ φ.2⟩
  left_inv φ := Subtype.ext (by
    show D.localMap k⁻¹ (D.localMap k (φ : D.L →ᵇ C)) = φ
    rw [← D.localMap_mul, inv_mul_cancel, D.localMap_one])
  right_inv φ := Subtype.ext (by
    show D.localMap k (D.localMap k⁻¹ (φ : D.L →ᵇ C)) = φ
    rw [← D.localMap_mul, mul_inv_cancel, D.localMap_one])
  map_mul' φ ψ := Subtype.ext (map_mul (D.localAct C k) (φ : D.L →ᵇ C) ψ)
  map_add' φ ψ := Subtype.ext (map_add (D.localAct C k) (φ : D.L →ᵇ C) ψ)
  map_star' φ := Subtype.ext (map_star (D.localAct C k) (φ : D.L →ᵇ C))
  map_smul' c φ := Subtype.ext (map_smul (D.localAct C k) c (φ : D.L →ᵇ C))

theorem coe_localActionEquiv (k : D.F) (φ : D.LocalAlgebraOf C) :
    ((D.localActionEquiv C k φ : D.LocalAlgebraOf C) : D.L →ᵇ C) = D.localMap k φ :=
  rfl

variable (C) in
/-- **The action of `F` on the local algebra** `B_L`, `(k · φ)(x) = orth(π_k) (φ (k⁻¹ · x))`
(`thm:fixed-radical-membership`, UCT input; Tu 1999, §10; HK 2001, §9). -/
def localAction : D.F →* (D.LocalAlgebraOf C ≃⋆ₐ[ℂ] D.LocalAlgebraOf C) where
  toFun := D.localActionEquiv C
  map_one' := StarAlgEquiv.ext fun φ => Subtype.ext (D.localMap_one (φ : D.L →ᵇ C))
  map_mul' k k' := StarAlgEquiv.ext fun φ =>
    Subtype.ext (D.localMap_mul k k' (φ : D.L →ᵇ C))

/-- `B_L` is an `F`-C⋆-algebra, so `B_L ⋊_r F` is defined (`thm:fixed-radical-membership`,
UCT input). -/
instance instGCStarAlgebraLocalAlgebraOf : GCStarAlgebra D.F (D.LocalAlgebraOf C) :=
  ⟨D.localAction C⟩

theorem coe_act_localAlgebra (k : D.F) (φ : D.LocalAlgebraOf C) :
    ((GCStarAlgebra.act (A := D.LocalAlgebraOf C) k φ : D.LocalAlgebraOf C) : D.L →ᵇ C) =
      D.localMap k φ :=
  rfl

end LocalDatum

end AffineIsometricAction

end

end GroupApproximation.Full.TWWUCT

import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionExtInverseCorners

/-!
# Assembling a dilation on `H_J ⊕ H_J`

Lane `TWWSch-Inv2`, work order `WO-Inv-2` (towards `exists_dilation_of_isCPCOp`), part of the
Ext-inverse step of `thm:fixed-radical-membership`.

Kasparov's Stinespring theorem (J. Operator Theory 4 (1980), Thm 3 and §7; Lance, *Hilbert
C⋆-modules*, Ch. 5–6) produces, for a completely positive contraction `ψ : S → 𝓛(H_J)`, a
Hilbert `J`-module `E`, a representation `π` of `S` on `E` and an isometry `V : H_J → E` with
`V⋆ π(a) V = ψ(a)`. Kasparov stabilization then absorbs the complement `C = ker V⋆` into
`H_J`: `H_J ⊕ C ≅ H_J`. This file is the purely algebraic last step: from such data it builds
a unitary `W : H_J ⊕ H_J ≅ E ⊕ H_J` with `W (ξ, 0) = (V ξ, 0)` and the representation
`ρ(a) = W⋆ (π(a) ⊕ 0) W` of `S` on `H_J ⊕ H_J`, whose `(1,1)` corner is `ψ`.

* `kerAdjSubmodule`, `kerAdj`: the complement `ker V⋆` as a Hilbert module;
* `kerProj`: `e ↦ e - V V⋆ e`, landing in `ker V⋆` when `V⋆V = 1`;
* `joinKer`, `isUnitaryAdj_joinKer`: `F ⊕ ker V⋆ ≅ E`, `(ξ, c) ↦ Vξ + c`;
* `dilationUnitary`, `isUnitaryAdj_dilationUnitary`: `F ⊕ G ≅ E ⊕ G` from `U : G ⊕ ker V⋆ ≅ G`;
* `isRepresentation_prodMap_zero`, `isRepresentation_unitaryConj`;
* **`exists_dilation_of_stinespring`**.
-/

noncomputable section

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule

universe u₁ u₂ u₃

section DilationAssembly

variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]
variable {F : CStarModule.{0, u₁} J} {E : CStarModule.{0, u₂} J} {G : CStarModule.{0, u₃} J}

/-- The adjoint map of an adjointable operator is additive. -/
theorem adj_map_add (V : Adjointable F E) (x y : E.carrier) :
    V.adj (x + y) = V.adj x + V.adj y :=
  (Adjointable.adjoint V).map_add x y

/-- The adjoint map of an adjointable operator respects differences. -/
theorem adj_map_sub (V : Adjointable F E) (x y : E.carrier) :
    V.adj (x - y) = V.adj x - V.adj y :=
  (Adjointable.adjoint V).map_sub x y

/-- The adjoint map of an adjointable operator kills `0`. -/
theorem adj_map_zero (V : Adjointable F E) : V.adj 0 = 0 :=
  (Adjointable.adjoint V).map_zero

/-- **The complement of the range of `V`**: `ker V⋆` as a `ℂ`-submodule of `E`. -/
def kerAdjSubmodule (V : Adjointable F E) : Submodule ℂ E.carrier where
  carrier := {x | V.adj x = 0}
  add_mem' {x y} hx hy := by
    have hx' : V.adj x = 0 := hx
    have hy' : V.adj y = 0 := hy
    show V.adj (x + y) = 0
    rw [adj_map_add, hx', hy', add_zero]
  zero_mem' := adj_map_zero V
  smul_mem' c x hx := by
    have hx' : V.adj x = 0 := hx
    show V.adj (c • x) = 0
    have h : V.adj (c • x) = c • V.adj x := (Adjointable.adjoint V).map_smul c x
    rw [h, hx', smul_zero]

/-- **`ker V⋆` as a Hilbert `J`-module**, with the inner product and action of `E`. It is closed
under the action because `V⋆` is `J`-linear. -/
def kerAdj (V : Adjointable F E) : CStarModule.{0, u₂} J where
  carrier := ↥(kerAdjSubmodule V)
  act x b := ⟨E.act x.1 b, by
    have hx : V.adj x.1 = 0 := x.2
    show V.adj (E.act x.1 b) = 0
    have h : V.adj (E.act x.1 b) = F.act (V.adj x.1) b := (Adjointable.adjoint V).map_act x.1 b
    rw [h, hx, CStarModule.act_zero_left]⟩
  inner x y := E.inner x.1 y.1
  act_add_left x y b := Subtype.ext (E.act_add_left x.1 y.1 b)
  act_add_right x b c := Subtype.ext (E.act_add_right x.1 b c)
  act_assoc x b c := Subtype.ext (E.act_assoc x.1 b c)
  act_smul c x b := Subtype.ext (E.act_smul c x.1 b)
  inner_add_right x y z := E.inner_add_right x.1 y.1 z.1
  inner_smul_right c x y := E.inner_smul_right c x.1 y.1
  inner_act_right x y b := E.inner_act_right x.1 y.1 b
  inner_star x y := E.inner_star x.1 y.1
  inner_self_isPositive x := E.inner_self_isPositive x.1
  inner_self_eq_zero x hx := Subtype.ext (E.inner_self_eq_zero x.1 hx)

theorem kerAdj_inner (V : Adjointable F E) (x y : (kerAdj V).carrier) :
    (kerAdj V).inner x y = E.inner x.1 y.1 := rfl

/-- A vector of `ker V⋆` is killed by `V⋆`. -/
theorem adj_kerAdj (V : Adjointable F E) (x : (kerAdj V).carrier) : V.adj x.1 = 0 := x.2

/-- **The projection onto `ker V⋆`**: `e ↦ e - V V⋆ e`, for an isometry `V`. -/
def kerProj (V : Adjointable F E) (hV : ∀ ξ, V.adj (V.toFun ξ) = ξ) (e : E.carrier) :
    (kerAdj V).carrier :=
  ⟨e - V.toFun (V.adj e), by
    show V.adj (e - V.toFun (V.adj e)) = 0
    rw [adj_map_sub, hV, sub_self]⟩

/-- **`F ⊕ ker V⋆ ≅ E`** for an isometry `V : F → E`: `(ξ, c) ↦ V ξ + c`, with adjoint
`e ↦ (V⋆ e, e - V V⋆ e)`. -/
def joinKer (V : Adjointable F E) (hV : ∀ ξ, V.adj (V.toFun ξ) = ξ) :
    Adjointable (prod F (kerAdj V)) E where
  toFun p := V.toFun p.1 + p.2.1
  adj e := (V.adj e, kerProj V hV e)
  inner_adj p e := by
    show E.inner (V.toFun p.1 + p.2.1) e
      = F.inner p.1 (V.adj e) + E.inner p.2.1 (e - V.toFun (V.adj e))
    rw [E.inner_add_left, V.inner_adj, E.inner_sub_right, V.inner_adj' (V.adj e) p.2.1,
      adj_kerAdj V p.2, F.inner_zero_left, sub_zero]

theorem joinKer_toFun (V : Adjointable F E) (hV : ∀ ξ, V.adj (V.toFun ξ) = ξ)
    (p : (prod F (kerAdj V)).carrier) : (joinKer V hV).toFun p = V.toFun p.1 + p.2.1 := rfl

theorem isUnitaryAdj_joinKer (V : Adjointable F E) (hV : ∀ ξ, V.adj (V.toFun ξ) = ξ) :
    (joinKer V hV).IsUnitaryAdj where
  adj_toFun p := by
    have h1 : V.adj (V.toFun p.1 + p.2.1) = p.1 := by
      rw [adj_map_add, hV, adj_kerAdj V p.2, add_zero]
    refine Prod.ext h1 (Subtype.ext ?_)
    show V.toFun p.1 + p.2.1 - V.toFun (V.adj (V.toFun p.1 + p.2.1)) = p.2.1
    rw [h1]
    abel
  toFun_adj e := by
    show V.toFun (V.adj e) + (e - V.toFun (V.adj e)) = e
    abel

/-- **The dilation unitary** `W : F ⊕ G ≅ E ⊕ G` built from an isometry `V : F → E` and a
unitary `U : G ⊕ ker V⋆ ≅ G`: `W (ξ, η) = (V ξ + (U⋆η)₂, (U⋆η)₁)`. -/
def dilationUnitary (V : Adjointable F E) (hV : ∀ ξ, V.adj (V.toFun ξ) = ξ)
    (U : Adjointable (prod G (kerAdj V)) G) : Adjointable (prod F G) (prod E G) where
  toFun p := ((joinKer V hV).toFun (p.1, (U.adj p.2).2), (U.adj p.2).1)
  adj q := (((joinKer V hV).adj q.1).1, U.toFun (q.2, ((joinKer V hV).adj q.1).2))
  inner_adj p q := by
    show E.inner ((joinKer V hV).toFun (p.1, (U.adj p.2).2)) q.1 + G.inner (U.adj p.2).1 q.2
      = F.inner p.1 ((joinKer V hV).adj q.1).1
        + G.inner p.2 (U.toFun (q.2, ((joinKer V hV).adj q.1).2))
    rw [(joinKer V hV).inner_adj, U.inner_adj']
    show F.inner p.1 ((joinKer V hV).adj q.1).1
        + (kerAdj V).inner (U.adj p.2).2 ((joinKer V hV).adj q.1).2
        + G.inner (U.adj p.2).1 q.2
      = F.inner p.1 ((joinKer V hV).adj q.1).1
        + (G.inner (U.adj p.2).1 q.2
          + (kerAdj V).inner (U.adj p.2).2 ((joinKer V hV).adj q.1).2)
    abel

theorem isUnitaryAdj_dilationUnitary (V : Adjointable F E) (hV : ∀ ξ, V.adj (V.toFun ξ) = ξ)
    {U : Adjointable (prod G (kerAdj V)) G} (hU : U.IsUnitaryAdj) :
    (dilationUnitary V hV U).IsUnitaryAdj where
  adj_toFun p := by
    have hJ := (isUnitaryAdj_joinKer V hV).adj_toFun (p.1, (U.adj p.2).2)
    show (((joinKer V hV).adj ((joinKer V hV).toFun (p.1, (U.adj p.2).2))).1,
        U.toFun ((U.adj p.2).1,
          ((joinKer V hV).adj ((joinKer V hV).toFun (p.1, (U.adj p.2).2))).2)) = p
    rw [hJ]
    exact Prod.ext rfl (hU.toFun_adj p.2)
  toFun_adj q := by
    show ((joinKer V hV).toFun (((joinKer V hV).adj q.1).1,
          (U.adj (U.toFun (q.2, ((joinKer V hV).adj q.1).2))).2),
        (U.adj (U.toFun (q.2, ((joinKer V hV).adj q.1).2))).1) = q
    rw [hU.adj_toFun]
    exact Prod.ext ((isUnitaryAdj_joinKer V hV).toFun_adj q.1) rfl

/-- `W (ξ, 0) = (V ξ, 0)`: the dilation unitary extends `V` on the first summand. -/
theorem dilationUnitary_toFun_inl (V : Adjointable F E) (hV : ∀ ξ, V.adj (V.toFun ξ) = ξ)
    (U : Adjointable (prod G (kerAdj V)) G) (ξ : F.carrier) :
    (dilationUnitary V hV U).toFun (ξ, 0) = (V.toFun ξ, 0) := by
  show (V.toFun ξ + (U.adj 0).2.1, (U.adj 0).1) = (V.toFun ξ, 0)
  rw [adj_map_zero U]
  show (V.toFun ξ + 0, 0) = (V.toFun ξ, 0)
  rw [add_zero]

/-- The zero operator is bounded. -/
theorem isBounded_zeroOp : (Adjointable.zero F E).IsBounded := by
  refine ⟨0, le_rfl, fun x => ?_⟩
  show E.norm (0 : E.carrier) ≤ 0 * F.norm x
  rw [E.norm_zero_vector, zero_mul]

variable {S : Type} [NonUnitalCStarAlgebra S]

/-- **`π ⊕ 0` is a representation** on `E ⊕ G`. -/
theorem isRepresentation_prodMap_zero {π : S → Adjointable E E} (hπ : IsRepresentation E π) :
    IsRepresentation (prod E G) (fun a => Adjointable.prodMap (π a) (Adjointable.zero G G)) where
  bounded a := (hπ.bounded a).prodMap isBounded_zeroOp
  map_add a a' p := by
    show ((π (a + a')).toFun p.1, (0 : G.carrier))
      = ((π a).toFun p.1 + (π a').toFun p.1, 0 + 0)
    rw [hπ.map_add, add_zero]
  map_smul c a p := by
    show ((π (c • a)).toFun p.1, (0 : G.carrier)) = (c • (π a).toFun p.1, c • 0)
    rw [hπ.map_smul, smul_zero]
  map_mul a a' p := by
    show ((π (a * a')).toFun p.1, (0 : G.carrier)) = ((π a).toFun ((π a').toFun p.1), 0)
    rw [hπ.map_mul]
  map_star a p := by
    show ((π (star a)).toFun p.1, (0 : G.carrier)) = ((π a).adj p.1, 0)
    rw [hπ.map_star]

/-- **Conjugating a representation by a unitary** `W : F ≅ E` gives a representation on `F`:
`a ↦ W⋆ π(a) W`. -/
theorem isRepresentation_unitaryConj {π : S → Adjointable E E} (hπ : IsRepresentation E π)
    {W : Adjointable F E} (hW : W.IsUnitaryAdj) :
    IsRepresentation F
      (fun a => Adjointable.comp (Adjointable.adjoint W) (Adjointable.comp (π a) W)) where
  bounded a := isBounded_comp hW.isBounded.adjoint (isBounded_comp (hπ.bounded a) hW.isBounded)
  map_add a a' x := by
    show W.adj ((π (a + a')).toFun (W.toFun x))
      = W.adj ((π a).toFun (W.toFun x)) + W.adj ((π a').toFun (W.toFun x))
    rw [hπ.map_add, adj_map_add]
  map_smul c a x := by
    show W.adj ((π (c • a)).toFun (W.toFun x)) = c • W.adj ((π a).toFun (W.toFun x))
    rw [hπ.map_smul]
    exact (Adjointable.adjoint W).map_smul c _
  map_mul a a' x := by
    show W.adj ((π (a * a')).toFun (W.toFun x))
      = W.adj ((π a).toFun (W.toFun (W.adj ((π a').toFun (W.toFun x)))))
    rw [hπ.map_mul, hW.toFun_adj]
  map_star a x := by
    show W.adj ((π (star a)).toFun (W.toFun x)) = W.adj ((π a).adj (W.toFun x))
    rw [hπ.map_star]

/-- **The Kasparov dilation, assembled** (Kasparov, J. Operator Theory 4 (1980), Thm 3 and §7;
Lance, *Hilbert C⋆-modules*, Ch. 5–6), for `thm:fixed-radical-membership`. A representation `π`
of `S` on `E`, an isometry `V : H_J → E` compressing `π` to `ψ`, and a unitary
`U : H_J ⊕ ker V⋆ ≅ H_J` (Kasparov stabilization of the complement) give a representation `ρ`
of `S` on `H_J ⊕ H_J` whose `(1,1)` corner is exactly `ψ`. -/
theorem exists_dilation_of_stinespring {ψ : S → StdOp J} {E : CStarModule.{0, u₂} J}
    {π : S → Adjointable E E} (hπ : IsRepresentation E π)
    (V : Adjointable (standardModule ℕ J) E) (hV : ∀ ξ, V.adj (V.toFun ξ) = ξ)
    (hcomp : ∀ a ξ, V.adj ((π a).toFun (V.toFun ξ)) = (ψ a).toFun ξ)
    (U : Adjointable (prod (standardModule ℕ J) (kerAdj V)) (standardModule ℕ J))
    (hU : U.IsUnitaryAdj) :
    ∃ ρ : S → StdSumOp J, IsRepresentation (StdSum J) ρ ∧
      ∀ a ξ, (corner11 (ρ a)).toFun ξ = (ψ a).toFun ξ := by
  refine ⟨fun a => Adjointable.comp (Adjointable.adjoint (dilationUnitary V hV U))
      (Adjointable.comp (Adjointable.prodMap (π a)
        (Adjointable.zero (standardModule ℕ J) (standardModule ℕ J)))
        (dilationUnitary V hV U)),
    isRepresentation_unitaryConj (isRepresentation_prodMap_zero hπ)
      (isUnitaryAdj_dilationUnitary V hV hU), fun a ξ => ?_⟩
  rw [corner11_toFun]
  show ((dilationUnitary V hV U).adj
      ((Adjointable.prodMap (π a) (Adjointable.zero (standardModule ℕ J) (standardModule ℕ J))).toFun
        ((dilationUnitary V hV U).toFun (ξ, 0)))).1 = (ψ a).toFun ξ
  rw [dilationUnitary_toFun_inl]
  show V.adj ((π a).toFun (V.toFun ξ)) = (ψ a).toFun ξ
  exact hcomp a ξ

end DilationAssembly

end GroupApproximation.Full.TWWSchafhauser

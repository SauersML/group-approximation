import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionSplitExtCorona
import Mathlib.Tactic.NoncommRing

/-!
# Corona push-forwards: the operator side of `Ext(S, -)` in the second variable

Lane `TWWSch3d2Nat`, work order `WO-TWWSch-3d2-Nat`. Manuscript: `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (l.1370). There the obstruction class lives in
`KK¹(S, J) = Ext(S, J)` and is moved along maps of the coefficient algebra `J`.

## Why an interface, and not `f : J →⋆ₙₐ[ℂ] J'` directly

A Busby cycle of `ObstructionExt` is a lift `S → 𝓛(H_J)`, `H_J = ℓ²(ℕ, J)`, multiplicative
modulo `𝒦(H_J)`. Pushing it forward along a `⋆`-homomorphism `f : J → J'` needs a map
`𝓛(H_J) → 𝓛(H_{J'})`. For a general `f` no such map comes from `f` coordinatewise: `f` does
not extend to multiplier algebras unless it is nondegenerate. The classical construction
(G. G. Kasparov, Izv. Akad. Nauk SSSR 44 (1980), §7; B. Blackadar, *K-theory for operator
algebras*, 13.5 and 17.1) goes through the interior tensor product `H_J ⊗_f J'` (E. C. Lance,
*Hilbert C⋆-modules*, Ch. 4) and Kasparov stabilization `H_J ⊗_f J' ⊕ H_{J'} ≅ H_{J'}` (Lance,
Ch. 6; J. Mingo, W. Phillips, Proc. AMS 91 (1984)). The result is `T ↦ V (T ⊗ 1) V⋆`.

Neither piece is in the repository. So we isolate exactly what the Ext calculus uses from that
construction:

* `CoronaPushforward J J'`: a non-unital `⋆`-homomorphism `𝓑(H_J) → 𝓑(H_{J'})` of bounded
  operators that preserves compact operators and carries the standard direct-sum operator
  `W (A ⊞ B) W⋆` to a direct sum up to a unitary and compacts.

This is a structure, i.e. data together with proofs about that data. It is not a hypothesis
standing in for a theorem. Building `CoronaPushforward.ofHom f` from `f` is sent as a work order
to `main`. The functoriality of `Ext` is proved here for every push-forward.

## What is proved

* `ExtMap.unitize_mul_aux`, `ExtMap.unitize_conj_aux`: the ring identities behind the unitary
  `Φ(v) + (1 - Φ(1))` (a non-unital `Φ` sends unitaries to partial isometries);
* `CoronaPushforward.unitize_unitary`, `CoronaPushforward.unitize_conj`: that unitary, and
  `u Φ(T) u⋆ = Φ(v T v⋆)`;
* `CoronaPushforward.exists_unitary_sum`: the direct-sum clause for an *arbitrary* unitary
  `H_J ⊕ H_J ≅ H_J`, reduced to the standard one;
* `CoronaPushforward.id`, `CoronaPushforward.comp`, `CoronaPushforward.IsEquivalent`.
-/

noncomputable section

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule

namespace ExtMap

/-! ## Ring identities -/

/-- `(a + (1 - P))(b + (1 - P)) = 1` once `ab = P`, `aP = a`, `Pb = b` and `P² = P`. -/
theorem unitize_mul_aux {R : Type*} [Ring R] (a b P : R) (hab : a * b = P) (haP : a * P = a)
    (hPb : P * b = b) (hPP : P * P = P) : (a + (1 - P)) * (b + (1 - P)) = 1 := by
  have key : (a + (1 - P)) * (b + (1 - P))
      = a * b + (a - a * P) + (b - P * b) + (1 - P - P + P * P) := by noncomm_ring
  rw [key, hab, haP, hPb, hPP]
  abel

/-- `(b + (1 - P)) t (a + (1 - P)) = b t a` once `P t = t = t P`. -/
theorem unitize_conj_aux {R : Type*} [Ring R] (b t a P : R) (hPt : P * t = t)
    (htP : t * P = t) : (b + (1 - P)) * (t * (a + (1 - P))) = b * (t * a) := by
  have key : (b + (1 - P)) * (t * (a + (1 - P)))
      = b * (t * a) + (b * t - b * (t * P)) + (t * a - P * t * a)
        + (t - P * t - t * P + P * t * P) := by noncomm_ring
  rw [key, hPt, htP]
  abel

variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-! ## Compact perturbations -/

/-- Replace the left operator of a compact perturbation by a pointwise equal one. -/
theorem compactEq_of_toFun_eq {T T' U : StdOp J} (hT : CompactEq J T U)
    (h : ∀ ξ, T.toFun ξ = T'.toFun ξ) : CompactEq J T' U :=
  Adjointable.IsCompactOp.congr (T := Adjointable.sub T U) (T' := Adjointable.sub T' U)
    (fun ξ => by
      show T.toFun ξ - U.toFun ξ = T'.toFun ξ - U.toFun ξ
      rw [h ξ])
    hT

/-- Conjugation by a bounded operator preserves compact perturbation. -/
theorem compactEq_conj {T U : StdOp J} (h : CompactEq J T U) {V : StdOp J}
    (hV : V.IsBounded) :
    CompactEq J (Adjointable.comp V (Adjointable.comp T (Adjointable.adjoint V)))
      (Adjointable.comp V (Adjointable.comp U (Adjointable.adjoint V))) :=
  Adjointable.IsCompactOp.congr
    (T := Adjointable.comp V (Adjointable.comp (Adjointable.sub T U) (Adjointable.adjoint V)))
    (T' := Adjointable.sub (Adjointable.comp V (Adjointable.comp T (Adjointable.adjoint V)))
      (Adjointable.comp V (Adjointable.comp U (Adjointable.adjoint V))))
    (fun ξ => by
      show V.toFun (T.toFun (V.adj ξ) - U.toFun (V.adj ξ))
        = V.toFun (T.toFun (V.adj ξ)) - V.toFun (U.toFun (V.adj ξ))
      exact V.map_sub _ _)
    (Adjointable.IsCompactOp.comp_left
      (Adjointable.IsCompactOp.comp_right (T := Adjointable.sub T U) h hV.adjoint) hV)

/-! ## Bounded operators as elements of `StdBdd J` -/

/-- A bounded operator on `H_J`, as an element of the `⋆`-algebra `StdBdd J`. -/
def toBdd (T : StdOp J) (hT : T.IsBounded) : StdBdd J :=
  ⟨T, mem_boundedAdj.mpr hT⟩

theorem toBdd_coe (T : StdOp J) (hT : T.IsBounded) : ((toBdd T hT : StdBdd J) : StdOp J) = T :=
  rfl

theorem coe_isBounded (T : StdBdd J) : (T : StdOp J).IsBounded :=
  mem_boundedAdj.mp T.2

theorem bdd_ext {T U : StdBdd J} (h : ∀ x, (T : StdOp J).toFun x = (U : StdOp J).toFun x) :
    T = U :=
  Subtype.ext (adjointable_ext h)

/-- The coercion of `u t u⋆` is the composite `u ∘ t ∘ u⋆`, definitionally. -/
theorem coe_mul_mul_star (u t : StdBdd J) :
    ((u * (t * star u) : StdBdd J) : StdOp J)
      = Adjointable.comp (u : StdOp J) (Adjointable.comp (t : StdOp J)
          (Adjointable.adjoint (u : StdOp J))) :=
  rfl

theorem star_mul_toBdd {U : StdOp J} (hU : U.IsUnitaryAdj) :
    star (toBdd U hU.isBounded) * toBdd U hU.isBounded = 1 :=
  bdd_ext fun x => hU.adj_toFun x

theorem mul_star_toBdd {U : StdOp J} (hU : U.IsUnitaryAdj) :
    toBdd U hU.isBounded * star (toBdd U hU.isBounded) = 1 :=
  bdd_ext fun x => hU.toFun_adj x

/-- A unitary of the `⋆`-algebra `StdBdd J` is a unitary operator. -/
theorem isUnitaryAdj_of_bdd {u : StdBdd J} (h1 : star u * u = 1) (h2 : u * star u = 1) :
    (u : StdOp J).IsUnitaryAdj where
  adj_toFun x := congrArg (fun T : StdBdd J => (T : StdOp J).toFun x) h1
  toFun_adj x := congrArg (fun T : StdBdd J => (T : StdOp J).toFun x) h2

/-! ## The standard direct sum `W (A ⊞ B) W⋆`, `W = natSumMerge J` -/

/-- The standard direct sum of two bounded operators, transported to `H_J` by the canonical
unitary `natSumMerge J : H_J ⊕ H_J ≅ H_J`. -/
def sumBdd (A B : StdBdd J) : StdBdd J :=
  toBdd (Adjointable.comp (Adjointable.natSumMerge J)
      (Adjointable.comp (Adjointable.prodMap (A : StdOp J) (B : StdOp J))
        (Adjointable.adjoint (Adjointable.natSumMerge J))))
    (isBounded_comp_of (Adjointable.isUnitaryAdj_natSumMerge J).isBounded
      (isBounded_comp_of ((coe_isBounded A).prodMap (coe_isBounded B))
        (Adjointable.isUnitaryAdj_natSumMerge J).adjoint.isBounded))

theorem isUnitaryAdj_sumConjOp {U : Adjointable (HilbertModule.prod (standardModule ℕ J)
    (standardModule ℕ J)) (standardModule ℕ J)} (hU : U.IsUnitaryAdj) :
    (U.comp (Adjointable.adjoint (Adjointable.natSumMerge J))).IsUnitaryAdj :=
  hU.comp (Adjointable.isUnitaryAdj_natSumMerge J).adjoint

/-- The unitary `U W⋆` of `H_J`, comparing a unitary `U : H_J ⊕ H_J ≅ H_J` with the standard
one. -/
def sumConj (U : Adjointable (HilbertModule.prod (standardModule ℕ J) (standardModule ℕ J))
    (standardModule ℕ J)) (hU : U.IsUnitaryAdj) : StdBdd J :=
  toBdd (U.comp (Adjointable.adjoint (Adjointable.natSumMerge J)))
    (isUnitaryAdj_sumConjOp hU).isBounded

variable {U : Adjointable (HilbertModule.prod (standardModule ℕ J) (standardModule ℕ J))
  (standardModule ℕ J)}

theorem star_mul_sumConj (hU : U.IsUnitaryAdj) : star (sumConj U hU) * sumConj U hU = 1 :=
  star_mul_toBdd (isUnitaryAdj_sumConjOp hU)

theorem mul_star_sumConj (hU : U.IsUnitaryAdj) : sumConj U hU * star (sumConj U hU) = 1 :=
  mul_star_toBdd (isUnitaryAdj_sumConjOp hU)

/-- `(U W⋆) (W (A ⊞ B) W⋆) (U W⋆)⋆ = U (A ⊞ B) U⋆`, pointwise. -/
theorem sumConj_conj_toFun (hU : U.IsUnitaryAdj) (A B : StdBdd J)
    (ξ : (standardModule ℕ J).carrier) :
    ((sumConj U hU * (sumBdd A B * star (sumConj U hU)) : StdBdd J) : StdOp J).toFun ξ
      = U.toFun ((Adjointable.prodMap (A : StdOp J) (B : StdOp J)).toFun (U.adj ξ)) := by
  show U.toFun ((Adjointable.natSumMerge J).adj ((Adjointable.natSumMerge J).toFun
      ((Adjointable.prodMap (A : StdOp J) (B : StdOp J)).toFun ((Adjointable.natSumMerge J).adj
        ((Adjointable.natSumMerge J).toFun (U.adj ξ)))))) = _
  rw [(Adjointable.isUnitaryAdj_natSumMerge J).adj_toFun,
    (Adjointable.isUnitaryAdj_natSumMerge J).adj_toFun]

/-- A direct sum under an arbitrary unitary `U` is the standard one conjugated by `U W⋆`. -/
theorem compactEq_sumConj (hU : U.IsUnitaryAdj) {A B C : StdBdd J}
    (h : CompactEq J (Adjointable.comp U (Adjointable.comp
      (Adjointable.prodMap (A : StdOp J) (B : StdOp J)) (Adjointable.adjoint U))) (C : StdOp J)) :
    CompactEq J ((sumConj U hU * (sumBdd A B * star (sumConj U hU)) : StdBdd J) : StdOp J)
      (C : StdOp J) :=
  compactEq_of_toFun_eq h fun ξ => (sumConj_conj_toFun hU A B ξ).symm

end ExtMap

/-! ## The interface -/

/-- **A corona push-forward** `𝓑(H_J) → 𝓑(H_{J'})`. It is the operator-level datum that moves
Busby cycles from `J` to `J'` (Kasparov 1980 §7, Blackadar 17.1). It consists of

* a non-unital `⋆`-homomorphism of the bounded operators;
* preservation of compact operators, so that it descends to the corona algebras;
* compatibility with direct sums: the standard sum `W (A ⊞ B) W⋆` goes to `Φ A ⊞ Φ B` up to a
  unitary `H_{J'} ⊕ H_{J'} ≅ H_{J'}` and compacts.

For `T ↦ V (T ⊗ 1) V⋆` the third clause holds with an explicit unitary. The construction from
a `⋆`-homomorphism `f : J → J'` (`CoronaPushforward.ofHom`) is a separate work order. -/
structure CoronaPushforward (J J' : Type) [NonUnitalCStarAlgebra J] [PartialOrder J]
    [StarOrderedRing J] [NonUnitalCStarAlgebra J'] [PartialOrder J'] [StarOrderedRing J'] where
  /-- The map on bounded operators. -/
  toHom : StdBdd J →⋆ₙₐ[ℂ] StdBdd J'
  /-- Compact operators go to compact operators. -/
  map_compact : ∀ T : StdBdd J, Adjointable.IsCompactOp (T : StdOp J) →
    Adjointable.IsCompactOp (toHom T : StdOp J')
  /-- The standard direct sum goes to a direct sum, up to a unitary and compacts. -/
  exists_sum_unitary : ∃ R : Adjointable (HilbertModule.prod (standardModule ℕ J')
      (standardModule ℕ J')) (standardModule ℕ J'), R.IsUnitaryAdj ∧
    ∀ A B : StdBdd J, CompactEq J' (Adjointable.comp R (Adjointable.comp
      (Adjointable.prodMap (toHom A : StdOp J') (toHom B : StdOp J')) (Adjointable.adjoint R)))
      (toHom (ExtMap.sumBdd A B) : StdOp J')

namespace CoronaPushforward

variable {J J' J'' : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]
  [NonUnitalCStarAlgebra J'] [PartialOrder J'] [StarOrderedRing J']
  [NonUnitalCStarAlgebra J''] [PartialOrder J''] [StarOrderedRing J'']

/-- A push-forward preserves compact perturbation. -/
theorem compactEq (Φ : CoronaPushforward J J') {A B : StdBdd J}
    (h : CompactEq J (A : StdOp J) (B : StdOp J)) :
    CompactEq J' (Φ.toHom A : StdOp J') (Φ.toHom B : StdOp J') := by
  have hk := Φ.map_compact (A - B) h
  rw [_root_.map_sub Φ.toHom] at hk
  exact hk

/-- The unitary `Φ(v) + (1 - Φ(1))` attached to a unitary `v`. The non-unital `Φ` only sends
`v` to a partial isometry, and the correction `1 - Φ(1)` completes it. -/
def unitize (Φ : CoronaPushforward J J') (v : StdBdd J) : StdBdd J' :=
  Φ.toHom v + (1 - Φ.toHom 1)

theorem star_unitize (Φ : CoronaPushforward J J') (v : StdBdd J) :
    star (Φ.unitize v) = Φ.toHom (star v) + (1 - Φ.toHom 1) := by
  rw [CoronaPushforward.unitize, star_add, star_sub, star_one, ← _root_.map_star Φ.toHom v,
    ← _root_.map_star Φ.toHom 1, star_one]

/-- `u Φ(T) u⋆ = Φ(v T v⋆)` for `u = Φ.unitize v`. -/
theorem unitize_conj (Φ : CoronaPushforward J J') (v T : StdBdd J) :
    Φ.unitize v * (Φ.toHom T * star (Φ.unitize v)) = Φ.toHom (v * (T * star v)) := by
  have hPt : Φ.toHom 1 * Φ.toHom T = Φ.toHom T := by
    rw [← _root_.map_mul Φ.toHom, one_mul]
  have htP : Φ.toHom T * Φ.toHom 1 = Φ.toHom T := by
    rw [← _root_.map_mul Φ.toHom, mul_one]
  rw [Φ.star_unitize, _root_.map_mul Φ.toHom, _root_.map_mul Φ.toHom, CoronaPushforward.unitize]
  exact ExtMap.unitize_conj_aux _ _ _ _ hPt htP

/-- `Φ.unitize v` is a unitary when `v` is. -/
theorem unitize_unitary (Φ : CoronaPushforward J J') {v : StdBdd J} (h1 : star v * v = 1)
    (h2 : v * star v = 1) :
    star (Φ.unitize v) * Φ.unitize v = 1 ∧ Φ.unitize v * star (Φ.unitize v) = 1 := by
  have hP : Φ.toHom 1 * Φ.toHom 1 = Φ.toHom 1 := by rw [← _root_.map_mul Φ.toHom, one_mul]
  have hsv : Φ.toHom (star v) * Φ.toHom v = Φ.toHom 1 := by rw [← _root_.map_mul Φ.toHom, h1]
  have hvs : Φ.toHom v * Φ.toHom (star v) = Φ.toHom 1 := by rw [← _root_.map_mul Φ.toHom, h2]
  have hsP : Φ.toHom (star v) * Φ.toHom 1 = Φ.toHom (star v) := by
    rw [← _root_.map_mul Φ.toHom, mul_one]
  have hPs : Φ.toHom 1 * Φ.toHom (star v) = Φ.toHom (star v) := by
    rw [← _root_.map_mul Φ.toHom, one_mul]
  have hvP : Φ.toHom v * Φ.toHom 1 = Φ.toHom v := by rw [← _root_.map_mul Φ.toHom, mul_one]
  have hPv : Φ.toHom 1 * Φ.toHom v = Φ.toHom v := by rw [← _root_.map_mul Φ.toHom, one_mul]
  rw [Φ.star_unitize, CoronaPushforward.unitize]
  exact ⟨ExtMap.unitize_mul_aux _ _ _ hsv hsP hPv hP, ExtMap.unitize_mul_aux _ _ _ hvs hvP hPs hP⟩

/-- **Direct sums under an arbitrary unitary.** Given any unitary `U : H_J ⊕ H_J ≅ H_J`, one
unitary `U'` for `J'` carries every `U`-direct sum to a `U'`-direct sum. Here
`U' = (Φ.unitize (U W⋆)) R`, where `R` is the unitary of `exists_sum_unitary`. -/
theorem exists_unitary_sum (Φ : CoronaPushforward J J')
    {U : Adjointable (HilbertModule.prod (standardModule ℕ J) (standardModule ℕ J))
      (standardModule ℕ J)} (hU : U.IsUnitaryAdj) :
    ∃ U' : Adjointable (HilbertModule.prod (standardModule ℕ J') (standardModule ℕ J'))
      (standardModule ℕ J'), U'.IsUnitaryAdj ∧
      ∀ A B C : StdBdd J, CompactEq J (Adjointable.comp U (Adjointable.comp
        (Adjointable.prodMap (A : StdOp J) (B : StdOp J)) (Adjointable.adjoint U))) (C : StdOp J) →
        CompactEq J' (Adjointable.comp U' (Adjointable.comp
          (Adjointable.prodMap (Φ.toHom A : StdOp J') (Φ.toHom B : StdOp J'))
          (Adjointable.adjoint U'))) (Φ.toHom C : StdOp J') := by
  obtain ⟨R, hR, hsum⟩ := Φ.exists_sum_unitary
  have hu := Φ.unitize_unitary (ExtMap.star_mul_sumConj hU) (ExtMap.mul_star_sumConj hU)
  refine ⟨Adjointable.comp (Φ.unitize (ExtMap.sumConj U hU) : StdOp J') R,
    (ExtMap.isUnitaryAdj_of_bdd hu.1 hu.2).comp hR, fun A B C h => ?_⟩
  have h2 := Φ.compactEq (ExtMap.compactEq_sumConj hU h)
  rw [← Φ.unitize_conj, ExtMap.coe_mul_mul_star] at h2
  have h3 := ExtMap.compactEq_conj (hsum A B)
    (ExtMap.coe_isBounded (Φ.unitize (ExtMap.sumConj U hU)))
  exact ExtMap.compactEq_of_toFun_eq (compactEq_trans h3 h2) fun _ => rfl

/-- The identity push-forward. -/
protected def id (J : Type) [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J] :
    CoronaPushforward J J where
  toHom := NonUnitalStarAlgHom.id ℂ (StdBdd J)
  map_compact _ h := h
  exists_sum_unitary := ⟨Adjointable.natSumMerge J, Adjointable.isUnitaryAdj_natSumMerge J,
    fun _ _ => compactEq_refl _⟩

/-- The composite of two push-forwards. The direct-sum clause of `Ψ` is used for the unitary
supplied by `Φ`, through `exists_unitary_sum`. -/
protected def comp (Ψ : CoronaPushforward J' J'') (Φ : CoronaPushforward J J') :
    CoronaPushforward J J'' where
  toHom := Ψ.toHom.comp Φ.toHom
  map_compact T h := Ψ.map_compact (Φ.toHom T) (Φ.map_compact T h)
  exists_sum_unitary := by
    obtain ⟨R, hR, hsum⟩ := Φ.exists_sum_unitary
    obtain ⟨U', hU', hU'sum⟩ := Ψ.exists_unitary_sum hR
    exact ⟨U', hU', fun A B => hU'sum (Φ.toHom A) (Φ.toHom B) (Φ.toHom (ExtMap.sumBdd A B))
      (hsum A B)⟩

theorem id_toHom_apply (T : StdBdd J) : (CoronaPushforward.id J).toHom T = T :=
  rfl

theorem comp_toHom_apply (Ψ : CoronaPushforward J' J'') (Φ : CoronaPushforward J J')
    (T : StdBdd J) : (Ψ.comp Φ).toHom T = Ψ.toHom (Φ.toHom T) :=
  rfl

/-- Two push-forwards are **equivalent** when they agree up to one unitary of `H_{J'}` and
compacts. Equivalent push-forwards induce the same map on `Ext`
(`ExtGroup.mapOf_eq_of_isEquivalent`). This is the sense in which `ofHom id` is `id` and
`ofHom (g ∘ f)` is `ofHom g ∘ ofHom f` (Blackadar 17.1). -/
def IsEquivalent (Φ Φ' : CoronaPushforward J J') : Prop :=
  ∃ R : StdOp J', R.IsUnitaryAdj ∧ ∀ T : StdBdd J,
    CompactEq J' (Adjointable.comp R (Adjointable.comp (Φ.toHom T : StdOp J')
      (Adjointable.adjoint R))) (Φ'.toHom T : StdOp J')

theorem IsEquivalent.refl (Φ : CoronaPushforward J J') : Φ.IsEquivalent Φ :=
  ⟨Adjointable.id _, Adjointable.isUnitaryAdj_id _, fun T =>
    ExtMap.compactEq_of_toFun_eq (compactEq_refl (Φ.toHom T : StdOp J')) fun _ => rfl⟩

end CoronaPushforward

end GroupApproximation.Full.TWWSchafhauser

end

import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionExtInverseCorners

/-!
# The complement of a dilation is an inverse

Lane `TWWSch3d2Inv`, work order `WO-TWWSch-3d2-Inv`, step 3.

Let `x` be a Busby cycle over `S` with coefficients in `J`, and let `ρ` be an honest
representation of `S` on `H_J ⊕ H_J` whose `(1,1)` corner is `x` modulo compacts and whose
`(2,1)` corner is compact. Then the `(2,2)` corner `c = (1 - VV*) ρ (1 - VV*)` is a Busby cycle,
and under the unitary `natSumMerge J : H_J ⊕ H_J ≅ H_J` the diagonal `x ⊕ c` agrees with the
split cycle `Ad(natSumMerge) ∘ ρ` modulo compacts. So `c` inverts `x` in `Ext(S, J)`.
This is the formal part of Arveson, Duke Math. J. 44 (1977), §4, and Kasparov,
J. Operator Theory 4 (1980), §7 (Blackadar, *K-theory for operator algebras*, 15.6–15.7).

* `BusbyCycle.ofRepresentation`, `BusbyCycle.isSplit_ofRepresentation`: a representation is a
  split cycle;
* `conjMerge`, `isRepresentation_conjMerge`: transport along `natSumMerge J`;
* `complementCycle`: the `(2,2)` corner as a Busby cycle;
* `isDirectSum_conjMerge` and **`BusbyCycle.exists_inverse_of_representation`**;
* `isCompactOp_adjoint_comp_corner21`: when the `(1,1)` corner of `ρ` is `x` modulo compacts,
  `T₂₁* T₂₁ = T₁₁(a*a) - T₁₁(a*) T₁₁(a)` is compact for `T₂₁ = corner21 (ρ a)`;
* `IsCPCOp`: the pointwise completely positive contractive maps `S → 𝓛(H_J)` that the
  Choi–Effros lift produces and the Kasparov–Stinespring dilation consumes.
-/

noncomputable section

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule

section Complement

variable {S : Type} [NonUnitalCStarAlgebra S]
variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- **A representation of `S` on `H_J` is a split Busby cycle.** -/
def BusbyCycle.ofRepresentation (ρ : S → StdOp J)
    (hρ : IsRepresentation (standardModule ℕ J) ρ) : BusbyCycle S J where
  lift := ρ
  bounded := hρ.bounded
  map_add a a' := compactEq_of_toFun_eq fun ξ => hρ.map_add a a' ξ
  map_smul c a := compactEq_of_toFun_eq fun ξ => hρ.map_smul c a ξ
  map_mul a a' := compactEq_of_toFun_eq fun ξ => hρ.map_mul a a' ξ
  map_star a := compactEq_of_toFun_eq fun ξ => hρ.map_star a ξ

theorem BusbyCycle.isSplit_ofRepresentation (ρ : S → StdOp J)
    (hρ : IsRepresentation (standardModule ℕ J) ρ) :
    (BusbyCycle.ofRepresentation ρ hρ).IsSplit :=
  ⟨ρ, hρ, fun a => compactEq_refl (ρ a)⟩

/-- Transport of an operator on `H_J ⊕ H_J` to `H_J` along `natSumMerge J`. -/
def conjMerge (T : StdSumOp J) : StdOp J :=
  Adjointable.comp (Adjointable.natSumMerge J)
    (Adjointable.comp T (Adjointable.adjoint (Adjointable.natSumMerge J)))

theorem isRepresentation_conjMerge {ρ : S → StdSumOp J} (hρ : IsRepresentation (StdSum J) ρ) :
    IsRepresentation (standardModule ℕ J) (fun a => conjMerge (ρ a)) where
  bounded a := isBounded_comp (Adjointable.isUnitaryAdj_natSumMerge J).isBounded
    (isBounded_comp (hρ.bounded a) (Adjointable.isUnitaryAdj_natSumMerge J).isBounded.adjoint)
  map_add a a' ξ := by
    show (Adjointable.natSumMerge J).toFun
        ((ρ (a + a')).toFun ((Adjointable.natSumMerge J).adj ξ))
      = (Adjointable.natSumMerge J).toFun ((ρ a).toFun ((Adjointable.natSumMerge J).adj ξ))
        + (Adjointable.natSumMerge J).toFun ((ρ a').toFun ((Adjointable.natSumMerge J).adj ξ))
    rw [hρ.map_add, Adjointable.map_add]
  map_smul c a ξ := by
    show (Adjointable.natSumMerge J).toFun
        ((ρ (c • a)).toFun ((Adjointable.natSumMerge J).adj ξ))
      = c • (Adjointable.natSumMerge J).toFun
        ((ρ a).toFun ((Adjointable.natSumMerge J).adj ξ))
    rw [hρ.map_smul, Adjointable.map_smul]
  map_mul a a' ξ := by
    show (Adjointable.natSumMerge J).toFun
        ((ρ (a * a')).toFun ((Adjointable.natSumMerge J).adj ξ))
      = (Adjointable.natSumMerge J).toFun ((ρ a).toFun ((Adjointable.natSumMerge J).adj
        ((Adjointable.natSumMerge J).toFun ((ρ a').toFun ((Adjointable.natSumMerge J).adj ξ)))))
    rw [hρ.map_mul, (Adjointable.isUnitaryAdj_natSumMerge J).adj_toFun]
  map_star a ξ := by
    show (Adjointable.natSumMerge J).toFun
        ((ρ (star a)).toFun ((Adjointable.natSumMerge J).adj ξ))
      = (Adjointable.natSumMerge J).toFun ((ρ a).adj ((Adjointable.natSumMerge J).adj ξ))
    rw [hρ.map_star]

/-- **The complement cycle** `c = (1 - VV*) ρ (1 - VV*)`: the `(2,2)` corner of a
representation on `H_J ⊕ H_J` with compact `(2,1)` corner. Multiplicativity modulo compacts is
`T₂₂(aa') = T₂₁(a) T₁₂(a') + T₂₂(a) T₂₂(a')`. -/
def complementCycle (ρ : S → StdSumOp J) (hρ : IsRepresentation (StdSum J) ρ)
    (hoff : ∀ a, (corner21 (ρ a)).IsCompactOp) : BusbyCycle S J where
  lift a := corner22 (ρ a)
  bounded a := isBounded_corner22 (hρ.bounded a)
  map_add a a' := compactEq_of_toFun_eq fun η => by
    show ((ρ (a + a')).toFun (0, η)).2 = ((ρ a).toFun (0, η)).2 + ((ρ a').toFun (0, η)).2
    rw [hρ.map_add, stdSum_snd_add]
  map_smul c a := compactEq_of_toFun_eq fun η => by
    show ((ρ (c • a)).toFun (0, η)).2 = c • ((ρ a).toFun (0, η)).2
    rw [hρ.map_smul, stdSum_snd_smul]
  map_mul a a' := by
    show Adjointable.IsCompactOp (Adjointable.sub (corner22 (ρ (a * a')))
      (Adjointable.comp (corner22 (ρ a)) (corner22 (ρ a'))))
    refine Adjointable.IsCompactOp.congr (fun η => ?_)
      (Adjointable.IsCompactOp.comp_right (hoff a) (isBounded_corner12 (hρ.bounded a')))
    show ((ρ a).toFun (((ρ a').toFun (0, η)).1, 0)).2
      = ((ρ (a * a')).toFun (0, η)).2 - ((ρ a).toFun (0, ((ρ a').toFun (0, η)).2)).2
    rw [hρ.map_mul, toFun_split' (ρ a) ((ρ a').toFun (0, η)), stdSum_snd_add]
    abel
  map_star a := compactEq_of_toFun_eq fun η => by
    show ((ρ (star a)).toFun (0, η)).2 = ((ρ a).adj (0, η)).2
    rw [hρ.map_star]

/-- The `(1,2)` corner is compact too: it is the adjoint of the `(2,1)` corner at `a*`. -/
theorem isCompactOp_corner12 {ρ : S → StdSumOp J} (hρ : IsRepresentation (StdSum J) ρ)
    (hoff : ∀ a, (corner21 (ρ a)).IsCompactOp) (a : S) : (corner12 (ρ a)).IsCompactOp := by
  refine Adjointable.IsCompactOp.congr (fun η => ?_) (hoff (star a)).adjoint
  show ((ρ (star a)).adj (0, η)).1 = ((ρ a).toFun (0, η)).1
  rw [← hρ.map_star, star_star]

/-- `x ⊕ c - ρ = ι₁ (x - T₁₁) π₁ - ι₁ T₁₂ π₂ - ι₂ T₂₁ π₁` is compact. -/
theorem isCompactOp_prodMap_sub (x : BusbyCycle S J) {ρ : S → StdSumOp J}
    (hρ : IsRepresentation (StdSum J) ρ) (hcorner : ∀ a, CompactEq J (x.lift a) (corner11 (ρ a)))
    (hoff : ∀ a, (corner21 (ρ a)).IsCompactOp) (a : S) :
    (Adjointable.sub (Adjointable.prodMap (x.lift a) (corner22 (ρ a))) (ρ a)).IsCompactOp := by
  have h1 := Adjointable.IsCompactOp.comp_left
    (Adjointable.IsCompactOp.comp_right (hcorner a).isCompactOp
      (Adjointable.isBounded_fstProj (E := standardModule ℕ J) (F := standardModule ℕ J)))
    (Adjointable.isBounded_inl (E := standardModule ℕ J) (F := standardModule ℕ J))
  have h2 := Adjointable.IsCompactOp.comp_left
    (Adjointable.IsCompactOp.comp_right (isCompactOp_corner12 hρ hoff a)
      (Adjointable.isBounded_sndProj (E := standardModule ℕ J) (F := standardModule ℕ J)))
    (Adjointable.isBounded_inl (E := standardModule ℕ J) (F := standardModule ℕ J))
  have h3 := Adjointable.IsCompactOp.comp_right (hoff a)
    (Adjointable.isBounded_fstProj (E := standardModule ℕ J) (F := standardModule ℕ J))
  have h3' := Adjointable.IsCompactOp.comp_left h3
    (Adjointable.isBounded_inr (E := standardModule ℕ J) (F := standardModule ℕ J))
  refine Adjointable.IsCompactOp.congr (fun p => ?_)
    (Adjointable.IsCompactOp.sub (Adjointable.IsCompactOp.sub h1 h2) h3')
  refine Prod.ext ?_ ?_
  · show (x.lift a).toFun p.1 - ((ρ a).toFun (p.1, 0)).1 - ((ρ a).toFun (0, p.2)).1 - 0
      = (x.lift a).toFun p.1 - ((ρ a).toFun p).1
    rw [toFun_split' (ρ a) p, stdSum_fst_add]
    abel
  · show (0 : (standardModule ℕ J).carrier) - 0 - ((ρ a).toFun (p.1, 0)).2
      = ((ρ a).toFun (0, p.2)).2 - ((ρ a).toFun p).2
    rw [toFun_split' (ρ a) p, stdSum_snd_add]
    abel

theorem isDirectSum_conjMerge (x : BusbyCycle S J) {ρ : S → StdSumOp J}
    (hρ : IsRepresentation (StdSum J) ρ) (hcorner : ∀ a, CompactEq J (x.lift a) (corner11 (ρ a)))
    (hoff : ∀ a, (corner21 (ρ a)).IsCompactOp) :
    (BusbyCycle.ofRepresentation _ (isRepresentation_conjMerge hρ)).IsDirectSum x
      (complementCycle ρ hρ hoff) := by
  refine ⟨Adjointable.natSumMerge J, Adjointable.isUnitaryAdj_natSumMerge J, fun a => ?_⟩
  show Adjointable.IsCompactOp (Adjointable.sub
    (Adjointable.comp (Adjointable.natSumMerge J)
      (Adjointable.comp (Adjointable.prodMap (x.lift a) (corner22 (ρ a)))
        (Adjointable.adjoint (Adjointable.natSumMerge J))))
    (conjMerge (ρ a)))
  refine Adjointable.IsCompactOp.congr (fun ξ => ?_)
    (Adjointable.IsCompactOp.comp_left
      (Adjointable.IsCompactOp.comp_right (isCompactOp_prodMap_sub x hρ hcorner hoff a)
        (Adjointable.isUnitaryAdj_natSumMerge J).isBounded.adjoint)
      (Adjointable.isUnitaryAdj_natSumMerge J).isBounded)
  show (Adjointable.natSumMerge J).toFun
      ((Adjointable.prodMap (x.lift a) (corner22 (ρ a))).toFun
          ((Adjointable.natSumMerge J).adj ξ)
        - (ρ a).toFun ((Adjointable.natSumMerge J).adj ξ))
    = (Adjointable.natSumMerge J).toFun
        ((Adjointable.prodMap (x.lift a) (corner22 (ρ a))).toFun
          ((Adjointable.natSumMerge J).adj ξ))
      - (Adjointable.natSumMerge J).toFun ((ρ a).toFun ((Adjointable.natSumMerge J).adj ξ))
  rw [Adjointable.map_sub]

/-- **Step 3 of the inverse** (Arveson 1977 §4; Kasparov 1980 §7; Blackadar 15.7): a
representation of `S` on `H_J ⊕ H_J` whose `(1,1)` corner is `x` modulo compacts and whose
`(2,1)` corner is compact exhibits an inverse of `x` up to split cycles. -/
theorem BusbyCycle.exists_inverse_of_representation (x : BusbyCycle S J) (ρ : S → StdSumOp J)
    (hρ : IsRepresentation (StdSum J) ρ) (hcorner : ∀ a, CompactEq J (x.lift a) (corner11 (ρ a)))
    (hoff : ∀ a, (corner21 (ρ a)).IsCompactOp) :
    ∃ (c d : BusbyCycle S J), d.IsDirectSum x c ∧ d.IsSplit :=
  ⟨complementCycle ρ hρ hoff, BusbyCycle.ofRepresentation _ (isRepresentation_conjMerge hρ),
    isDirectSum_conjMerge x hρ hcorner hoff, BusbyCycle.isSplit_ofRepresentation _ _⟩

/-- **The off-diagonal corner squares to a compact**: if `T₁₁ ∘ ρ ≡ x` modulo compacts then
`T₂₁(b)* T₂₁(b) = T₁₁(b*b) - T₁₁(b*) T₁₁(b)` is compact (Kasparov 1980, §7, proof of Thm 2). -/
theorem isCompactOp_adjoint_comp_corner21 (x : BusbyCycle S J) {ρ : S → StdSumOp J}
    (hρ : IsRepresentation (StdSum J) ρ) (hcorner : ∀ a, CompactEq J (x.lift a) (corner11 (ρ a)))
    (b : S) :
    (Adjointable.comp (Adjointable.adjoint (corner21 (ρ b))) (corner21 (ρ b))).IsCompactOp := by
  have hkey : CompactEq J (corner11 (ρ (star b * b)))
      (Adjointable.comp (corner11 (ρ (star b))) (corner11 (ρ b))) :=
    compactEq_trans (compactEq_trans (compactEq_symm (hcorner (star b * b)))
      (x.map_mul (star b) b))
      (CompactEq.comp (hcorner (star b)) (hcorner b) (isBounded_corner11 (hρ.bounded _))
        (x.bounded b))
  refine Adjointable.IsCompactOp.congr (fun ξ => ?_) hkey.isCompactOp
  show ((ρ (star b * b)).toFun (ξ, 0)).1
      - ((ρ (star b)).toFun (((ρ b).toFun (ξ, 0)).1, 0)).1
    = ((ρ b).adj (0, ((ρ b).toFun (ξ, 0)).2)).1
  rw [← hρ.map_star, hρ.map_mul, toFun_split' (ρ (star b)) ((ρ b).toFun (ξ, 0)),
    stdSum_fst_add]
  abel

end Complement

section CPC

variable {S : Type} [CStarAlgebra S]
variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- **A completely positive contraction `S → 𝓛(H_J)`**, stated pointwise: linear, `⋆`-preserving,
bounded, with positive matrices `[⟨ξᵢ, ψ(aᵢ* aⱼ) ξⱼ⟩]` summed against vectors (Lance, *Hilbert
C*-modules*, Ch. 5; Kasparov 1980, §7), and `ψ(1)` a contraction. -/
structure IsCPCOp (ψ : S → StdOp J) : Prop where
  bounded : ∀ a : S, (ψ a).IsBounded
  map_add : ∀ (a a' : S) (ξ : (standardModule ℕ J).carrier),
    (ψ (a + a')).toFun ξ = (ψ a).toFun ξ + (ψ a').toFun ξ
  map_smul : ∀ (c : ℂ) (a : S) (ξ : (standardModule ℕ J).carrier),
    (ψ (c • a)).toFun ξ = c • (ψ a).toFun ξ
  map_star : ∀ (a : S) (ξ : (standardModule ℕ J).carrier),
    (ψ (star a)).toFun ξ = (ψ a).adj ξ
  posDef : ∀ (n : ℕ) (a : Fin n → S) (ξ : Fin n → (standardModule ℕ J).carrier),
    OrderZero.IsPositiveElem
      (∑ i, ∑ j, (standardModule ℕ J).inner (ξ i) ((ψ (star (a i) * a j)).toFun (ξ j)))
  contractive : (ψ 1).IsBoundedBy 1

end CPC

end GroupApproximation.Full.TWWSchafhauser

end

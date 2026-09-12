import GroupApproximation.Algebra.RabinVariantTower
import GroupApproximation.Algebra.HNNTrivialAssociated
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Tactic.Group
import Mathlib.Tactic.NormNum

/-!
# The presentation of the variant construction

`Algebra.RabinVariantTower` builds the tower and proves both halves of the
biconditional for it.  The Adian--Rabin reduction, however, is a statement about
a *presentation*: the map it needs is `w ↦ P(w)` with `P(w)` a finite
presentation.  This file writes that presentation down and maps it into the
tower.

The generators are the source generators `xᵢ`, the free letter `s`, one letter
`tᵢ` for each `sᵢ`, and the four cascade letters `u`, `b`, `c`, `k`.  The
relators are the source relators together with

    `u tᵢ u⁻¹ (tᵢ sᵢ)⁻¹`,   `b u b⁻¹ u⁻²`,   `c b c⁻¹ b⁻²`,   `k z k⁻¹ c⁻¹`,

where `sᵢ` is `s` for `i = 0` and `s xᵢ₋₁` otherwise, and `z = ⁅w, s⁆`.

`toTower` is the homomorphism into the tower, and it exists because every one of
those relators holds there --- which is exactly what
`RabinVariantTower.conj_t_eq_ts`, `casc1_conj`, `casc2_conj` and `full_conj`
say.  Composing with it turns the tower's `full_base_injective` into the
statement the reduction needs: the source group embeds in the *presented*
group.
-/

namespace GroupApproximation
namespace RabinVariantPresentation

open RabinVariantTower

/-- The letters adjoined to the source generators. -/
inductive Extra (m : ℕ) : Type
  | s : Extra m
  | t : Fin (m + 1) → Extra m
  | u : Extra m
  | b : Extra m
  | c : Extra m
  | k : Extra m
  deriving DecidableEq

/-- The generators of the presentation. -/
abbrev Gen (m : ℕ) : Type := Fin m ⊕ Extra m

variable {m : ℕ}

/-- A source generator, as a word. -/
def X (i : Fin m) : FreeGroup (Gen m) := FreeGroup.of (Sum.inl i)

/-- The free letter, as a word. -/
def S : FreeGroup (Gen m) := FreeGroup.of (Sum.inr Extra.s)

/-- The `i`th stable letter of the killing layer, as a word. -/
def T (i : Fin (m + 1)) : FreeGroup (Gen m) := FreeGroup.of (Sum.inr (Extra.t i))

/-- The cascade letters, as words. -/
def U : FreeGroup (Gen m) := FreeGroup.of (Sum.inr Extra.u)
/-- The second cascade letter. -/
def B : FreeGroup (Gen m) := FreeGroup.of (Sum.inr Extra.b)
/-- The third cascade letter. -/
def C : FreeGroup (Gen m) := FreeGroup.of (Sum.inr Extra.c)
/-- The last cascade letter. -/
def K : FreeGroup (Gen m) := FreeGroup.of (Sum.inr Extra.k)

/-- `sᵢ`: the letter `s` at `i = 0`, and `s xᵢ₋₁` afterwards.  The change of
generators, at the level of words. -/
def sWord (i : Fin (m + 1)) : FreeGroup (Gen m) :=
  Fin.cases S (fun j => S * X j) i

@[simp] theorem sWord_zero : sWord (0 : Fin (m + 1)) = S := rfl

@[simp] theorem sWord_succ (j : Fin m) : sWord j.succ = S * X j := rfl

/-- The source generators, embedded in the larger free group. -/
def emb : FreeGroup (Fin m) →* FreeGroup (Gen m) := FreeGroup.map Sum.inl

/-- The witness word `z = ⁅w, s⁆`. -/
def Z (w : FreeGroup (Fin m)) : FreeGroup (Gen m) :=
  emb w * S * (emb w)⁻¹ * S⁻¹

/-- **The relators.**  The source relators, the killing relations, and the
cascade. -/
def relators (R : Set (FreeGroup (Fin m))) (w : FreeGroup (Fin m)) :
    Set (FreeGroup (Gen m)) :=
  (fun r => emb r) '' R
    ∪ Set.range (fun i : Fin (m + 1) => U * T i * U⁻¹ * (T i * sWord i)⁻¹)
    ∪ {B * U * B⁻¹ * (U ^ (2 : ℕ))⁻¹, C * B * C⁻¹ * (B ^ (2 : ℕ))⁻¹,
        K * Z w * K⁻¹ * C⁻¹}

/-- **The presented group of the construction.** -/
abbrev Pres (R : Set (FreeGroup (Fin m))) (w : FreeGroup (Fin m)) : Type :=
  PresentedGroup (relators R w)

/-! ## Mapping the presentation into the tower

Every relator holds in the tower, so the presentation maps into it.  The four
families of relators are discharged by the four conjugation lemmas of
`RabinVariantTower`, and the source relators by the fact that the source group
sits inside. -/

variable {Γ : Type} [Group Γ] (x : Fin (m + 1) → Γ) (xs : Fin m → Γ)

/-- The witness `z = ⁅w, s⁆`, as an element of the tower. -/
noncomputable def zElt (w : FreeGroup (Fin m)) : Casc2 x :=
  casc2OfMid x (midOfBase
    (RabinVariantTower.baseOf (FreeGroup.lift xs w) * RabinVariantTower.s *
      (RabinVariantTower.baseOf (FreeGroup.lift xs w))⁻¹ * (RabinVariantTower.s)⁻¹))

variable {w : FreeGroup (Fin m)}
  {hz : ∀ p : ℤ, p ≠ 0 → (zElt x xs w) ^ p ≠ 1}

/-- **The witness has infinite order.**  Stage 1 of the tower is an HNN
extension with trivial associated subgroups, where every word in the stable
letter is Britton-reduced, so `HNNTrivialAssociated.commElt_zpow_ne_one`
applies to `⁅w, s⁆` there; and stage 1 embeds in `Casc2` because every layer
above it is an HNN extension over its own base.

This is what removes the last hypothesis of the construction: the tower is
stated for an arbitrary element of infinite order, and the witness is one
exactly when the word is nontrivial in the source group. -/
theorem zElt_infinite (hw : FreeGroup.lift xs w ≠ 1) :
    ∀ p : ℤ, p ≠ 0 → (zElt x xs w) ^ p ≠ 1 := by
  intro p hp h
  have hzz : casc2OfMid x (midOfBase
      ((HNNTrivialAssociated.commElt (FreeGroup.lift xs w)) ^ p)) = 1 := by
    rw [map_zpow, map_zpow]
    exact h
  refine HNNTrivialAssociated.commElt_zpow_ne_one _ hw hp ?_
  refine midOfBase_injective (n := m + 1) ?_
  refine casc2OfMid_injective x ?_
  rw [map_one, map_one]
  exact hzz

/-- Where the generators go in the tower. -/
noncomputable def towerGen : Gen m → Full x hz
  | Sum.inl i => fullOf x hz (casc2OfBase x (xs i))
  | Sum.inr Extra.s =>
      fullOf x hz (casc2OfMid x (midOfBase (RabinVariantTower.s)))
  | Sum.inr (Extra.t i) => fullOf x hz (casc2OfMid x (RabinVariantTower.t i))
  | Sum.inr Extra.u => fullOf x hz (casc2Of x (casc1Of x HNNExtension.t))
  | Sum.inr Extra.b => fullOf x hz (casc2Of x (bLetter x))
  | Sum.inr Extra.c => fullOf x hz (cLetter x)
  | Sum.inr Extra.k => kLetter x hz

/-- The homomorphism the generator map induces on the free group. -/
noncomputable def towerLift : FreeGroup (Gen m) →* Full x hz :=
  FreeGroup.lift (towerGen x xs (hz := hz))

@[simp] theorem towerLift_X (i : Fin m) :
    towerLift x xs (hz := hz) (X i) = fullOf x hz (casc2OfBase x (xs i)) := by
  simp [towerLift, X, towerGen]

@[simp] theorem towerLift_S :
    towerLift x xs (hz := hz) S
      = fullOf x hz (casc2OfMid x (midOfBase (RabinVariantTower.s))) := by
  simp [towerLift, S, towerGen]

@[simp] theorem towerLift_T (i : Fin (m + 1)) :
    towerLift x xs (hz := hz) (T i)
      = fullOf x hz (casc2OfMid x (RabinVariantTower.t i)) := by
  simp [towerLift, T, towerGen]

@[simp] theorem towerLift_U :
    towerLift x xs (hz := hz) U
      = fullOf x hz (casc2Of x (casc1Of x HNNExtension.t)) := by
  simp [towerLift, U, towerGen]

@[simp] theorem towerLift_B :
    towerLift x xs (hz := hz) B = fullOf x hz (casc2Of x (bLetter x)) := by
  simp [towerLift, B, towerGen]

@[simp] theorem towerLift_C :
    towerLift x xs (hz := hz) C = fullOf x hz (cLetter x) := by
  simp [towerLift, C, towerGen]

@[simp] theorem towerLift_K :
    towerLift x xs (hz := hz) K = kLetter x hz := by
  simp [towerLift, K, towerGen]

/-- The source generators, mapped through. -/
theorem towerLift_emb (r : FreeGroup (Fin m)) :
    towerLift x xs (hz := hz) (emb r)
      = (fullOf x hz).comp (casc2OfBase x) (FreeGroup.lift xs r) := by
  have h : (towerLift x xs (hz := hz)).comp (emb : FreeGroup (Fin m) →* _)
      = ((fullOf x hz).comp (casc2OfBase x)).comp (FreeGroup.lift xs) := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    simp [emb, towerLift, towerGen]
  exact DFunLike.congr_fun h r

/-! ## The relators hold in the tower

Each family is one of the tower's conjugation lemmas, pushed up the cascade one
layer at a time. -/

@[simp] theorem casc2OfBase_eq (g : Γ) :
    casc2OfBase x g = casc2OfMid x (midOfBase (RabinVariantTower.baseOf g)) := rfl

/-- The killing relation, pushed to the top. -/
theorem conj_ts_top (i : Fin (m + 1)) :
    fullOf x hz (casc2OfMid x (ts x i))
      = fullOf x hz (casc2Of x (casc1Of x HNNExtension.t)) *
        fullOf x hz (casc2OfMid x (t i)) *
        (fullOf x hz (casc2Of x (casc1Of x HNNExtension.t)))⁻¹ := by
  have h0 := conj_t_eq_ts x i
  have h1 := congrArg (casc1Of x) h0
  rw [map_mul, map_mul, map_inv] at h1
  have h2 := congrArg (casc2Of x) h1
  rw [map_mul, map_mul, map_inv] at h2
  have h3 := congrArg (fullOf x hz) h2
  rw [map_mul, map_mul, map_inv] at h3
  exact h3

/-- The first cascade relation, pushed to the top. -/
theorem casc1_top :
    fullOf x hz (casc2Of x (casc1Of x ((HNNExtension.t : Top Γ x) ^ (2 : ℤ))))
      = fullOf x hz (casc2Of x (bLetter x)) *
        fullOf x hz (casc2Of x (casc1Of x HNNExtension.t)) *
        (fullOf x hz (casc2Of x (bLetter x)))⁻¹ := by
  have h1 := congrArg (casc2Of x) (casc1_conj x)
  rw [map_mul, map_mul, map_inv] at h1
  have h2 := congrArg (fullOf x hz) h1
  rw [map_mul, map_mul, map_inv] at h2
  exact h2

/-- The second cascade relation, pushed to the top. -/
theorem casc2_top :
    fullOf x hz (casc2Of x ((bLetter x) ^ (2 : ℤ)))
      = fullOf x hz (cLetter x) * fullOf x hz (casc2Of x (bLetter x)) *
        (fullOf x hz (cLetter x))⁻¹ := by
  have h1 := congrArg (fullOf x hz) (casc2_conj x)
  rw [map_mul, map_mul, map_inv] at h1
  exact h1

/-! ## Each relator dies -/

/-- The `b`-relator holds. -/
theorem relator_B_dies :
    towerLift x xs (hz := hz) (B * U * B⁻¹ * (U ^ (2 : ℕ))⁻¹) = 1 := by
  have h := casc1_top x xs (hz := hz)
  have hpow : fullOf x hz (casc2Of x (casc1Of x
      ((HNNExtension.t : Top Γ x) ^ (2 : ℤ))))
      = (fullOf x hz (casc2Of x (casc1Of x HNNExtension.t))) ^ (2 : ℕ) := by
    rw [map_zpow, map_zpow, map_zpow, ← zpow_natCast]
    norm_cast
  rw [hpow] at h
  simp only [map_mul, map_inv, map_pow, towerLift_B, towerLift_U]
  rw [← h]
  group

/-- The `c`-relator holds. -/
theorem relator_C_dies :
    towerLift x xs (hz := hz) (C * B * C⁻¹ * (B ^ (2 : ℕ))⁻¹) = 1 := by
  have h := casc2_top x xs (hz := hz)
  have hpow : fullOf x hz (casc2Of x ((bLetter x) ^ (2 : ℤ)))
      = (fullOf x hz (casc2Of x (bLetter x))) ^ (2 : ℕ) := by
    rw [map_zpow, map_zpow, ← zpow_natCast]
    norm_cast
  rw [hpow] at h
  simp only [map_mul, map_inv, map_pow, towerLift_B, towerLift_C]
  rw [← h]
  group

/-- The witness element, expanded.  Proved in `Casc2`, where nothing depends on
the infinite-order hypothesis: the tower's type mentions that hypothesis, which
mentions `zElt`, so `zElt` cannot be rewritten inside a goal of tower type. -/
theorem zElt_eq :
    zElt x xs w
      = casc2OfBase x (FreeGroup.lift xs w) *
        casc2OfMid x (midOfBase RabinVariantTower.s) *
        (casc2OfBase x (FreeGroup.lift xs w))⁻¹ *
        (casc2OfMid x (midOfBase RabinVariantTower.s))⁻¹ := by
  unfold zElt
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, casc2OfBase_eq]
  simp [mul_assoc]

/-- The witness word maps to the witness element.  The last step is `congrArg`
rather than `rw`, for the reason above. -/
theorem towerLift_Z :
    towerLift x xs (hz := hz) (Z w) = fullOf x hz (zElt x xs w) := by
  have hL : towerLift x xs (hz := hz) (Z w)
      = fullOf x hz (casc2OfBase x (FreeGroup.lift xs w) *
          casc2OfMid x (midOfBase RabinVariantTower.s) *
          (casc2OfBase x (FreeGroup.lift xs w))⁻¹ *
          (casc2OfMid x (midOfBase RabinVariantTower.s))⁻¹) := by
    rw [Z, map_mul, map_mul, map_mul, map_inv, map_inv, towerLift_emb,
      towerLift_S, map_mul, map_mul, map_mul, map_inv, map_inv]
    simp [MonoidHom.comp_apply, mul_assoc]
  rw [hL]
  exact congrArg (fullOf x hz) (zElt_eq x xs).symm

/-- The `k`-relator holds: this is where the witness enters. -/
theorem relator_K_dies :
    towerLift x xs (hz := hz) (K * Z w * K⁻¹ * C⁻¹) = 1 := by
  have h := full_conj x hz
  simp only [map_mul, map_inv, towerLift_K, towerLift_Z, towerLift_C]
  rw [← h]
  group

/-! ## The killing family

The one relator family left needs the tower's family `x : Fin (n+1) → Γ` to
line up with the source generators.  Taking it to be `Fin.cases 1 xs` makes
`sWord` match structurally --- `sWord 0 = s` and `sWord j.succ = s xⱼ` are both
`rfl` --- so the index bookkeeping disappears. -/

/-- The family the tower is applied to: `1` at index `0`, the source generators
after it.  Index `0` is what gives the letter `s` itself, which is what makes
the collapse reach `s = 1` and not merely `s xᵢ = 1`. -/
def famOf (xs : Fin m → Γ) : Fin (m + 1) → Γ := Fin.cases 1 xs

@[simp] theorem famOf_zero : famOf xs 0 = 1 := rfl

@[simp] theorem famOf_succ (j : Fin m) : famOf xs j.succ = xs j := rfl

theorem sgen_one : RabinVariantTower.sgen (1 : Γ) = RabinVariantTower.s := by
  simp [RabinVariantTower.sgen]

variable {hz' : ∀ p : ℤ, p ≠ 0 → (zElt (famOf xs) xs w) ^ p ≠ 1}

/-- The word `sᵢ` maps to the tower's `sᵢ`. -/
theorem towerLift_sWord (i : Fin (m + 1)) :
    towerLift (famOf xs) xs (hz := hz') (sWord i)
      = fullOf (famOf xs) hz'
          (casc2OfMid (famOf xs) (midOfBase (RabinVariantTower.sgen (famOf xs i)))) := by
  induction i using Fin.cases with
  | zero => rw [sWord_zero, towerLift_S, famOf_zero, sgen_one]
  | succ j =>
      rw [sWord_succ, map_mul, towerLift_S, towerLift_X, famOf_succ,
        RabinVariantTower.sgen, map_mul, map_mul, map_mul, casc2OfBase_eq]

/-- **The killing relator holds.**  This is the relation that does the work:
`u = 1` turns it into `sᵢ = 1`. -/
theorem relator_kill_dies (i : Fin (m + 1)) :
    towerLift (famOf xs) xs (hz := hz')
        (U * T i * U⁻¹ * (T i * sWord i)⁻¹) = 1 := by
  have h := conj_ts_top (famOf xs) xs (hz := hz') i
  have hts : casc2OfMid (famOf xs) (ts (famOf xs) i)
      = casc2OfMid (famOf xs) (t i) *
        casc2OfMid (famOf xs) (midOfBase (RabinVariantTower.sgen (famOf xs i))) := by
    rw [ts, map_mul]
  rw [hts, map_mul] at h
  simp only [map_mul, map_inv, towerLift_U, towerLift_T, towerLift_sWord]
  rw [← h]
  group

/-! ## The homomorphism into the tower

Every relator dies, so the presentation maps into the tower.  Composed with
`RabinVariantTower.full_base_injective` this is the embedding half for the
*presented* group, which is what the reduction needs. -/

variable {R : Set (FreeGroup (Fin m))}

theorem relators_die (hR : ∀ r ∈ R, FreeGroup.lift xs r = 1) :
    ∀ r ∈ relators R w, towerLift (famOf xs) xs (hz := hz') r = 1 := by
  rintro r ((⟨r₀, hr₀, rfl⟩ | ⟨i, rfl⟩) | (rfl | rfl | rfl))
  · rw [towerLift_emb, hR r₀ hr₀, map_one]
  · exact relator_kill_dies xs i
  · exact relator_B_dies (famOf xs) xs
  · exact relator_C_dies (famOf xs) xs
  · exact relator_K_dies (famOf xs) xs

/-- **The presentation maps into the tower.** -/
noncomputable def toTower (hR : ∀ r ∈ R, FreeGroup.lift xs r = 1) :
    Pres R w →* Full (famOf xs) hz' :=
  PresentedGroup.toGroup (relators_die xs (hz' := hz') hR)

@[simp] theorem toTower_of (hR : ∀ r ∈ R, FreeGroup.lift xs r = 1) (g : Gen m) :
    toTower xs (hz' := hz') hR (PresentedGroup.of g)
      = towerGen (famOf xs) xs (hz := hz') g :=
  PresentedGroup.toGroup.of _

/-! ## The source group embeds in the presented group

Specialising to the source group given by its own presentation. -/

section Source

variable {m : ℕ} (R : Set (FreeGroup (Fin m))) (w : FreeGroup (Fin m))

/-- The source generators, in the source group. -/
noncomputable def srcGens : Fin m → PresentedGroup R := fun i => PresentedGroup.of i

theorem srcGens_relators (r : FreeGroup (Fin m)) (hr : r ∈ R) :
    FreeGroup.lift (srcGens R) r = 1 := by
  have h : (FreeGroup.lift (srcGens R)) = PresentedGroup.mk R := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    simp [srcGens, PresentedGroup.of]
  rw [h]
  exact PresentedGroup.mk_eq_one_iff.2 (Subgroup.subset_normalClosure hr)

/-- The source group, inside the presented group of the construction. -/
noncomputable def srcToPres : PresentedGroup R →* Pres R w :=
  PresentedGroup.toGroup (f := fun i => PresentedGroup.of (Sum.inl i)) (by
    intro r hr
    have h : (FreeGroup.lift fun i => (PresentedGroup.of (Sum.inl i) : Pres R w))
        = (PresentedGroup.mk (relators R w)).comp emb := by
      refine FreeGroup.ext_hom _ _ fun i => ?_
      simp [emb, PresentedGroup.of]
    rw [h, MonoidHom.comp_apply]
    exact PresentedGroup.mk_eq_one_iff.2
      (Subgroup.subset_normalClosure (Or.inl (Or.inl ⟨r, hr, rfl⟩))))

/-- **The embedding half, for the presented group.**  The source group embeds in
the group the construction presents.  Its image under `toTower` is the image of
the source group in the tower, which is injective by
`RabinVariantTower.full_base_injective`. -/
theorem srcToPres_injective
    (hzz : ∀ p : ℤ, p ≠ 0 → (zElt (famOf (srcGens R)) (srcGens R) w) ^ p ≠ 1) :
    Function.Injective (srcToPres R w) := by
  have hcomp : (toTower (srcGens R) (hz' := hzz) (srcGens_relators R)).comp
      (srcToPres R w)
      = (fullOf (famOf (srcGens R)) hzz).comp (casc2OfBase (famOf (srcGens R))) := by
    refine PresentedGroup.ext fun i => ?_
    show toTower (srcGens R) (hz' := hzz) (srcGens_relators R)
      (srcToPres R w (PresentedGroup.of i)) = _
    rw [srcToPres, PresentedGroup.toGroup.of, toTower_of]
    rfl
  intro a b hab
  have h := congrArg (toTower (srcGens R) (hz' := hzz) (srcGens_relators R)) hab
  rw [← MonoidHom.comp_apply, ← MonoidHom.comp_apply, hcomp] at h
  exact full_base_injective (famOf (srcGens R)) hzz h

/-- **The embedding half, with no hypothesis left.**  If the word is nontrivial
in the source group then the source group embeds in the group the construction
presents.  The witness hypothesis is discharged by `zElt_infinite`, so what
remains is exactly the Adian--Rabin condition on `w`. -/
theorem srcToPres_injective_of_ne_one (hw : PresentedGroup.mk R w ≠ 1) :
    Function.Injective (srcToPres R w) := by
  have h : (FreeGroup.lift (srcGens R)) = PresentedGroup.mk R := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    simp [srcGens, PresentedGroup.of]
  refine srcToPres_injective R w (zElt_infinite (famOf (srcGens R)) (srcGens R) ?_)
  rw [h]
  exact hw

end Source

/-! ## The collapse, at the level of the presentation

When `w = 1` in the source group the witness `z` is trivial, the cascade fires,
and everything except the `tᵢ` and `k` dies.  What is left is free, hence
residually finite, hence MF --- which is all the reduction needs on this side,
and the reason the tower's associated subgroups could be taken cyclic.

The retraction below exists for *every* `w`: it sends the `tᵢ` and `k` to a
free basis and everything else to `1`, and each relator dies because every
relator contains a generator outside `{tᵢ, k}` in a position that kills it. -/

/-- The free basis the collapse lands on: one letter per `tᵢ`, and `k`. -/
abbrev FreeGen (m : ℕ) : Type := Fin (m + 1) ⊕ Unit

/-- Where the generators go in the free group. -/
def freeGen : Gen m → FreeGroup (FreeGen m)
  | Sum.inl _ => 1
  | Sum.inr Extra.s => 1
  | Sum.inr (Extra.t i) => FreeGroup.of (Sum.inl i)
  | Sum.inr Extra.u => 1
  | Sum.inr Extra.b => 1
  | Sum.inr Extra.c => 1
  | Sum.inr Extra.k => FreeGroup.of (Sum.inr ())

theorem freeGen_relators (R : Set (FreeGroup (Fin m))) (w : FreeGroup (Fin m)) :
    ∀ r ∈ relators R w, FreeGroup.lift (freeGen (m := m)) r = 1 := by
  have hemb : ∀ r : FreeGroup (Fin m),
      FreeGroup.lift (freeGen (m := m)) (emb r) = 1 := by
    intro r
    have h : (FreeGroup.lift (freeGen (m := m))).comp
        (emb : FreeGroup (Fin m) →* _) = 1 := by
      refine FreeGroup.ext_hom _ _ fun i => ?_
      simp [emb, freeGen]
    exact DFunLike.congr_fun h r
  have hS : FreeGroup.lift (freeGen (m := m)) S = 1 := by simp [S, freeGen]
  have hU : FreeGroup.lift (freeGen (m := m)) U = 1 := by simp [U, freeGen]
  have hB : FreeGroup.lift (freeGen (m := m)) B = 1 := by simp [B, freeGen]
  have hC : FreeGroup.lift (freeGen (m := m)) C = 1 := by simp [C, freeGen]
  have hsw : ∀ i : Fin (m + 1), FreeGroup.lift (freeGen (m := m)) (sWord i) = 1 := by
    intro i
    induction i using Fin.cases with
    | zero => rw [sWord_zero, hS]
    | succ j => rw [sWord_succ, map_mul, hS, X]; simp [freeGen]
  have hZ : FreeGroup.lift (freeGen (m := m)) (Z w) = 1 := by
    rw [Z, map_mul, map_mul, map_mul, map_inv, map_inv, hemb, hS]
    simp
  rintro r ((⟨r₀, -, rfl⟩ | ⟨i, rfl⟩) | (rfl | rfl | rfl))
  · exact hemb r₀
  · rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_mul, hU, hsw]
    simp
  · rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_pow, hB, hU]
    simp
  · rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_pow, hB, hC]
    simp
  · rw [map_mul, map_mul, map_mul, map_inv, map_inv, hZ, hC]
    simp

/-- **The retraction onto the free group.** -/
noncomputable def presRetract (R : Set (FreeGroup (Fin m))) (w : FreeGroup (Fin m)) :
    Pres R w →* FreeGroup (FreeGen m) :=
  PresentedGroup.toGroup (freeGen_relators R w)

/-! ### The relations, inside the presented group -/

variable (R : Set (FreeGroup (Fin m))) (w : FreeGroup (Fin m))

/-- A relator is trivial in the presented group. -/
theorem mk_relator_eq_one {r : FreeGroup (Gen m)} (hr : r ∈ relators R w) :
    (PresentedGroup.mk (relators R w)) r = 1 :=
  PresentedGroup.mk_eq_one_iff.2 (Subgroup.subset_normalClosure hr)

/-- The generators of the presented group. -/
def gS : Pres R w := PresentedGroup.of (Sum.inr Extra.s)
/-- A source generator. -/
def gX (i : Fin m) : Pres R w := PresentedGroup.of (Sum.inl i)
/-- A killing-layer letter. -/
def gT (i : Fin (m + 1)) : Pres R w := PresentedGroup.of (Sum.inr (Extra.t i))
/-- The first cascade letter. -/
def gU : Pres R w := PresentedGroup.of (Sum.inr Extra.u)
/-- The second cascade letter. -/
def gB : Pres R w := PresentedGroup.of (Sum.inr Extra.b)
/-- The third cascade letter. -/
def gC : Pres R w := PresentedGroup.of (Sum.inr Extra.c)
/-- The last cascade letter. -/
def gK : Pres R w := PresentedGroup.of (Sum.inr Extra.k)

/-- The source family, with `1` at index `0`. -/
def gFam : Fin (m + 1) → Pres R w := Fin.cases 1 (gX R w)

@[simp] theorem gFam_zero : gFam R w 0 = 1 := rfl

/-- `b u b⁻¹ = u²`. -/
theorem rel_B : gB R w * gU R w * (gB R w)⁻¹ = (gU R w) ^ (2 : ℕ) := by
  have h := mk_relator_eq_one R w (r := B * U * B⁻¹ * (U ^ (2 : ℕ))⁻¹)
    (Or.inr (by simp))
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_pow] at h
  have := mul_inv_eq_one.1 h
  exact this

/-- `c b c⁻¹ = b²`. -/
theorem rel_C : gC R w * gB R w * (gC R w)⁻¹ = (gB R w) ^ (2 : ℕ) := by
  have h := mk_relator_eq_one R w (r := C * B * C⁻¹ * (B ^ (2 : ℕ))⁻¹)
    (Or.inr (by simp))
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_pow] at h
  exact mul_inv_eq_one.1 h

/-- `k z k⁻¹ = c`. -/
theorem rel_K :
    gK R w * (PresentedGroup.mk (relators R w) (Z w)) * (gK R w)⁻¹ = gC R w := by
  have h := mk_relator_eq_one R w (r := K * Z w * K⁻¹ * C⁻¹) (Or.inr (by simp))
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h
  exact mul_inv_eq_one.1 h

/-- The word `sᵢ`, inside the presented group. -/
theorem mk_sWord (i : Fin (m + 1)) :
    (PresentedGroup.mk (relators R w)) (sWord i) = gS R w * gFam R w i := by
  induction i using Fin.cases with
  | zero => rw [sWord_zero, gFam_zero, mul_one]; rfl
  | succ j => rw [sWord_succ, map_mul]; rfl

/-- `u tᵢ u⁻¹ = tᵢ sᵢ`. -/
theorem rel_kill (i : Fin (m + 1)) :
    gU R w * gT R w i * (gU R w)⁻¹ = gT R w i * (gS R w * gFam R w i) := by
  have h := mk_relator_eq_one R w
    (r := U * T i * U⁻¹ * (T i * sWord i)⁻¹) (Or.inl (Or.inr ⟨i, rfl⟩))
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_mul] at h
  have h2 := mul_inv_eq_one.1 h
  rw [mk_sWord] at h2
  exact h2

/-! ### The collapse fires -/

/-- A source word, inside the presented group, is its image from the source
group. -/
theorem mk_emb (v : FreeGroup (Fin m)) :
    (PresentedGroup.mk (relators R w)) (emb v)
      = srcToPres R w (PresentedGroup.mk R v) := by
  have h : (PresentedGroup.mk (relators R w)).comp (emb : FreeGroup (Fin m) →* _)
      = (srcToPres R w).comp (PresentedGroup.mk R) := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    show (PresentedGroup.mk (relators R w)) (emb (FreeGroup.of i)) = _
    rw [emb, FreeGroup.map.of]
    show PresentedGroup.of (Sum.inl i) = srcToPres R w (PresentedGroup.of i)
    rw [srcToPres, PresentedGroup.toGroup.of]
  exact DFunLike.congr_fun h v

/-- The witness is trivial in the presented group exactly when the word is
trivial in the source group. -/
theorem mk_Z_eq_one (hw : PresentedGroup.mk R w = 1) :
    (PresentedGroup.mk (relators R w)) (Z w) = 1 := by
  rw [Z, map_mul, map_mul, map_mul, map_inv, map_inv, mk_emb, hw, map_one]
  simp

/-- **The collapse.**  If the word is trivial in the source group then the
cascade fires and everything but the `tᵢ` and `k` dies. -/
theorem collapse_pres (hw : PresentedGroup.mk R w = 1) :
    gC R w = 1 ∧ gB R w = 1 ∧ gU R w = 1 ∧ gS R w = 1 ∧
      ∀ i, gFam R w i = 1 :=
  RabinVariantTower.collapse_of_relations (j := 0) (gFam_zero R w)
    (rel_K R w) (rel_C R w) (rel_B R w) (rel_kill R w) (mk_Z_eq_one R w hw)

/-- The surviving generators. -/
def freeBasis : FreeGen m → Pres R w
  | Sum.inl i => gT R w i
  | Sum.inr _ => gK R w

theorem presRetract_freeBasis (g : FreeGen m) :
    presRetract R w (freeBasis R w g) = FreeGroup.of g := by
  cases g with
  | inl i =>
      show presRetract R w (PresentedGroup.of (Sum.inr (Extra.t i))) = _
      rw [presRetract, PresentedGroup.toGroup.of]
      rfl
  | inr u =>
      cases u
      show presRetract R w (PresentedGroup.of (Sum.inr Extra.k)) = _
      rw [presRetract, PresentedGroup.toGroup.of]
      rfl

/-- A presented group is generated by its generators. -/
theorem mem_closure_of (v : FreeGroup (Gen m)) :
    (PresentedGroup.mk (relators R w)) v
      ∈ Subgroup.closure (Set.range (PresentedGroup.of : Gen m → Pres R w)) := by
  have hv : v ∈ Subgroup.closure
      (Set.range (FreeGroup.of : Gen m → FreeGroup (Gen m))) := by
    rw [FreeGroup.closure_range_of]
    trivial
  have himg := Subgroup.mem_map_of_mem (PresentedGroup.mk (relators R w)) hv
  rw [MonoidHom.map_closure] at himg
  refine Subgroup.closure_mono ?_ himg
  rintro _ ⟨y, ⟨i, rfl⟩, rfl⟩
  exact ⟨i, rfl⟩

/-- **The collapse lands on a free group.**  When the word is trivial in the
source, the `tᵢ` and `k` freely generate the presented group. -/
theorem pres_free (hw : PresentedGroup.mk R w = 1) :
    Function.Bijective (FreeGroup.lift (freeBasis R w)) := by
  obtain ⟨hC, hB, hU, hS, hFam⟩ := collapse_pres R w hw
  refine HNNRetraction.freeGroupLift_bijective (presRetract R w) _
    (presRetract_freeBasis R w) fun y => ?_
  obtain ⟨v, rfl⟩ :=
    (QuotientGroup.mk_surjective (s := Subgroup.normalClosure (relators R w))) y
  have hgen : ∀ g : Gen m,
      (PresentedGroup.of g : Pres R w) ∈
        Subgroup.closure (Set.range (freeBasis R w)) := by
    rintro (i | e)
    · have : (PresentedGroup.of (Sum.inl i) : Pres R w) = 1 := by
        have := hFam i.succ
        rwa [gFam, Fin.cases_succ] at this
      rw [this]
      exact one_mem _
    · cases e with
      | s => rw [show (PresentedGroup.of (Sum.inr Extra.s) : Pres R w) = gS R w from rfl,
          hS]; exact one_mem _
      | t i => exact Subgroup.subset_closure ⟨Sum.inl i, rfl⟩
      | u => rw [show (PresentedGroup.of (Sum.inr Extra.u) : Pres R w) = gU R w from rfl,
          hU]; exact one_mem _
      | b => rw [show (PresentedGroup.of (Sum.inr Extra.b) : Pres R w) = gB R w from rfl,
          hB]; exact one_mem _
      | c => rw [show (PresentedGroup.of (Sum.inr Extra.c) : Pres R w) = gC R w from rfl,
          hC]; exact one_mem _
      | k => exact Subgroup.subset_closure ⟨Sum.inr (), rfl⟩
  have hmem := mem_closure_of R w v
  refine (Subgroup.closure_le _).2 ?_ hmem
  rintro _ ⟨g, rfl⟩
  exact hgen g

end RabinVariantPresentation
end GroupApproximation
import GroupApproximation.GGT.DGOProposition435
import GroupApproximation.GGT.DGOLemma421Proof

/-!
# Finitely many auxiliary letters, from Proposition 4.14

Both joint forms of `GGT/DGOProposition435.lean` have a local-finiteness
residue at an original index.  This module confines the auxiliary letters of
the words that realise those relative balls, using
`GGT.OsinComponents.DGOProposition414Uniform`, Dahmani--Guirardel--Osin's
isolated-component bound, together with one combinatorial input about shortest
words.  The confinement is stated once, for an arbitrary joint relative
generating set, and then applied to each form.

## The argument

Let `h` lie in the joint relative ball of radius `n` at an original index
`lam`, and let `w` be a joint word of length at most `n` spelling `h` and
avoiding `Γ_{H_lam}`.  Reading each original peripheral letter as an auxiliary
*base* letter turns `w` into an auxiliary word, and appending the base letter
`h⁻¹` closes it into a cycle, `auxCycle w h`.  Every side of that cycle is a
single edge, so it is a `(1,1)`-quasi-geodesic polygon with `w.length + 1`
sides.

If the auxiliary letters of `w` are maximal isolated components of that cycle,
Proposition 4.14 bounds each of them in the auxiliary relative metric by
`C * (w.length + 1)`, with `C` depending only on the auxiliary relative
generating set.  Local finiteness of the auxiliary family, the second clause of
its hyperbolic embeddedness, then confines every auxiliary letter to a union of
finitely many relative balls.  That union is finite when the auxiliary index
type is, which it is in the filling lane, where it is
`HullSC.AuxiliaryPeripheralIndex k`.

## What each form is then left with

For `jointRelGenSet`, whose base is the proper part of the original base, the
confined letters are finitely many extra base letters, and a finite enlargement
of the base keeps the relative balls finite.  So its local-finiteness residue is
**discharged**: `relBall_inl_finite_of_proposition414Uniform`.

For `jointRelGenSetFull`, whose base is the whole auxiliary base, the confined
letters are again finitely many extra base letters, but the base itself already
exceeds the original one by the whole enlargement of the relative generating
set.  What is left is `DGOProposition435FullOriginalLocalFinitenessStatement`:
the original family alone stays locally finite when its base is enlarged to the
auxiliary base.  That residue mentions neither the auxiliary peripherals nor the
joint index type, so it is strictly smaller than the one it replaces, and it is
the half that in Dahmani--Guirardel--Osin comes from Theorem 4.24 rather than
from Proposition 4.14.

## The remaining combinatorial input

`DGOProposition435IsolatedWitnessStatement` is the maximality and isolation of
the auxiliary components, for *some* word of the same length.  It is the
short-cut argument: two connected auxiliary components of one word can be
replaced by a single auxiliary letter, and adjacent auxiliary letters of the
same index merge, both of which shorten the word without breaking the avoidance
condition, since an auxiliary letter is never an edge of `Γ_{H_lam}`.  A word of
minimal length therefore has no such pair.  It needs no hyperbolic geometry,
only word surgery.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v w

variable {G : Type u} [Group G] {Λ : Type v} {I : Type w}

/-! ## The cycle closed by the original peripheral edge -/

/-- **The auxiliary cycle of a joint word.**  The joint word read in the
auxiliary alphabet, closed by the base letter `h⁻¹`. -/
def auxCycle (w : List (RelLetter G (Sum Λ I))) (h : G) :
    List (RelLetter G I) :=
  w.map RelLetter.auxOfJoint ++ [RelLetter.base h⁻¹]

@[simp] theorem auxCycle_length (w : List (RelLetter G (Sum Λ I))) (h : G) :
    (auxCycle w h).length = w.length + 1 := by
  simp [auxCycle]

theorem listVal_auxCycle (w : List (RelLetter G (Sum Λ I))) {h : G}
    (hval : RelLetter.listVal w = h) :
    RelLetter.listVal (auxCycle w h) = 1 := by
  rw [auxCycle, OsinComponents.listVal_append,
    RelLetter.listVal_map_auxOfJoint, hval]
  show h * (h⁻¹ * 1) = 1
  rw [mul_one, mul_inv_cancel]

theorem getElem_auxCycle_of_lt (w : List (RelLetter G (Sum Λ I))) (h : G)
    {p : ℕ} (hp : p < w.length) (hp' : p < (auxCycle w h).length) :
    (auxCycle w h)[p]'hp' = RelLetter.auxOfJoint (w[p]'hp) := by
  have hmap : p < (w.map RelLetter.auxOfJoint).length := by
    rw [List.length_map]
    exact hp
  show (w.map RelLetter.auxOfJoint ++ [RelLetter.base h⁻¹])[p]'hp' = _
  rw [List.getElem_append_left hmap, List.getElem_map]

/-- A joint letter is an auxiliary letter once the joint base and the original
peripherals are auxiliary base letters. -/
theorem isLetter_auxOfJoint_of_letters (J : RelGenSet G (Sum Λ I))
    (E : RelGenSet G I) (hbase : J.base ⊆ E.base)
    (hinl : ∀ lam : Λ, ((J.fam (Sum.inl lam) : Subgroup G) : Set G) ⊆ E.base)
    (hinr : ∀ i : I, J.fam (Sum.inr i) = E.fam i)
    {a : RelLetter G (Sum Λ I)} (ha : J.IsLetter a) :
    E.IsLetter (RelLetter.auxOfJoint a) := by
  cases a with
  | base _ => exact hbase ha
  | comp s _ =>
      cases s with
      | inl lam => exact hinl lam ha
      | inr j =>
          show _ ∈ E.fam j
          rw [← hinr j]
          exact ha

theorem isLetter_auxCycle (J : RelGenSet G (Sum Λ I)) (E : RelGenSet G I)
    (hJbase : J.base ⊆ E.base)
    (hJinl : ∀ lam : Λ, ((J.fam (Sum.inl lam) : Subgroup G) : Set G) ⊆ E.base)
    (hJinr : ∀ i : I, J.fam (Sum.inr i) = E.fam i)
    {w : List (RelLetter G (Sum Λ I))} (hlet : ∀ a ∈ w, J.IsLetter a) {h : G}
    (hinv : h⁻¹ ∈ E.base) : ∀ a ∈ auxCycle w h, E.IsLetter a := by
  intro a ha
  rw [auxCycle, List.mem_append] at ha
  rcases ha with ha | ha
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact isLetter_auxOfJoint_of_letters J E hJbase hJinl hJinr (hlet b hb)
  · rw [List.eq_of_mem_singleton ha]
    exact hinv

/-! ## The cycle is a quasi-geodesic polygon -/

/-- **Every side of the auxiliary cycle is a single edge**, so the cycle is a
`(1,1)`-quasi-geodesic polygon with one side per letter. -/
theorem isQuasiGeodesicPolygon_auxCycle (E : RelGenSet G I)
    (w : List (RelLetter G (Sum Λ I))) (h : G)
    (hlet : ∀ a ∈ auxCycle w h, E.IsLetter a)
    (hval : RelLetter.listVal (auxCycle w h) = 1) :
    OsinComponents.IsQuasiGeodesicPolygon E 1 1 (w.length + 1) 1
      (auxCycle w h) := by
  refine ⟨hlet, hval, fun s => min s (w.length + 1), by simp, by simp,
    fun s => min_le_min (Nat.le_succ s) le_rfl, ?_⟩
  intro s _ i j hi hij hj
  dsimp only at hi hj
  have hji : j - i ≤ 1 := by omega
  have hcast : ((j - i : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hji
  have hle : ((j - i : ℕ) : ℝ) / 1 - 1 ≤ 0 := by
    rw [div_one]
    linarith
  exact hle.trans (Nat.cast_nonneg _)

/-! ## The combinatorial input -/

/-- **The isolated-witness statement.**

Every element of a joint relative ball is spelled by a joint word of the same
length whose auxiliary letters, read in the auxiliary alphabet, are maximal
isolated components of the cycle closed by the original peripheral edge.  The
joint relative generating set is arbitrary, subject only to restricting to the
two given families and having auxiliary base letters, so the statement serves
every joint form of `GGT/DGOProposition435.lean`.

This is the short-cut argument on a word of minimal length; it uses no
hyperbolic geometry. -/
def DGOProposition435IsolatedWitnessStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type v} {I : Type w}
    (J : RelGenSet G (Sum Lambda I)) (D : RelGenSet G Lambda)
    (E : RelGenSet G I),
      J.base ⊆ E.base →
      (∀ lam : Lambda, J.fam (Sum.inl lam) = D.fam lam) →
      (∀ i : I, J.fam (Sum.inr i) = E.fam i) →
      D.alphabet.carrier ⊆ E.base →
      D.IsHyperbolicallyEmbedded →
      E.IsHyperbolicallyEmbedded →
        ∀ (lam : Lambda) (n : ℕ) (h : G),
          h ∈ J.relBall (Sum.inl lam) n →
            ∃ w : List (RelLetter G (Sum Lambda I)),
              (∀ a ∈ w, J.IsLetter a) ∧
                RelLetter.listVal w = h ∧
                  AvoidsFrom J.fam (Sum.inl lam) w 1 ∧
                    w.length ≤ n ∧
                      ∀ (p : ℕ) (hp : p < w.length) (i : I) (e : G),
                        (w[p]'hp) = RelLetter.comp (Sum.inr i) e →
                          OsinComponents.IsComp i (auxCycle w h) p (p + 1) ∧
                            OsinComponents.IsIsolated E.fam i 1
                              (auxCycle w h) p

/-! ## Proposition 4.14 confines the auxiliary letters -/

/-- **Finitely many auxiliary letters suffice**, from Proposition 4.14 and the
isolated-witness statement.

The constant `C` comes from Proposition 4.14 at `(1,1)`; every auxiliary letter
of an isolated witness is an isolated component of a `(1,1)`-quasi-geodesic
polygon with at most `n + 1` sides, so it lies in the auxiliary relative ball of
radius `C * (n + 1)`.  Those balls are finite, and there are finitely many of
them because the auxiliary index type is finite. -/
theorem exists_finite_auxiliaryLetters_of_proposition414Uniform
    (h414 : OsinComponents.DGOProposition414Uniform.{u, w})
    (hiso : DGOProposition435IsolatedWitnessStatement.{u, v, w})
    [Finite I] (J : RelGenSet G (Sum Λ I)) (D : RelGenSet G Λ)
    (E : RelGenSet G I) (hJbase : J.base ⊆ E.base)
    (hJinl : ∀ lam : Λ, J.fam (Sum.inl lam) = D.fam lam)
    (hJinr : ∀ i : I, J.fam (Sum.inr i) = E.fam i)
    (hbase : D.alphabet.carrier ⊆ E.base)
    (hEsymm : OsinComponents.DGO421BaseSymmetric E)
    (hD : D.IsHyperbolicallyEmbedded) (hE : E.IsHyperbolicallyEmbedded)
    (lam : Λ) (n : ℕ) :
    ∃ F : Set G, F.Finite ∧
      ∀ h ∈ J.relBall (Sum.inl lam) n,
        ∃ w : List (RelLetter G (Sum Λ I)),
          (∀ a ∈ w, J.IsLetter a) ∧
            RelLetter.listVal w = h ∧
              AvoidsFrom J.fam (Sum.inl lam) w 1 ∧
                w.length ≤ n ∧
                  ∀ (i : I) (e : G),
                    RelLetter.comp (Sum.inr i) e ∈ w → e ∈ F := by
  obtain ⟨C, -, -, hball⟩ :=
    h414 G I E hE.hyperbolic hEsymm 1 1 le_rfl zero_le_one
  refine ⟨⋃ i : I, E.relBall i (C * (n + 1)),
    Set.finite_iUnion (fun i => hE.locallyFinite i (C * (n + 1))), ?_⟩
  intro h hh
  obtain ⟨w, hlet, hval, hav, hlen, hcomp⟩ :=
    hiso J D E hJbase hJinl hJinr hbase hD hE lam n h hh
  refine ⟨w, hlet, hval, hav, hlen, ?_⟩
  intro i e hmem
  obtain ⟨p, hp, hpe⟩ := List.mem_iff_getElem.mp hmem
  obtain ⟨hcompP, hisoP⟩ := hcomp p hp i e hpe
  have hhmem : h ∈ D.fam lam := by
    rw [← hJinl lam]
    exact hh.1
  have hinv : h⁻¹ ∈ E.base :=
    hbase (Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨lam, inv_mem hhmem⟩))
  have hJinl' : ∀ mu : Λ, ((J.fam (Sum.inl mu) : Subgroup G) : Set G) ⊆ E.base := by
    intro mu x hx
    refine hbase (Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨mu, ?_⟩))
    rw [← hJinl mu]
    exact hx
  have hpoly := isQuasiGeodesicPolygon_auxCycle E w h
    (isLetter_auxCycle J E hJbase hJinl' hJinr hlet hinv)
    (listVal_auxCycle w hval)
  have hmemball := hball (w.length + 1) 1 (auxCycle w h) hpoly i p (p + 1)
    hcompP hisoP
  have hplen : p < (auxCycle w h).length := by
    rw [auxCycle_length]
    omega
  have hstep : OsinComponents.vertex (1 : G) (auxCycle w h) (p + 1)
      = OsinComponents.vertex (1 : G) (auxCycle w h) p *
        ((auxCycle w h)[p]'hplen).val :=
    OsinComponents.vertex_succ (auxCycle w h) 1 p hplen
  have hvale : ((auxCycle w h)[p]'hplen).val = e := by
    rw [getElem_auxCycle_of_lt w h hp hplen, hpe]
    rfl
  rw [hstep, hvale, inv_mul_cancel_left] at hmemball
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  exact OsinComponents.relBall_mono_radius E i
    (Nat.mul_le_mul le_rfl (by omega)) hmemball

/-! ## Model tests for the combinatorial input -/

/-- **Radius zero.**  The only element of the ball is the identity, spelled by
the empty word, which has no auxiliary letter to isolate. -/
theorem exists_isolatedWitness_zero (J : RelGenSet G (Sum Λ I))
    (E : RelGenSet G I) (lam : Λ) (h : G)
    (hh : h ∈ J.relBall (Sum.inl lam) 0) :
    ∃ w : List (RelLetter G (Sum Λ I)),
      (∀ a ∈ w, J.IsLetter a) ∧
        RelLetter.listVal w = h ∧
          AvoidsFrom J.fam (Sum.inl lam) w 1 ∧
            w.length ≤ 0 ∧
              ∀ (p : ℕ) (hp : p < w.length) (i : I) (e : G),
                (w[p]'hp) = RelLetter.comp (Sum.inr i) e →
                  OsinComponents.IsComp i (auxCycle w h) p (p + 1) ∧
                    OsinComponents.IsIsolated E.fam i 1 (auxCycle w h) p := by
  rw [RelGenSet.relBall_zero, Set.mem_singleton_iff] at hh
  subst hh
  exact ⟨[], by simp, RelLetter.listVal_nil, trivial, by simp,
    fun p hp => absurd hp (by simp)⟩

/-- **No auxiliary subgroups.**  There is no auxiliary letter to isolate, so
any spelling of an element of the ball is an isolated witness. -/
theorem exists_isolatedWitness_of_isEmpty [IsEmpty I] (J : RelGenSet G (Sum Λ I))
    (E : RelGenSet G I) (lam : Λ) (n : ℕ) (h : G)
    (hh : h ∈ J.relBall (Sum.inl lam) n) :
    ∃ w : List (RelLetter G (Sum Λ I)),
      (∀ a ∈ w, J.IsLetter a) ∧
        RelLetter.listVal w = h ∧
          AvoidsFrom J.fam (Sum.inl lam) w 1 ∧
            w.length ≤ n ∧
              ∀ (p : ℕ) (hp : p < w.length) (i : I) (e : G),
                (w[p]'hp) = RelLetter.comp (Sum.inr i) e →
                  OsinComponents.IsComp i (auxCycle w h) p (p + 1) ∧
                    OsinComponents.IsIsolated E.fam i 1 (auxCycle w h) p := by
  obtain ⟨-, w, hlet, hval, hav, hlen⟩ := hh
  exact ⟨w, hlet, hval, hav, hlen, fun _ _ i => isEmptyElim i⟩

/-! ## A finite enlargement of any base -/

/-- `relBall_finite_adjoinBase` with local finiteness in place of hyperbolic
embeddedness, so that it applies to a relative generating set for which only
the residue is known. -/
theorem relBall_finite_adjoinBase' (D : RelGenSet G Λ) (F : Set G)
    (hFinv : ∀ x ∈ F, x⁻¹ ∈ F) (hFfin : F.Finite)
    (hloc : ∀ (mu : Λ) (m : ℕ), (D.relBall mu m).Finite) (lam : Λ) (n : ℕ) :
    ((adjoinBase D F hFinv).relBall lam n).Finite :=
  RelGenSet.localFiniteness_of_finite_base_diff D (adjoinBase D F hFinv) rfl
    (hFfin.subset (by
      rintro x ⟨hx, hxn⟩
      exact hx.resolve_left hxn))
    hloc lam n

/-! ## The residue of the original-base form, discharged -/

/-- **The local-finiteness residue of `jointRelGenSet` follows from
Proposition 4.14 and the isolated-witness statement.**

Confining the auxiliary letters to a finite set turns them into finitely many
extra base letters, and a finite enlargement of the base keeps the relative
balls finite by the local-finiteness half of Corollary 4.27. -/
theorem relBall_inl_finite_of_proposition414Uniform
    (h414 : OsinComponents.DGOProposition414Uniform.{u, w})
    (hiso : DGOProposition435IsolatedWitnessStatement.{u, v, w})
    [Finite I] (D : RelGenSet G Λ) (E : RelGenSet G I)
    (hbase : D.alphabet.carrier ⊆ E.base)
    (hEsymm : OsinComponents.DGO421BaseSymmetric E)
    (hD : D.IsHyperbolicallyEmbedded) (hE : E.IsHyperbolicallyEmbedded)
    (lam : Λ) (n : ℕ) :
    ((jointRelGenSet D E).relBall (Sum.inl lam) n).Finite := by
  obtain ⟨F, hFfin, hwit⟩ :=
    exists_finite_auxiliaryLetters_of_proposition414Uniform h414 hiso
      (jointRelGenSet D E) D E
      (fun _ hx => hbase (Set.mem_union_left _ (properBase_subset_base D hx)))
      (fun _ => rfl) (fun _ => rfl) hbase hEsymm hD hE lam n
  have hUinv : ∀ x ∈ F ∪ F⁻¹, x⁻¹ ∈ F ∪ F⁻¹ := by
    rintro x (hx | hx)
    · exact Or.inr (by simpa using hx)
    · exact Or.inl (by simpa using hx)
  refine (relBall_finite_adjoinBase D (F ∪ F⁻¹) hUinv (hFfin.union hFfin.inv)
    hD lam n).subset ?_
  exact relBall_inl_subset_of_auxLetters _ (adjoinBase D (F ∪ F⁻¹) hUinv)
    (fun _ hx => Or.inl (properBase_subset_base D hx)) (fun _ => rfl) F
    (fun _ hx => Or.inr (Or.inl hx)) lam n hwit

/-- **The original-base form, with only its hyperbolicity residue left.** -/
theorem isHyperbolicallyEmbedded_jointRelGenSet_of_proposition414Uniform
    (h414 : OsinComponents.DGOProposition414Uniform.{u, w})
    (hiso : DGOProposition435IsolatedWitnessStatement.{u, v, w})
    [Finite I] (D : RelGenSet G Λ) (E : RelGenSet G I)
    (hbase : D.alphabet.carrier ⊆ E.base)
    (hEsymm : OsinComponents.DGO421BaseSymmetric E)
    (hD : D.IsHyperbolicallyEmbedded) (hE : E.IsHyperbolicallyEmbedded)
    (hhyp : ∃ delta : ℝ,
      IsHyperbolicSpace delta (Cayley (jointRelGenSet D E).alphabet)) :
    (jointRelGenSet D E).IsHyperbolicallyEmbedded := by
  refine ⟨hhyp, ?_⟩
  rintro (lam | i) n
  · exact relBall_inl_finite_of_proposition414Uniform h414 hiso D E hbase
      hEsymm hD hE lam n
  · exact (hE.locallyFinite i n).subset
      (jointRelGenSet_relBall_inr_subset D E hbase i n)

/-! ## The residue of the auxiliary-alphabet form, reduced -/

/-- **The original family over the auxiliary base.**

The original peripheral family with its base enlarged to the whole auxiliary
base, minus the original peripherals so that the hygiene invariant survives.
Its alphabet is the auxiliary base together with the original peripherals. -/
def originalOverAux (D : RelGenSet G Λ) (E : RelGenSet G I)
    (hbase : D.alphabet.carrier ⊆ E.base)
    (hEinv : ∀ x ∈ E.base, x⁻¹ ∈ E.base) : RelGenSet G Λ where
  base := jointBaseFull D E
  fam := D.fam
  symmetricGenerating := by
    classical
    refine ⟨?_, ?_⟩
    · rintro y (hy | hy)
      · have hyinv : y⁻¹ ∈ E.base := hEinv y hy.1
        by_cases hH : y⁻¹ ∈ (⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G))
        · exact Or.inr hH
        · exact Or.inl ⟨hyinv, hH⟩
      · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hy
        exact Or.inr (Set.mem_iUnion.mpr ⟨lam, (D.fam lam).inv_mem hlam⟩)
    · refine eq_top_iff.mpr ?_
      rw [← D.symmetricGenerating.closure_eq]
      apply Subgroup.closure_mono
      rintro y (hy | hy)
      · by_cases hH : y ∈ (⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G))
        · exact Or.inr hH
        · exact Or.inl ⟨hbase (Set.mem_union_left _ hy), hH⟩
      · exact Or.inr hy

@[simp] theorem originalOverAux_base (D : RelGenSet G Λ) (E : RelGenSet G I)
    (hbase : D.alphabet.carrier ⊆ E.base)
    (hEinv : ∀ x ∈ E.base, x⁻¹ ∈ E.base) :
    (originalOverAux D E hbase hEinv).base = jointBaseFull D E := rfl

@[simp] theorem originalOverAux_fam (D : RelGenSet G Λ) (E : RelGenSet G I)
    (hbase : D.alphabet.carrier ⊆ E.base)
    (hEinv : ∀ x ∈ E.base, x⁻¹ ∈ E.base) :
    (originalOverAux D E hbase hEinv).fam = D.fam := rfl

/-- **The alphabet of the original family over the auxiliary base is that
base.**  Dropping the peripherals from the base and putting them back as
peripheral letters changes nothing. -/
@[simp] theorem originalOverAux_alphabet_carrier (D : RelGenSet G Λ)
    (E : RelGenSet G I) (hbase : D.alphabet.carrier ⊆ E.base)
    (hEinv : ∀ x ∈ E.base, x⁻¹ ∈ E.base) :
    (originalOverAux D E hbase hEinv).alphabet.carrier = E.base := by
  classical
  refine Set.Subset.antisymm ?_ ?_
  · rintro y (hy | hy)
    · exact hy.1
    · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hy
      exact hbase (Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨lam, hlam⟩))
  · intro y hy
    by_cases hH : y ∈ (⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G))
    · exact Or.inr hH
    · exact Or.inl ⟨hy, hH⟩

/-- **Joint hyperbolicity is free over the auxiliary base.**

If the original family is read over the auxiliary base rather than over its own,
the joint alphabet is *literally* the auxiliary alphabet: the base contributes
every auxiliary base letter that is not peripheral, and the peripherals come
back as peripheral letters.  So clause (a) needs no transport and no finiteness
hypothesis, at any distance between the two bases.

The auxiliary family may be taken before its relative generating set was
enlarged, since only its family and base enter.  Its consumers are in
`GGT/DGOProposition435HullBase.lean`. -/
theorem jointHyperbolic_originalOverAux (D : RelGenSet G Λ)
    (E E' : RelGenSet G I) (hfam : E'.fam = E.fam)
    (hbase : D.alphabet.carrier ⊆ E'.base)
    (hEinv : ∀ x ∈ E'.base, x⁻¹ ∈ E'.base)
    (hE' : ∃ delta : ℝ, IsHyperbolicSpace delta (Cayley E'.alphabet)) :
    ∃ delta : ℝ, IsHyperbolicSpace delta
      (Cayley (jointRelGenSet (originalOverAux D E' hbase hEinv) E).alphabet) := by
  have hcarrier :
      (jointRelGenSet (originalOverAux D E' hbase hEinv) E).alphabet.carrier
        = E'.alphabet.carrier := by
    rw [jointRelGenSet_alphabet_carrier, originalOverAux_alphabet_carrier]
    show E'.base ∪ (⋃ i : I, ((E.fam i : Subgroup G) : Set G))
      = E'.base ∪ (⋃ i : I, ((E'.fam i : Subgroup G) : Set G))
    rw [hfam]
  exact exists_isHyperbolicSpace_of_alphabet_eq
    (OsinComponents.alphabet_eq_of_carrier_eq hcarrier) hE'

/-- **The residue of the auxiliary-alphabet form, with the auxiliary family
removed.**

The original peripheral family alone must stay locally finite once its base is
enlarged to the auxiliary base.  Neither the auxiliary peripherals nor the joint
index type occurs, so this is strictly smaller than
`DGOProposition435FullLocalFinitenessStatement`, which it implies together with
Proposition 4.14 and the isolated-witness statement.  It is the half that
Dahmani--Guirardel--Osin get from Theorem 4.24, the isoperimetric
characterisation, and not from Proposition 4.14. -/
def DGOProposition435FullOriginalLocalFinitenessStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type v} {I : Type w}
    (D : RelGenSet G Lambda) (E : RelGenSet G I)
    (hbase : D.alphabet.carrier ⊆ E.base)
    (hEinv : ∀ x ∈ E.base, x⁻¹ ∈ E.base),
      D.IsHyperbolicallyEmbedded →
      E.IsHyperbolicallyEmbedded →
        ∀ (lam : Lambda) (n : ℕ),
          ((originalOverAux D E hbase hEinv).relBall lam n).Finite

/-- **The auxiliary-alphabet residue reduces to the original-family one.** -/
theorem relBall_inl_finite_full_of_proposition414Uniform
    (h414 : OsinComponents.DGOProposition414Uniform.{u, w})
    (hiso : DGOProposition435IsolatedWitnessStatement.{u, v, w})
    (horig : DGOProposition435FullOriginalLocalFinitenessStatement.{u, v, w})
    [Finite I] (D : RelGenSet G Λ) (E : RelGenSet G I)
    (hbase : D.alphabet.carrier ⊆ E.base)
    (hEinv : ∀ x ∈ E.base, x⁻¹ ∈ E.base)
    (hD : D.IsHyperbolicallyEmbedded) (hE : E.IsHyperbolicallyEmbedded)
    (lam : Λ) (n : ℕ) :
    ((jointRelGenSetFull D E).relBall (Sum.inl lam) n).Finite := by
  obtain ⟨F, hFfin, hwit⟩ :=
    exists_finite_auxiliaryLetters_of_proposition414Uniform h414 hiso
      (jointRelGenSetFull D E) D E (jointRelGenSetFull_base_subset D E)
      (fun _ => rfl) (fun _ => rfl) hbase hEinv hD hE lam n
  have hUinv : ∀ x ∈ F ∪ F⁻¹, x⁻¹ ∈ F ∪ F⁻¹ := by
    rintro x (hx | hx)
    · exact Or.inr (by simpa using hx)
    · exact Or.inl (by simpa using hx)
  refine (relBall_finite_adjoinBase' (originalOverAux D E hbase hEinv)
    (F ∪ F⁻¹) hUinv (hFfin.union hFfin.inv)
    (fun mu m => horig D E hbase hEinv hD hE mu m) lam n).subset ?_
  exact relBall_inl_subset_of_auxLetters _
    (adjoinBase (originalOverAux D E hbase hEinv) (F ∪ F⁻¹) hUinv)
    (fun _ hx => Or.inl hx) (fun _ => rfl) F
    (fun _ hx => Or.inr (Or.inl hx)) lam n hwit

/-- **The auxiliary-alphabet form, from Proposition 4.14 and the two smaller
inputs.**  Clause (a) is free in this form, so nothing else is needed. -/
theorem isHyperbolicallyEmbedded_jointRelGenSetFull_of_proposition414Uniform
    (h414 : OsinComponents.DGOProposition414Uniform.{u, w})
    (hiso : DGOProposition435IsolatedWitnessStatement.{u, v, w})
    (horig : DGOProposition435FullOriginalLocalFinitenessStatement.{u, v, w})
    [Finite I] (D : RelGenSet G Λ) (E : RelGenSet G I)
    (hbase : D.alphabet.carrier ⊆ E.base)
    (hEinv : ∀ x ∈ E.base, x⁻¹ ∈ E.base)
    (hD : D.IsHyperbolicallyEmbedded) (hE : E.IsHyperbolicallyEmbedded) :
    (jointRelGenSetFull D E).IsHyperbolicallyEmbedded := by
  refine ⟨jointRelGenSetFull_hyperbolic D E hbase hE, ?_⟩
  rintro (lam | i) n
  · exact relBall_inl_finite_full_of_proposition414Uniform h414 hiso horig D E
      hbase hEinv hD hE lam n
  · exact (hE.locallyFinite i n).subset
      (jointRelGenSetFull_relBall_inr_subset D E hbase i n)

/-! ## Model tests for the reduced residue -/

/-- **No original subgroups.**  The residue is vacuous. -/
theorem originalOverAux_relBall_finite_of_isEmpty [IsEmpty Λ]
    (D : RelGenSet G Λ) (E : RelGenSet G I)
    (hbase : D.alphabet.carrier ⊆ E.base)
    (hEinv : ∀ x ∈ E.base, x⁻¹ ∈ E.base) (lam : Λ) (n : ℕ) :
    ((originalOverAux D E hbase hEinv).relBall lam n).Finite :=
  isEmptyElim lam

/-- **A matched alphabet.**  The enlarged base is then the proper part of the
original base, so the residue is the original family's own local finiteness. -/
theorem originalOverAux_relBall_finite_of_base_eq (D : RelGenSet G Λ)
    (E : RelGenSet G I) (hbase : D.alphabet.carrier ⊆ E.base)
    (hEinv : ∀ x ∈ E.base, x⁻¹ ∈ E.base)
    (heq : E.base = D.alphabet.carrier) (hD : D.IsHyperbolicallyEmbedded)
    (lam : Λ) (n : ℕ) :
    ((originalOverAux D E hbase hEinv).relBall lam n).Finite := by
  have hsub : (originalOverAux D E hbase hEinv).base ⊆ D.base := by
    rw [originalOverAux_base, jointBaseFull_eq_properBase D E heq]
    exact properBase_subset_base D
  refine (hD.locallyFinite lam n).subset ?_
  rintro g ⟨hmem, u, hlet, hval, hav, hlen⟩
  refine ⟨hmem, u, ?_, hval, hav, hlen⟩
  intro a ha
  have hb := hlet a ha
  cases a with
  | base _ => exact hsub hb
  | comp _ _ => exact hb


/-! ## The named endpoints -/

/-- **The auxiliary-alphabet residue, from Proposition 4.14 and the
original-family residue.** -/
theorem dgoProposition435FullLocalFiniteness_of_proposition414Uniform
    (h414 : OsinComponents.DGOProposition414Uniform.{u, w})
    (hiso : DGOProposition435IsolatedWitnessStatement.{u, v, w})
    (horig : DGOProposition435FullOriginalLocalFinitenessStatement.{u, v, w}) :
    DGOProposition435FullLocalFinitenessStatement.{u, v, w} := by
  intro G _ Lambda I _ D E hbase hEinv hD hE lam n
  exact relBall_inl_finite_full_of_proposition414Uniform h414 hiso horig D E
    hbase hEinv hD hE lam n

/-- **The auxiliary-alphabet form of Proposition 4.35's joint direction, from
Proposition 4.14 and the two smaller inputs.**

This is the assembly leaf, reduced: clause (a) is free, clause (b) at an
auxiliary index comes from the auxiliary family itself, and clause (b) at an
original index comes from Proposition 4.14, the isolated-witness statement, and
the local finiteness of the original family over the auxiliary base. -/
theorem dgoProposition435FullStatement_of_proposition414Uniform
    (h414 : OsinComponents.DGOProposition414Uniform.{u, w})
    (hiso : DGOProposition435IsolatedWitnessStatement.{u, v, w})
    (horig : DGOProposition435FullOriginalLocalFinitenessStatement.{u, v, w}) :
    DGOProposition435FullStatement.{u, v, w} :=
  dgoProposition435FullStatement_of_localFiniteness
    (dgoProposition435FullLocalFiniteness_of_proposition414Uniform h414 hiso
      horig)

end RelHyp
end GGT
end GroupApproximation

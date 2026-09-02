import GroupApproximation.GGT.DGOProposition435
import GroupApproximation.GGT.DGOLemma421Proof

/-!
# Finitely many auxiliary letters, from Proposition 4.14

`GGT.RelHyp.DGOProposition435FiniteAuxiliaryLettersStatement` is the residue
that the local finiteness of the joint family was reduced to: for each original
index and radius, finitely many auxiliary letters suffice to spell the whole
joint relative ball.  This module proves it from
`GGT.OsinComponents.DGOProposition414Uniform`, Dahmani--Guirardel--Osin's
isolated-component bound, together with one combinatorial input about shortest
words.

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

## The remaining combinatorial input

`DGOProposition435IsolatedWitnessStatement` is exactly the maximality and
isolation of the auxiliary components, for *some* word of the same length.  It
is the short-cut argument: two connected auxiliary components of one word can
be replaced by a single auxiliary letter, and adjacent auxiliary letters of the
same index merge, both of which shorten the word without breaking the
avoidance condition, since an auxiliary letter is never an edge of
`Γ_{H_lam}`.  A word of minimal length therefore has no such pair.  It needs no
hyperbolic geometry, only word surgery, and it is stated as a separate named
Prop so that the geometric half above does not depend on proving it.
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

theorem isLetter_auxCycle (D : RelGenSet G Λ) (E : RelGenSet G I)
    (hbase : D.alphabet.carrier ⊆ E.base)
    {w : List (RelLetter G (Sum Λ I))}
    (hlet : ∀ a ∈ w, (jointRelGenSet D E).IsLetter a) {h : G}
    (hinv : h⁻¹ ∈ E.base) : ∀ a ∈ auxCycle w h, E.IsLetter a := by
  intro a ha
  rw [auxCycle, List.mem_append] at ha
  rcases ha with ha | ha
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact isLetter_auxOfJoint_of_letters _ E
      (fun _ hx => hbase (Set.mem_union_left _ (properBase_subset_base D hx)))
      (fun lam _ hx =>
        hbase (Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨lam, hx⟩)))
      (fun _ => rfl) (hlet b hb)
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


theorem getElem_auxCycle_of_lt (w : List (RelLetter G (Sum Λ I))) (h : G)
    {p : ℕ} (hp : p < w.length) (hp' : p < (auxCycle w h).length) :
    (auxCycle w h)[p]'hp' = RelLetter.auxOfJoint (w[p]'hp) := by
  have hmap : p < (w.map RelLetter.auxOfJoint).length := by
    rw [List.length_map]
    exact hp
  show (w.map RelLetter.auxOfJoint ++ [RelLetter.base h⁻¹])[p]'hp' = _
  rw [List.getElem_append_left hmap, List.getElem_map]

/-! ## The combinatorial input -/

/-- **The isolated-witness statement.**

Every element of the joint relative ball is spelled by a joint word of the same
length whose auxiliary letters, read in the auxiliary alphabet, are maximal
isolated components of the cycle closed by the original peripheral edge.  This
is the short-cut argument on a word of minimal length; it uses no hyperbolic
geometry. -/
def DGOProposition435IsolatedWitnessStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type v} {I : Type w}
    (D : RelGenSet G Lambda) (E : RelGenSet G I),
      D.alphabet.carrier ⊆ E.base →
      D.IsHyperbolicallyEmbedded →
      E.IsHyperbolicallyEmbedded →
        ∀ (lam : Lambda) (n : ℕ) (h : G),
          h ∈ (jointRelGenSet D E).relBall (Sum.inl lam) n →
            ∃ w : List (RelLetter G (Sum Lambda I)),
              (∀ a ∈ w, (jointRelGenSet D E).IsLetter a) ∧
                RelLetter.listVal w = h ∧
                  AvoidsFrom (jointRelGenSet D E).fam (Sum.inl lam) w 1 ∧
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
    [Finite I] (D : RelGenSet G Λ) (E : RelGenSet G I)
    (hbase : D.alphabet.carrier ⊆ E.base)
    (hEsymm : OsinComponents.DGO421BaseSymmetric E)
    (hD : D.IsHyperbolicallyEmbedded) (hE : E.IsHyperbolicallyEmbedded)
    (lam : Λ) (n : ℕ) :
    ∃ F : Set G, F.Finite ∧
      ∀ h ∈ (jointRelGenSet D E).relBall (Sum.inl lam) n,
        ∃ w : List (RelLetter G (Sum Λ I)),
          (∀ a ∈ w, (jointRelGenSet D E).IsLetter a) ∧
            RelLetter.listVal w = h ∧
              AvoidsFrom (jointRelGenSet D E).fam (Sum.inl lam) w 1 ∧
                w.length ≤ n ∧
                  ∀ (i : I) (e : G),
                    RelLetter.comp (Sum.inr i) e ∈ w → e ∈ F := by
  obtain ⟨C, -, -, hball⟩ :=
    h414 G I E hE.hyperbolic hEsymm 1 1 le_rfl zero_le_one
  refine ⟨⋃ i : I, E.relBall i (C * (n + 1)),
    Set.finite_iUnion (fun i => hE.locallyFinite i (C * (n + 1))), ?_⟩
  intro h hh
  obtain ⟨w, hlet, hval, hav, hlen, hcomp⟩ := hiso D E hbase hD hE lam n h hh
  refine ⟨w, hlet, hval, hav, hlen, ?_⟩
  intro i e hmem
  obtain ⟨p, hp, hpe⟩ := List.mem_iff_getElem.mp hmem
  obtain ⟨hcompP, hisoP⟩ := hcomp p hp i e hpe
  have hhmem : h ∈ D.fam lam := hh.1
  have hinv : h⁻¹ ∈ E.base :=
    hbase (Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨lam, inv_mem hhmem⟩))
  have hpoly := isQuasiGeodesicPolygon_auxCycle E w h
    (isLetter_auxCycle D E hbase hlet hinv) (listVal_auxCycle w hval)
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
theorem exists_isolatedWitness_zero (D : RelGenSet G Λ) (E : RelGenSet G I)
    (lam : Λ) (h : G)
    (hh : h ∈ (jointRelGenSet D E).relBall (Sum.inl lam) 0) :
    ∃ w : List (RelLetter G (Sum Λ I)),
      (∀ a ∈ w, (jointRelGenSet D E).IsLetter a) ∧
        RelLetter.listVal w = h ∧
          AvoidsFrom (jointRelGenSet D E).fam (Sum.inl lam) w 1 ∧
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
theorem exists_isolatedWitness_of_isEmpty [IsEmpty I] (D : RelGenSet G Λ)
    (E : RelGenSet G I) (lam : Λ) (n : ℕ) (h : G)
    (hh : h ∈ (jointRelGenSet D E).relBall (Sum.inl lam) n) :
    ∃ w : List (RelLetter G (Sum Λ I)),
      (∀ a ∈ w, (jointRelGenSet D E).IsLetter a) ∧
        RelLetter.listVal w = h ∧
          AvoidsFrom (jointRelGenSet D E).fam (Sum.inl lam) w 1 ∧
            w.length ≤ n ∧
              ∀ (p : ℕ) (hp : p < w.length) (i : I) (e : G),
                (w[p]'hp) = RelLetter.comp (Sum.inr i) e →
                  OsinComponents.IsComp i (auxCycle w h) p (p + 1) ∧
                    OsinComponents.IsIsolated E.fam i 1 (auxCycle w h) p := by
  obtain ⟨-, w, hlet, hval, hav, hlen⟩ := hh
  exact ⟨w, hlet, hval, hav, hlen, fun _ _ i => isEmptyElim i⟩

/-! ## The local-finiteness residue of the nested form, discharged -/

/-- **The nested form's local-finiteness residue follows from Proposition 4.14
and the isolated-witness statement.**

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
    exists_finite_auxiliaryLetters_of_proposition414Uniform h414 hiso D E hbase
      hEsymm hD hE lam n
  have hUinv : ∀ x ∈ F ∪ F⁻¹, x⁻¹ ∈ F ∪ F⁻¹ := by
    rintro x (hx | hx)
    · exact Or.inr (by simpa using hx)
    · exact Or.inl (by simpa using hx)
  have hUfin : (F ∪ F⁻¹).Finite := hFfin.union hFfin.inv
  refine (relBall_finite_adjoinBase D (F ∪ F⁻¹) hUinv hUfin hD lam n).subset ?_
  exact relBall_inl_subset_of_auxLetters _ (adjoinBase D (F ∪ F⁻¹) hUinv)
    (fun _ hx => Or.inl (properBase_subset_base D hx)) (fun _ => rfl) F
    (fun _ hx => Or.inr (Or.inl hx)) lam n hwit

/-- **The nested form, with only its hyperbolicity residue left.**

Both local-finiteness clauses are now proved: at an auxiliary index from the
auxiliary family itself, and at an original index from Proposition 4.14 and the
isolated-witness statement.  What remains is clause (a) alone, which is free
whenever the two alphabets agree. -/
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

end RelHyp
end GGT
end GroupApproximation

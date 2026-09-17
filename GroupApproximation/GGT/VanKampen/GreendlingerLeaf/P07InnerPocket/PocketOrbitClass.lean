import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketNoncrossingClass
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFillWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, inner pocket: the restricted face permutation and the face class

Lane `gl-p07-04`, first module.  Infrastructure for
`P07LakeExclusion.InnerPocketEnclosedTwoArcStatement` (`P07LakeExclusion/InnerTwoArcLong.lean`),
Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Certifies no printed sentence on its own.

## Notation

`M` is a combinatorial map, `keep` an `alpha`-closed dart predicate, `N = keepMap M keep` the map
on the kept edges (`CombMap.PredicateRestriction.toCombMap`) with face permutation `P`, and
`faceClass M keep c` (lane 05, `PocketNoncrossingClass.lean`) the faces reached from `c` by face
moves and crossings of unkept edges.

## The proofs

1. *First return* (`keepMap_facePerm_firstReturn`).  `P x = σ^m (α x)` for the first `m > 0`
   with `σ^m (α x)` kept: the rotation of `N` is the first return of `σ`.  Hence
   `vertexOf (α x) = vertexOf (P x)`.
2. *`P` stays in the class* (`keepMap_facePerm_mem_faceClass`).  The run
   `x, σ(αx), …, σ^m(αx) = P x` only crosses unkept edges (`faceClass_run`).
3. *The class lies in one face of `N`* (`keepMap_faceOf_eq`), when `M` is planar and `N` is
   connected: two kept darts based in the class are joined by face moves and unkept crossings, so
   `IsRestriction.faceOf_eq_of_faceClass` applies.
4. *The class meets a kept edge* (`exists_keep_mem_faceClass`), when `M` is connected and some
   dart is kept.  Otherwise the class is closed under `α` (an unkept crossing stays in the class,
   and kept darts are never based in it) and under `σ = P ∘ α`, hence it contains every face, in
   particular the face of the kept dart.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u

open Equiv SimpleClosedWalkSides PocketNoncrossing

namespace PocketOrbit

/-- The map on the kept edges. -/
noncomputable abbrev keepMap (M : CombMap.{u}) (keep : M.Dart → Prop)
    (hkeep : ∀ d, keep (M.alpha d) ↔ keep d) : CombMap.{u} :=
  CombMap.PredicateRestriction.toCombMap M keep hkeep

section General

variable {M : CombMap.{u}} {keep : M.Dart → Prop} (hkeep : ∀ d, keep (M.alpha d) ↔ keep d)

/-- **First return on the kept edges.** -/
theorem keepMap_facePerm_firstReturn (x : (keepMap M keep hkeep).Dart) :
    ∃ m, 0 < m ∧ ((keepMap M keep hkeep).facePerm x).1 = (M.sigma ^ m) (M.alpha x.1) ∧
      ∀ k, 0 < k → k < m → ¬ keep ((M.sigma ^ k) (M.alpha x.1)) := by
  obtain ⟨m, hm, hpm, havoid⟩ :=
    (CombMap.PredicateRestriction.isRestriction M keep hkeep).sigma_firstReturn
      ⟨M.alpha x.1, (hkeep x.1).mpr x.2⟩
  exact ⟨m, hm, hpm.symm, fun k hk hkm hk' => havoid k hk hkm ⟨⟨_, hk'⟩, rfl⟩⟩

/-- The restricted face successor starts at the end vertex of a dart. -/
theorem vertexOf_keepMap_facePerm (y : (keepMap M keep hkeep).Dart) :
    M.vertexOf (M.alpha y.1) = M.vertexOf ((keepMap M keep hkeep).facePerm y).1 := by
  obtain ⟨m, _, hpm, _⟩ := keepMap_facePerm_firstReturn hkeep y
  rw [hpm, P07LakeExclusion.LakeFill.lake_vertexOf_sigma_pow]

/-- The restricted face successor is reached by face moves and unkept crossings. -/
theorem keepMap_facePerm_eqvGen (x : (keepMap M keep hkeep).Dart) :
    Relation.EqvGen (CombMap.FaceClassStep M keep) x.1 ((keepMap M keep hkeep).facePerm x).1 := by
  obtain ⟨m, hm, hpm, havoid⟩ := keepMap_facePerm_firstReturn hkeep x
  have hrun := faceClass_run M keep x.1 m havoid m hm le_rfl
  rw [← hpm] at hrun
  exact hrun

/-- **The restricted face successor stays in the class.** -/
theorem keepMap_facePerm_mem_faceClass {c : M.Face} (x : (keepMap M keep hkeep).Dart)
    (hx : M.faceOf x.1 ∈ faceClass M keep c) :
    M.faceOf ((keepMap M keep hkeep).facePerm x).1 ∈ faceClass M keep c := by
  obtain ⟨y, hy, h⟩ := (faceOf_mem_faceClass_iff M keep c x.1).mp hx
  exact (faceOf_mem_faceClass_iff M keep c _).mpr
    ⟨y, hy, Relation.EqvGen.trans _ _ _ h (keepMap_facePerm_eqvGen hkeep x)⟩

theorem keepMap_facePerm_pow_mem_faceClass {c : M.Face} {x₀ : (keepMap M keep hkeep).Dart}
    (hx₀ : M.faceOf x₀.1 ∈ faceClass M keep c) :
    ∀ n : ℕ, M.faceOf (((keepMap M keep hkeep).facePerm ^ n) x₀).1 ∈ faceClass M keep c := by
  intro n
  induction n with
  | zero =>
      rw [pow_zero, Equiv.Perm.one_apply]
      exact hx₀
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact keepMap_facePerm_mem_faceClass hkeep _ ih

/-- **The class lies in one face of the kept map**, for a planar ambient map and a connected
kept map. -/
theorem keepMap_faceOf_eq (hM : M.IsPlanar) (hN : (keepMap M keep hkeep).IsConnected)
    {c : M.Face} {x y : (keepMap M keep hkeep).Dart} (hx : M.faceOf x.1 ∈ faceClass M keep c)
    (hy : M.faceOf y.1 ∈ faceClass M keep c) :
    (keepMap M keep hkeep).faceOf x = (keepMap M keep hkeep).faceOf y := by
  obtain ⟨x', hx', hxr⟩ := (faceOf_mem_faceClass_iff M keep c x.1).mp hx
  obtain ⟨y', hy', hyr⟩ := (faceOf_mem_faceClass_iff M keep c y.1).mp hy
  have h₀ : Relation.EqvGen (CombMap.FaceClassStep M keep) x' y' :=
    eqvGen_faceClass_of_sameCycle M keep ((M.faceOf_eq_iff x' y').mp (hx'.trans hy'.symm))
  have h : Relation.EqvGen (CombMap.FaceClassStep M keep) x.1 y.1 :=
    Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hxr)
      (Relation.EqvGen.trans _ _ _ h₀ hyr)
  have h' : Relation.EqvGen
      (CombMap.FaceClassStep M (· ∈ Set.range (Function.Embedding.subtype keep))) x.1 y.1 :=
    faceClass_mono M (fun z hz => by
      rintro ⟨z', rfl⟩
      exact hz z'.2) h
  exact (CombMap.PredicateRestriction.isRestriction M keep hkeep).faceOf_eq_of_faceClass hM hN
    (d := x) (d' := y) h'

end General

/-- **The class meets a kept edge**, for a connected map with some kept dart. -/
theorem exists_keep_mem_faceClass {M : CombMap.{u}} {keep : M.Dart → Prop}
    (hM : M.IsConnected) {d₀ : M.Dart} (hd₀ : keep d₀) (c : M.Face) :
    ∃ x, keep x ∧ M.faceOf x ∈ faceClass M keep c := by
  by_contra hE
  have halpha : ∀ x, M.faceOf x ∈ faceClass M keep c →
      M.faceOf (M.alpha x) ∈ faceClass M keep c := by
    intro x hx
    by_cases hk : keep x
    · exact (hE ⟨x, hk, hx⟩).elim
    · exact faceOf_alpha_mem_faceClass M keep c hk hx
  have hiff : ∀ x, M.faceOf (M.alpha x) ∈ faceClass M keep c ↔
      M.faceOf x ∈ faceClass M keep c := by
    intro x
    refine ⟨fun h => ?_, halpha x⟩
    have h' := halpha _ h
    rwa [M.alpha_involutive x] at h'
  have hstep : ∀ x y, M.Adjacent x y →
      (M.faceOf x ∈ faceClass M keep c ↔ M.faceOf y ∈ faceClass M keep c) := by
    rintro x y (rfl | rfl)
    · exact (hiff x).symm
    · have hsig : M.sigma x = M.facePerm (M.alpha x) := by
        show M.sigma x = M.sigma (M.alpha (M.alpha x))
        rw [M.alpha_involutive x]
      rw [hsig, M.faceOf_facePerm]
      exact (hiff x).symm
  have hall : ∀ x y, Relation.EqvGen M.Adjacent x y →
      (M.faceOf x ∈ faceClass M keep c ↔ M.faceOf y ∈ faceClass M keep c) := by
    intro x y h
    induction h with
    | rel a b hab => exact hstep a b hab
    | refl _ => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  obtain ⟨x₀, hx₀⟩ := Quotient.exists_rep c
  have hf₀ : M.faceOf x₀ = c := hx₀
  have hc₀ : M.faceOf x₀ ∈ faceClass M keep c :=
    (faceOf_mem_faceClass_iff M keep c x₀).mpr ⟨x₀, hf₀, Relation.EqvGen.refl _⟩
  exact hE ⟨d₀, hd₀, (hall _ _ (hM x₀ d₀)).mp hc₀⟩

end PocketOrbit

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketOrbit.keepMap
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketOrbit.keepMap_facePerm_firstReturn
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketOrbit.vertexOf_keepMap_facePerm
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketOrbit.keepMap_facePerm_eqvGen
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketOrbit.keepMap_facePerm_mem_faceClass
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketOrbit.keepMap_facePerm_pow_mem_faceClass
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketOrbit.keepMap_faceOf_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketOrbit.exists_keep_mem_faceClass

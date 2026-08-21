import GroupApproximation.Kazhdan.SL3Certificate
import GroupApproximation.Algebra.GroupTorsionFree
import GroupApproximation.Algebra.CongruenceTorsionFree
import GroupApproximation.Algebra.FinitePresentationFiniteIndex
import GroupApproximation.Algebra.FreeGroupFiniteRank
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Basic

/-!
# The torsion-free finitely presented Kazhdan partner

The bespoke router of `Sofic/SmallCancellationRouter.lean` routes a source
group and a *partner* group onto a common quotient, and property `(T)` of
that quotient is inherited from the partner alone
(`RoutingLemmaData.kazhdan`).  The partner is irreducibly external to the
router: `C'(1/6)` groups are cubulated, hence a-T-menable, so no infinite
group the router itself produces can be Kazhdan.

`TorsionFreeKazhdanPartner` bundles exactly what the router consumes and
what the endpoint's profile needs from the partner side: a countable,
torsion-free, finitely presented group with property `(T)` in `Type 0`,
the universe the `(T)` development is stated at.

## The candidate

`Γ(3) = ker(SL₃(ℤ) → SL₃(ℤ/3))`, the level-three principal congruence
subgroup.  Every field is proved; nothing is assumed —

* property `(T)` comes from `Kazhdan/SL3Certificate.lean`, which proves it
  for `SL₃(ℤ)` from the exact rational Hodge certificate, carried to `Γ(3)`
  by the finite-index instance below;
* torsion-freeness comes from `Algebra/CongruenceTorsionFree.lean`, which
  proves Minkowski's lemma at level three for the kernel of reduction
  modulo three in any dimension;
* finite presentation comes from `Algebra/SteinbergSL3.lean` (the
  thirteen-relator presentation of `SL₃(ℤ)` is complete) together with the
  in-repo Reidemeister--Schreier descent and the finite-rank lemma of
  `Algebra/FreeGroupFiniteRank.lean`.

So `gamma3Partner` below is a fully certified torsion-free finitely
presented Kazhdan partner, with no open leaves.

## Torsion-freeness conventions

The structure stores `IsPowerTorsionFree` — the ordinary notion, "only the
identity has finite order" — because that is what the routed endpoint
carries.  Mathlib's `IsMulTorsionFree` (injectivity of every power map) is
strictly stronger for nonabelian groups: the Klein bottle group is
torsion-free and satisfies `(ab)² = a²` with `ab ≠ a`.  So the bridge runs
one way only, and `ofIsMulTorsionFree` records it.
-/

namespace GroupApproximation

/-- **What the router needs from the Kazhdan side.**  A countable,
torsion-free, finitely presented group with property `(T)`, in `Type 0`.

Property `(T)` is stored at `HasKazhdanPropertyT.{0, 0}` because that is the
universe instantiation the routing interface and the frozen endpoint both
quantify at; no universe-independence theorem for `(T)` is implicit here. -/
structure TorsionFreeKazhdanPartner where
  /-- The carrier of the partner group. -/
  B : Type
  [group : Group B]
  /-- The partner is countable, so that the corona machinery applies to the
  routed quotient. -/
  [countable : Countable B]
  /-- The partner is torsion-free, in the power form used throughout this
  library. -/
  torsionFree : IsPowerTorsionFree B
  /-- The partner is finitely presented. -/
  [finitelyPresented : Group.IsFinitelyPresented B]
  /-- The partner has Kazhdan's property `(T)`. -/
  kazhdan : HasKazhdanPropertyT.{0, 0} B

namespace TorsionFreeKazhdanPartner

instance instGroup (Part : TorsionFreeKazhdanPartner) : Group Part.B :=
  Part.group

instance instCountable (Part : TorsionFreeKazhdanPartner) : Countable Part.B :=
  Part.countable

instance instFinitelyPresented (Part : TorsionFreeKazhdanPartner) :
    Group.IsFinitelyPresented Part.B :=
  Part.finitelyPresented

/-- **The one-way bridge from Mathlib's torsion-freeness.**  A group with
unique roots is torsion-free in the ordinary sense, so Mathlib's predicate
assembles a partner directly.  The converse direction does not exist and is
not needed: ordinary torsion-freeness does not give unique roots. -/
def ofIsMulTorsionFree (G : Type) [Group G] [Countable G] [IsMulTorsionFree G]
    [Group.IsFinitelyPresented G] (hT : HasKazhdanPropertyT.{0, 0} G) :
    TorsionFreeKazhdanPartner where
  B := G
  torsionFree := IsPowerTorsionFree.of_isMulTorsionFree
  kazhdan := hT

end TorsionFreeKazhdanPartner

/-! ## The level-three principal congruence subgroup -/

namespace CongruenceSubgroup

open Matrix

/-- The special linear group of rank three over the integers. -/
abbrev SL3Z : Type := Matrix.SpecialLinearGroup (Fin 3) ℤ

/-- **`SL₃(ℤ)` is countable.**  A special linear matrix is determined by its
nine integer entries, and `Fin 3 → Fin 3 → ℤ` is countable. -/
instance countable_SL3Z : Countable SL3Z := by
  have hinj : Function.Injective
      (fun A : SL3Z => (fun i j => A i j : Fin 3 → Fin 3 → ℤ)) := by
    intro A B h
    exact Matrix.SpecialLinearGroup.ext A B fun i j =>
      congrFun (congrFun h i) j
  exact hinj.countable

/-- **`SL₃(ℤ/3)` is finite**, for the same reason: nine entries in a finite
ring. -/
instance finite_SL3ZMod3 :
    Finite (Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) := by
  have hinj : Function.Injective
      (fun A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 3) =>
        (fun i j => A i j : Fin 3 → Fin 3 → ZMod 3)) := by
    intro A B h
    exact Matrix.SpecialLinearGroup.ext A B fun i j =>
      congrFun (congrFun h i) j
  exact Finite.of_injective _ hinj

/-- Entrywise reduction of a special linear matrix modulo three. -/
def reduceMod3 : SL3Z →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 3) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 3))

/-- **The level-three principal congruence subgroup** `Γ(3)`: the matrices
congruent to the identity modulo three. -/
def gamma3 : Subgroup SL3Z := reduceMod3.ker

/-- `Γ(3)` is countable, being a subgroup of a countable group. -/
instance countable_gamma3 : Countable ↥gamma3 :=
  inferInstanceAs (Countable { x : SL3Z // x ∈ gamma3 })

/-- **`Γ(3)` has finite index.**  It is the kernel of a homomorphism whose
target is finite, so its range is finite and Mathlib's kernel instance
applies.  This is the input the proved finite-index permanence theorem for
property `(T)` consumes. -/
instance finiteIndex_gamma3 : gamma3.FiniteIndex :=
  Subgroup.finiteIndex_ker reduceMod3

/-- **Property `(T)` for `Γ(3)`.**  Not an open leaf.  `SL₃(ℤ)` is Kazhdan
by the exact rational Hodge certificate of `Kazhdan/SL3Certificate.lean`,
the index of `Γ(3)` is finite by `finiteIndex_gamma3`, and property `(T)`
passes to finite-index subgroups by `Kazhdan/KazhdanFiniteIndex.lean`. -/
theorem gamma3_kazhdan : HasKazhdanPropertyT.{0, 0} ↥gamma3 :=
  SL3Certificate.hasKazhdanPropertyT_of_finiteIndex_in_sl3 gamma3

/-- **`Γ(3)` is torsion-free.**  Not an open leaf: Minkowski's lemma at
level three is proved in `Algebra/CongruenceTorsionFree.lean`, for the
kernel of reduction modulo three in any dimension, and `gamma3` is that
kernel at `Fin 3`.  The proof there is the graded one — an element of the
kernel is `1 + M` with `3 ∣ M`, and prime order forces the divisibility
level of `M` to rise by one indefinitely, so `M = 0`. -/
theorem gamma3_torsionFree :
    IsPowerTorsionFree ↥gamma3 :=
  CongruenceTorsionFree.isPowerTorsionFree_congruenceSubgroupThree

/-- **`Γ(3)` is finitely presented.**  Not an open leaf: finite
presentation of `SL₃(ℤ)` is `SteinbergSL3.isFinitelyPresented_SL3` (the
thirteen-relator presentation is complete, by the P13 descent), and
descent to a finite-index subgroup is the in-repo Reidemeister--Schreier
theorem together with the finite-rank lemma of
`Algebra/FreeGroupFiniteRank.lean`; `gamma3` is definitionally the
level-three congruence kernel that
`FiniteIndex.isFinitelyPresented_congruenceSubgroup` speaks about. -/
theorem gamma3_finitelyPresented :
    Group.IsFinitelyPresented ↥gamma3 :=
  FiniteIndex.isFinitelyPresented_congruenceSubgroup
    FiniteIndex.freeFiniteIndexFinitelyPresented 3

/-- **The canonical partner, fully certified.**  Every field is proved:
the group structure is the subgroup structure, countability is
`countable_gamma3`, property `(T)` is `gamma3_kazhdan` (the certificate),
torsion-freeness is `gamma3_torsionFree` (Minkowski), and finite
presentation is `gamma3_finitelyPresented` (P13 completeness plus
Reidemeister--Schreier).  No assumptions anywhere. -/
def gamma3Partner : TorsionFreeKazhdanPartner where
  B := ↥gamma3
  countable := countable_gamma3
  torsionFree := gamma3_torsionFree
  finitelyPresented := gamma3_finitelyPresented
  kazhdan := gamma3_kazhdan

/-- The partner's carrier is `Γ(3)` on the nose. -/
theorem gamma3Partner_B : gamma3Partner.B = ↥gamma3 := rfl

end CongruenceSubgroup

end GroupApproximation

import GroupApproximation.GGT.HullSCDGO

/-!
# The finite-order clause was not DGO's, and the statement carrying it is false

`Manuscript.NonMF.TheoremCDebts.dgoTheorem53` records DGO's Theorem 5.3 as a
literature debt.  Until issue #50 the conclusion it recorded --
`HullSC.RotatingQuotient` -- carried a clause saying that every element of
finite order of the quotient lifts to an element of `G` of the same order.
`DGOQuotientStatementGeodesicWithLift` below is that statement, and **it is
false**: this module proves it, which is why the clause now lives with the
family Hull builds, as `HullSCFilling.RotatingData.finiteOrder_lift`.

The mechanism also settles a second question, which `GGT/HullSCDGO.lean` had
left open.  Its diagnosis of an earlier defect was that without a geodesic the
very rotating condition constrains an annulus that can be empty, and its repair
was to add `IsGeodesicSpace X`.  That diagnosis was right about the annulus and
incomplete about the cure: a geodesic does not make the annulus non-empty,
*unboundedness* does.  A one-point space is geodesic, and its annulus
`20δ ≤ d(·, c) ≤ 40δ` is empty for every `δ > 0`.  So the model below satisfies
the repaired hypotheses as well as the unrepaired ones.

## The model

`Dot` is the one-point space.  Take any group `G` acting on it -- the action is
forced to be trivial -- any normal `K ≤ G`, and

    δ = 1,   ρ = 200,   C = univ,   Rot = fun _ => K.

Every hypothesis of `DGOQuotientStatementGeodesic` holds:

* `0 < δ` and `200 * δ ≤ ρ`;
* `IsHyperbolicSpace 1 Dot` -- every Gromov product is `0`, so the four-point
  inequality reads `min 0 0 - 1 ≤ 0`;
* `IsGeodesicSpace Dot` -- `dist x y = 0` and the constant map is the geodesic;
* `IsRotatingFamily G Dot univ (fun _ => K)` -- the action is by isometries
  because every distance is `0`, the orbit clause is `univ`, rotations fix their
  apex because there is one point, and equivariance is `h ∈ K ↔ g⁻¹hg ∈ K`,
  which is normality of `K`;
* `IsSeparated univ 200` -- `c ≠ c'` is absurd on a one-point space;
* `IsVeryRotating G Dot 1 univ (fun _ => K)` -- **vacuous**: its first
  hypothesis is `20 * 1 ≤ dist x c = 0`.

And `rotationNormalClosure univ (fun _ => K) = K`, since the normal closure of a
normal subgroup is itself.  So the recorded statement asserts, with no geometry
left in it:

> for every group `G` and every normal `K ≤ G`, every element of finite order of
> `G / K` is the image of an element of `G` of finite order.

`exists_isOfFinOrder_notMem_of_dgoQuotientGeodesicWithLift` is that reading, and
`Multiplicative ℤ` with `K = ⟨(2 : ℤ)⟩` refutes it: `G / K` has order two and
`ℤ` has no element of finite order but `0`.

## Which clause fails, and why it is the expected one

The failing clause is the finite-order lift, and `GGT/HullSCDGO.lean` already
records, from reading Theorem 5.3 against the source, that it is **not one of
that theorem's two conclusions**.  Both conclusions that *are* DGO's hold in the
model above.  The dichotomy: every nonidentity element of `K = Rot c` is
conjugate into `Rot c` by `a = 1`, so
`GGT/DGORotatingQuotientResidual.lean` builds the whole of
`HullSC.RotatingQuotient` here -- **the statement this repository now carries is
not refuted by this model, and that is the point of the repair.**  The free
splitting: `GGT/DGOFreeSplittingOnePoint.lean` proves 5.3(a) holds here too,
which closes the route `GGT/HullSCDGO.lean` proposed to the clause.  So nothing
here touches Dahmani-Guirardel-Osin; what it refutes is the transcription.

The reason no repair by hypothesis-strengthening is in sight: the finite-order
clause is a statement about lifting *elliptic* subgroups, and its proof in this
literature runs through a fixed-point argument in `X / K` together with control
on the **point stabilisers** of the action.  The model has an infinite stabiliser
-- all of `G` fixes the point -- and no hypothesis of the recorded statement
mentions stabilisers.  Asking for finite stabilisers is not available either: at
Hull's own cone-off the stabiliser of an apex is the elementary closure `E(w)`,
which is infinite.

## The repair this forced, and its precedent

The precedent is in this same chain.  `injRadius` and the displacement clause
were fields of `RotatingQuotient` until they were read against the source, and
they now live with the family Hull builds, as
`HullSCFilling.RotatingData.kernel_moves_base`.  The finite-order clause was in
exactly that position and has made the same move, to
`HullSCFilling.RotatingData.finiteOrder_lift`.  What remains of
`RotatingQuotient` is the quotient group, the map, its surjectivity, the kernel
and the dichotomy -- and `G ⧸ K` proves the first four outright, so DGO's
Theorem 5.3(b) is the whole of the citation.

Note that the refutation below uses only `IsOfFinOrder g` and never the
order-preserving equation `orderOf g = orderOf y`, so it is not an artefact of
the strong form of the clause: the weak form goes down with it, and with the
weak form goes any hope of reading torsion-freeness of the quotient off the
rotating hypotheses -- which is why
`HullSC.torsionFree_of_dgoQuotient` now takes the lift as a hypothesis.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry

universe u v

/-! ## The one-point space -/

/-- **The one-point space.**  Written out here rather than taken from `PUnit` so
that the metric and the action below are the only instances it carries. -/
inductive Dot : Type
  /-- Its point. -/
  | pt : Dot

/-- A one-point space has one point. -/
theorem dot_eq (x y : Dot) : x = y := by
  cases x
  cases y
  rfl

/-- The metric on the one-point space: every distance is `0`. -/
noncomputable instance instPseudoMetricSpaceDot : PseudoMetricSpace Dot where
  dist _ _ := 0
  dist_self _ := rfl
  dist_comm _ _ := rfl
  dist_triangle _ _ _ := show (0 : ℝ) ≤ 0 + 0 by rw [add_zero]

@[simp] theorem dist_dot (x y : Dot) : dist x y = 0 := rfl

/-- Every group acts on the one-point space, and only trivially. -/
instance instMulActionDot (G : Type u) [Group G] : MulAction G Dot where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The action is by isometries: every distance is `0`. -/
theorem isIsometricAction_dot (G : Type u) [Group G] : IsIsometricAction G Dot :=
  fun _ _ _ => rfl

/-- Every Gromov product of the one-point space is `0`. -/
theorem gromovProduct_dot (x y w : Dot) : gromovProduct x y w = 0 := by
  have h : gromovProduct x y w = ((0 : ℝ) + 0 - 0) / 2 := rfl
  rw [h]
  norm_num

/-- **The one-point space is hyperbolic**, with any positive constant: the
four-point inequality reads `min 0 0 - δ ≤ 0`. -/
theorem isHyperbolicSpace_dot : IsHyperbolicSpace 1 Dot := by
  intro w x y z
  simp only [gromovProduct_dot, min_self]
  norm_num

/-- **The one-point space is geodesic.**  This is what the repair of
`GGT/HullSCDGO.lean` asks for, and the one-point space has it: the two endpoints
are at distance `0` and the constant map is a geodesic between them.  So the
geodesic hypothesis does not exclude an empty annulus. -/
theorem isGeodesicSpace_dot : IsGeodesicSpace Dot := by
  intro x y
  refine ⟨fun _ => x, ?_, rfl, dot_eq x y⟩
  intro s hs t ht
  rw [dist_dot x y] at hs ht
  have hs0 : s = 0 := le_antisymm hs.2 hs.1
  have ht0 : t = 0 := le_antisymm ht.2 ht.1
  rw [hs0, ht0]
  simp

/-- Separation is vacuous on the one-point space, at any parameter. -/
theorem isSeparated_dot (rho : ℝ) : IsSeparated (Set.univ : Set Dot) rho := by
  intro c _ c' _ hne
  exact absurd (dot_eq c c') hne

/-- **The very rotating condition is vacuous on the one-point space**, for any
family of rotation subgroups: the annulus `20 δ ≤ d(·, c) ≤ 40 δ` about the one
apex is empty, every distance being `0`.

This is the whole mechanism of the refutation, and it survives the geodesic
hypothesis because boundedness, not the absence of geodesics, is what empties the
annulus. -/
theorem isVeryRotating_dot {G : Type u} [Group G] (Rot : Dot → Subgroup G) :
    IsVeryRotating G Dot 1 (Set.univ : Set Dot) Rot := by
  intro _ _ _ _ _ _ _ hx _ _ _ _ _ _ _ _
  rw [dist_dot] at hx
  exact absurd hx (by norm_num)

/-- **A normal subgroup is a rotating family on the one-point space.**  The
fixing clause is free and equivariance is normality. -/
theorem isRotatingFamily_dot {G : Type u} [Group G] {K : Subgroup G}
    (hK : K.Normal) :
    IsRotatingFamily G Dot (Set.univ : Set Dot) (fun _ => K) where
  isometric := fun _ _ _ => rfl
  apex_smul := by
    intro _ _ _
    exact Set.mem_univ _
  rot_fix := by
    intro _ _ _ _
    exact dot_eq _ _
  rot_equivariant := by
    intro g _ _ h
    constructor
    · intro hh
      have hconj := hK.conj_mem h hh g⁻¹
      rw [inv_inv] at hconj
      exact hconj
    · intro hh
      have hconj := hK.conj_mem _ hh g
      have heq : g * (g⁻¹ * h * g) * g⁻¹ = h := by group
      rw [heq] at hconj
      exact hconj

/-- What the rotations of that family generate is the subgroup itself. -/
theorem rotationNormalClosure_dot {G : Type u} [Group G] {K : Subgroup G}
    (hK : K.Normal) :
    rotationNormalClosure (Set.univ : Set Dot) (fun _ => K) = K := by
  haveI := hK
  have hset : {g : G | ∃ c ∈ (Set.univ : Set Dot), g ∈ K} = (K : Set G) := by
    ext g
    constructor
    · rintro ⟨_, -, hg⟩
      exact SetLike.mem_coe.mpr hg
    · intro hg
      show ∃ c ∈ (Set.univ : Set Dot), g ∈ K
      exact ⟨Dot.pt, Set.mem_univ _, SetLike.mem_coe.mp hg⟩
  show Subgroup.normalClosure {g : G | ∃ c ∈ (Set.univ : Set Dot), g ∈ K} = K
  rw [hset]
  exact Subgroup.normalClosure_eq_self K

/-! ## The statement as it was recorded, with the lifting clause in it -/

/-- **DGO's Theorem 5.3 as this repository recorded it before issue #50**: the
quotient, *together with the finite-order lifting clause*, which was a field of
`RotatingQuotient` until this module refuted the statement carrying it.

Written out here rather than left in the structure so that what was removed is
on the record and can be checked against the source.  Everything else about it
is `HullSC.DGOQuotientStatementGeodesic` verbatim, and
`dgoQuotientStatementGeodesic_of_withLift` below is the forgetful implication,
so this is the strictly stronger of the two and the difference is exactly the
clause. -/
def DGOQuotientStatementGeodesicWithLift : Prop :=
  ∀ {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]
    (δ ρ : ℝ) (C : Set X) (Rot : X → Subgroup G),
      0 < δ → 200 * δ ≤ ρ → IsHyperbolicSpace δ X → IsGeodesicSpace X →
        IsRotatingFamily G X C Rot → IsSeparated C ρ →
          IsVeryRotating G X δ C Rot →
            ∃ D : RotatingQuotient C Rot, ∀ y : D.Q, IsOfFinOrder y →
              ∃ g : G, D.q g = y ∧ orderOf g = orderOf y

/-- **Forgetting the clause.**  The recorded statement implies the one the
repository now carries, so the refutation below bears on the clause and on
nothing else. -/
theorem dgoQuotientStatementGeodesic_of_withLift
    (h : DGOQuotientStatementGeodesicWithLift.{u, v}) :
    DGOQuotientStatementGeodesic.{u, v} := by
  intro G _ X _ _ δ ρ C Rot hδ hρ hhyp hgeo hfam hsep hvr
  obtain ⟨D, -⟩ := h δ ρ C Rot hδ hρ hhyp hgeo hfam hsep hvr
  exact ⟨D⟩

/-- **What the recorded statement asserts once the geometry is emptied.**

Fed the one-point space it says: if `a ∉ K` but `a ^ n ∈ K` for some `n > 0` --
that is, if `G / K` has a nonidentity element of finite order -- then `G` has an
element of finite order outside `K`.

No hypothesis of the recorded statement survives the passage to a one-point
space, so nothing constrains the pair `(G, K)`: the geometry has been emptied
without leaving anything behind. -/
theorem exists_isOfFinOrder_notMem_of_dgoQuotientGeodesicWithLift
    (h : DGOQuotientStatementGeodesicWithLift.{0, 0}) {G : Type} [Group G]
    {K : Subgroup G} (hK : K.Normal) {a : G} (ha : a ∉ K) {n : ℕ} (hn : 0 < n)
    (hpow : a ^ n ∈ K) : ∃ g : G, g ∉ K ∧ IsOfFinOrder g := by
  obtain ⟨D, hlift⟩ := h 1 200 (Set.univ : Set Dot) (fun _ : Dot => K)
    (by norm_num) (by norm_num) isHyperbolicSpace_dot isGeodesicSpace_dot
    (isRotatingFamily_dot hK) (isSeparated_dot 200) (isVeryRotating_dot _)
  have hker : D.q.ker = K := by
    rw [D.ker_eq, rotationNormalClosure_dot hK]
  have hy1 : D.q a ≠ 1 := by
    intro hone
    refine ha ?_
    rw [← hker]
    exact MonoidHom.mem_ker.mpr hone
  have hyn : D.q a ^ n = 1 := by
    rw [← map_pow]
    refine MonoidHom.mem_ker.mp ?_
    rw [hker]
    exact hpow
  have hfiny : IsOfFinOrder (D.q a) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hyn⟩
  obtain ⟨g, hqg, horder⟩ := hlift (D.q a) hfiny
  refine ⟨g, ?_, ?_⟩
  · intro hgK
    have hq1 : D.q g = 1 := by
      refine MonoidHom.mem_ker.mp ?_
      rw [hker]
      exact hgK
    rw [hqg] at hq1
    exact hy1 hq1
  · refine orderOf_pos_iff.mp ?_
    rw [horder]
    exact orderOf_pos_iff.mpr hfiny

/-! ## The arithmetic witness -/

/-- `Multiplicative ℤ` is torsion-free. -/
theorem eq_one_of_isOfFinOrder_multiplicative_int {g : Multiplicative ℤ}
    (hg : IsOfFinOrder g) : g = 1 := by
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hg
  have hcong : (g ^ n).toAdd = (1 : Multiplicative ℤ).toAdd := by rw [hpow]
  rw [toAdd_pow, toAdd_one] at hcong
  rw [Int.nsmul_eq_mul] at hcong
  have hn0 : (n : ℤ) ≠ 0 := by omega
  have hzero : g.toAdd = 0 := by
    rcases mul_eq_zero.mp hcong with hcase | hcase
    · exact absurd hcase hn0
    · exact hcase
  exact Multiplicative.toAdd_eq_zero.mp hzero

/-- `1` is not even: the generator is outside the subgroup of index two. -/
theorem ofAdd_one_notMem_zpowers_two :
    Multiplicative.ofAdd (1 : ℤ)
      ∉ Subgroup.zpowers (Multiplicative.ofAdd (2 : ℤ)) := by
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hcong : ((Multiplicative.ofAdd (2 : ℤ)) ^ k).toAdd
      = (Multiplicative.ofAdd (1 : ℤ)).toAdd := by rw [hk]
  rw [toAdd_zpow, Multiplicative.toAdd_ofAdd,
    Multiplicative.toAdd_ofAdd, Int.zsmul_eq_mul] at hcong
  omega

/-- But its square is. -/
theorem ofAdd_one_pow_two_mem_zpowers_two :
    Multiplicative.ofAdd (1 : ℤ) ^ (2 : ℕ)
      ∈ Subgroup.zpowers (Multiplicative.ofAdd (2 : ℤ)) := by
  have hsmul : ((2 : ℕ) • (1 : ℤ)) = (2 : ℤ) := by
    rw [Int.nsmul_eq_mul]
    norm_num
  have hpow : Multiplicative.ofAdd (1 : ℤ) ^ (2 : ℕ)
      = Multiplicative.ofAdd (2 : ℤ) := by
    rw [← ofAdd_nsmul, hsmul]
  rw [hpow]
  exact Subgroup.mem_zpowers _

/-! ## The refutations -/

/-- **The statement with the lifting clause in it is false.**
`Multiplicative ℤ` modulo the powers of `2` has an element of order two, and `ℤ`
has no element of finite order but `0`, so the clause cannot be delivered on the
one-point space -- which is geodesic, hyperbolic, separated, and carries a very
rotating family vacuously.

This is issue #50, and it is why `HullSC.RotatingQuotient` no longer has that
field.  It is a statement about the clause and not about
`HullSC.DGOQuotientStatementGeodesic`, which the same model satisfies:
`GGT/DGORotatingQuotientResidual.lean` builds the quotient for it. -/
theorem not_dgoQuotientStatementGeodesicWithLift :
    ¬ DGOQuotientStatementGeodesicWithLift.{0, 0} := by
  intro h
  obtain ⟨g, hgK, hfin⟩ :=
    exists_isOfFinOrder_notMem_of_dgoQuotientGeodesicWithLift h
      (K := Subgroup.zpowers (Multiplicative.ofAdd (2 : ℤ))) inferInstance
      ofAdd_one_notMem_zpowers_two (n := 2) (by norm_num)
      ofAdd_one_pow_two_mem_zpowers_two
  refine hgK ?_
  rw [eq_one_of_isOfFinOrder_multiplicative_int hfin]
  exact one_mem _

end HullSC
end GroupApproximation

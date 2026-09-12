import GroupApproximation.GGT.KazhdanHypGirthEight

/-!
# Singer-equivariant reduction of girth-eight table checks

A `W(8)` triangle presentation found by the search has `1755` triangles, but
the order-`65` Singer element acts on them with `27` orbits.  This module proves
the finite reduction used to keep the resulting Lean witness small.

`TriangleEquivariant sigma tau T` says that applying `tau` to a triangle index
applies `sigma` to all three generator labels and leaves their signs fixed.
The induced permutation of signed generators preserves the directed and
undirected presentation-link counts.  Consequently it preserves degrees,
two-step counts, and three-step counts.

`CyclicOrbitCover sigma Rep` is explicit proof data saying that every element
is a forward iterate of one stored representative.  The final theorem
`girthEightChecks_of_singer_orbits` consumes three such covers:

* triangle representatives, `27` in the intended witness;
* link-vertex representatives for regularity;
* simultaneous link-vertex-pair representatives for simplicity and the two
  short-cycle tests.

For the intended witness the last two families are discharged from the
algebraic generalized-quadrangle incidence model, rather than enumerated.
Thus the theorem does not make the mathematically false claim that the `27`
triangle rows alone prove the generalized-quadrangle axioms.
-/

namespace GroupApproximation
namespace KazhdanHyp

open scoped BigOperators

set_option linter.unusedSectionVars false

universe u v

section Permutations

/-- The permutation of signed generators induced by a generator permutation;
the positive/inverse bit is unchanged. -/
def signedPerm {Generator : Type} (sigma : Equiv.Perm Generator) :
    Equiv.Perm (Generator × Bool) where
  toFun u := (sigma u.1, u.2)
  invFun u := (sigma.symm u.1, u.2)
  left_inv u := by simp
  right_inv u := by simp

@[simp] theorem signedPerm_apply {Generator : Type}
    (sigma : Equiv.Perm Generator) (u : Generator × Bool) :
    signedPerm sigma u = (sigma u.1, u.2) := rfl

@[simp] theorem signedPerm_symm {Generator : Type}
    (sigma : Equiv.Perm Generator) :
    (signedPerm sigma).symm = signedPerm sigma.symm := rfl

@[simp] theorem signedPerm_inverseSigned {Generator : Type}
    (sigma : Equiv.Perm Generator) (u : Generator × Bool) :
    signedPerm sigma (TriangularHodgeLayer.inverseSigned u) =
      TriangularHodgeLayer.inverseSigned (signedPerm sigma u) := rfl

/-- The simultaneous action on an ordered pair of link vertices. -/
def signedPairPerm {Generator : Type} (sigma : Equiv.Perm Generator) :
    Equiv.Perm ((Generator × Bool) × (Generator × Bool)) :=
  (signedPerm sigma).prodCongr (signedPerm sigma)

@[simp] theorem signedPairPerm_apply {Generator : Type}
    (sigma : Equiv.Perm Generator)
    (p : (Generator × Bool) × (Generator × Bool)) :
    signedPairPerm sigma p = (signedPerm sigma p.1, signedPerm sigma p.2) := rfl

/-- The permutation of triangle corners induced by a permutation of triangle
indices. -/
def cornerPerm {TriangleIndex : Type} (tau : Equiv.Perm TriangleIndex) :
    Equiv.Perm (TriangleIndex × Fin 3) :=
  tau.prodCongr (Equiv.refl (Fin 3))

@[simp] theorem cornerPerm_apply {TriangleIndex : Type}
    (tau : Equiv.Perm TriangleIndex) (p : TriangleIndex × Fin 3) :
    cornerPerm tau p = (tau p.1, p.2) := rfl

end Permutations

section EquivariantTable

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]

/-- One-step equivariance of a triangular table under generator and triangle
permutations.  This is the exact invariance imposed by the Singer search. -/
def TriangleEquivariant (sigma : Equiv.Perm Generator)
    (tau : Equiv.Perm TriangleIndex)
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) : Prop :=
  ∀ j k, T (tau j) k = signedPerm sigma (T j k)

/-- Identity permutations give a nonempty model of table equivariance. -/
theorem triangleEquivariant_identityModel
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) :
    TriangleEquivariant 1 1 T := by
  intro j k
  rfl

theorem TriangleEquivariant.inverse
    {sigma : Equiv.Perm Generator} {tau : Equiv.Perm TriangleIndex}
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
    (hT : TriangleEquivariant sigma tau T) :
    TriangleEquivariant sigma.symm tau.symm T := by
  intro j k
  have h := hT (tau.symm j) k
  have hj : tau (tau.symm j) = j := tau.apply_symm_apply j
  rw [hj] at h
  apply (signedPerm sigma).injective
  rw [h]
  simp

private def directedCornerPredicate
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (u v : Generator × Bool) (p : TriangleIndex × Fin 3) : Prop :=
  T p.1 p.2 = u ∧
    TriangularHodgeLayer.inverseSigned
      (T p.1 (TriangularHodgeLayer.nextCorner p.2)) = v

private theorem directedCornerPredicate_forward
    {sigma : Equiv.Perm Generator} {tau : Equiv.Perm TriangleIndex}
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
    (hT : TriangleEquivariant sigma tau T)
    {u v : Generator × Bool} {p : TriangleIndex × Fin 3}
    (hp : directedCornerPredicate T u v p) :
    directedCornerPredicate T (signedPerm sigma u) (signedPerm sigma v)
      (cornerPerm tau p) := by
  constructor
  · rw [cornerPerm_apply, hT p.1 p.2, hp.1]
  · rw [cornerPerm_apply, hT p.1 (TriangularHodgeLayer.nextCorner p.2),
      ← signedPerm_inverseSigned, hp.2]

private def directedCornerEquiv
    {sigma : Equiv.Perm Generator} {tau : Equiv.Perm TriangleIndex}
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
    (hT : TriangleEquivariant sigma tau T) (u v : Generator × Bool) :
    {p // directedCornerPredicate T u v p} ≃
      {p // directedCornerPredicate T (signedPerm sigma u) (signedPerm sigma v) p} where
  toFun p := ⟨cornerPerm tau p.1, directedCornerPredicate_forward hT p.2⟩
  invFun p := ⟨cornerPerm tau.symm p.1, by
    simpa [signedPerm] using directedCornerPredicate_forward hT.inverse p.2⟩
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext (tau.symm_apply_apply p.1.1) rfl
  right_inv p := by
    apply Subtype.ext
    exact Prod.ext (tau.apply_symm_apply p.1.1) rfl

/-- Directed link-edge multiplicities are Singer invariant. -/
theorem directedAdjacencyCount_signedPerm
    {sigma : Equiv.Perm Generator} {tau : Equiv.Perm TriangleIndex}
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
    (hT : TriangleEquivariant sigma tau T) (u v : Generator × Bool) :
    TriangularHodgeLayer.directedAdjacencyCount T
        (signedPerm sigma u) (signedPerm sigma v) =
      TriangularHodgeLayer.directedAdjacencyCount T u v := by
  classical
  unfold TriangularHodgeLayer.directedAdjacencyCount
  have hcard :
      (Finset.univ.filter fun p => directedCornerPredicate T
        (signedPerm sigma u) (signedPerm sigma v) p).card =
      (Finset.univ.filter fun p => directedCornerPredicate T u v p).card := by
    calc
      (Finset.univ.filter fun p => directedCornerPredicate T
          (signedPerm sigma u) (signedPerm sigma v) p).card =
          Fintype.card {p // directedCornerPredicate T
            (signedPerm sigma u) (signedPerm sigma v) p} :=
        (Fintype.card_subtype _).symm
      _ = Fintype.card {p // directedCornerPredicate T u v p} :=
        Fintype.card_congr (directedCornerEquiv hT u v).symm
      _ = (Finset.univ.filter fun p => directedCornerPredicate T u v p).card :=
        Fintype.card_subtype _
  simpa only [directedCornerPredicate] using hcard

/-- Undirected presentation-link multiplicities are Singer invariant. -/
theorem adjacencyCount_signedPerm
    {sigma : Equiv.Perm Generator} {tau : Equiv.Perm TriangleIndex}
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
    (hT : TriangleEquivariant sigma tau T) (u v : Generator × Bool) :
    TriangularHodgeLayer.adjacencyCount T
        (signedPerm sigma u) (signedPerm sigma v) =
      TriangularHodgeLayer.adjacencyCount T u v := by
  simp only [TriangularHodgeLayer.adjacencyCount]
  rw [directedAdjacencyCount_signedPerm hT,
    directedAdjacencyCount_signedPerm hT]

/-- The two-step count used by the no-four-cycle clause. -/
def linkTwoStep
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (u v : Generator × Bool) : ℕ :=
  ∑ x, TriangularHodgeLayer.adjacencyCount T x u *
    TriangularHodgeLayer.adjacencyCount T x v

/-- The three-step count used by the no-six-cycle clause. -/
def linkThreeStep
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (u v : Generator × Bool) : ℕ :=
  ∑ a, ∑ b, TriangularHodgeLayer.adjacencyCount T u a *
    TriangularHodgeLayer.adjacencyCount T a b *
    TriangularHodgeLayer.adjacencyCount T b v

/-- Link degrees are Singer invariant. -/
theorem degree_signedPerm
    {sigma : Equiv.Perm Generator} {tau : Equiv.Perm TriangleIndex}
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
    (hT : TriangleEquivariant sigma tau T) (u : Generator × Bool) :
    TriangularHodgeLayer.degree T (signedPerm sigma u) =
      TriangularHodgeLayer.degree T u := by
  unfold TriangularHodgeLayer.degree
  calc
    (∑ v, TriangularHodgeLayer.adjacencyCount T (signedPerm sigma u) v) =
        ∑ v, TriangularHodgeLayer.adjacencyCount T
          (signedPerm sigma u) (signedPerm sigma v) :=
      (Equiv.sum_comp (signedPerm sigma)
        (fun v => TriangularHodgeLayer.adjacencyCount T
          (signedPerm sigma u) v)).symm
    _ = ∑ v, TriangularHodgeLayer.adjacencyCount T u v :=
      Finset.sum_congr rfl fun v _ => adjacencyCount_signedPerm hT u v

/-- Two-step counts are Singer invariant. -/
theorem linkTwoStep_signedPerm
    {sigma : Equiv.Perm Generator} {tau : Equiv.Perm TriangleIndex}
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
    (hT : TriangleEquivariant sigma tau T) (u v : Generator × Bool) :
    linkTwoStep T (signedPerm sigma u) (signedPerm sigma v) =
      linkTwoStep T u v := by
  unfold linkTwoStep
  calc
    (∑ x, TriangularHodgeLayer.adjacencyCount T x (signedPerm sigma u) *
        TriangularHodgeLayer.adjacencyCount T x (signedPerm sigma v)) =
      ∑ x, TriangularHodgeLayer.adjacencyCount T (signedPerm sigma x)
          (signedPerm sigma u) *
        TriangularHodgeLayer.adjacencyCount T (signedPerm sigma x)
          (signedPerm sigma v) :=
        (Equiv.sum_comp (signedPerm sigma) _).symm
    _ = ∑ x, TriangularHodgeLayer.adjacencyCount T x u *
        TriangularHodgeLayer.adjacencyCount T x v :=
      Finset.sum_congr rfl fun x _ => by
        rw [adjacencyCount_signedPerm hT, adjacencyCount_signedPerm hT]

/-- Three-step counts are Singer invariant. -/
theorem linkThreeStep_signedPerm
    {sigma : Equiv.Perm Generator} {tau : Equiv.Perm TriangleIndex}
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
    (hT : TriangleEquivariant sigma tau T) (u v : Generator × Bool) :
    linkThreeStep T (signedPerm sigma u) (signedPerm sigma v) =
      linkThreeStep T u v := by
  unfold linkThreeStep
  calc
    (∑ a, ∑ b, TriangularHodgeLayer.adjacencyCount T (signedPerm sigma u) a *
        TriangularHodgeLayer.adjacencyCount T a b *
        TriangularHodgeLayer.adjacencyCount T b (signedPerm sigma v)) =
      ∑ a, ∑ b, TriangularHodgeLayer.adjacencyCount T
          (signedPerm sigma u) (signedPerm sigma a) *
        TriangularHodgeLayer.adjacencyCount T (signedPerm sigma a)
          (signedPerm sigma b) *
        TriangularHodgeLayer.adjacencyCount T (signedPerm sigma b)
          (signedPerm sigma v) := by
      rw [(Equiv.sum_comp (signedPerm sigma) _).symm]
      exact Finset.sum_congr rfl fun a _ =>
        (Equiv.sum_comp (signedPerm sigma) _).symm
    _ = ∑ a, ∑ b, TriangularHodgeLayer.adjacencyCount T u a *
        TriangularHodgeLayer.adjacencyCount T a b *
        TriangularHodgeLayer.adjacencyCount T b v := by
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
        rw [adjacencyCount_signedPerm hT, adjacencyCount_signedPerm hT,
          adjacencyCount_signedPerm hT]

end EquivariantTable

/-! ## Orbit representatives -/

/-- Explicit representative data for the forward orbits of one permutation.
The exponent is stored with each element, so consuming a cover performs no
orbit search in the kernel. -/
structure CyclicOrbitCover {X : Type u} (sigma : Equiv.Perm X) (Rep : Type v) where
  /-- The stored root of each orbit. -/
  root : Rep → X
  /-- The representative chosen for an element. -/
  representative : X → Rep
  /-- The forward exponent from the chosen root. -/
  exponent : X → ℕ
  /-- Every element is the claimed iterate of its root. -/
  covers : ∀ x, (sigma ^[exponent x]) (root (representative x)) = x

namespace CyclicOrbitCover

variable {X : Type u} {Rep : Type v} {sigma : Equiv.Perm X}

private theorem forward_iterate {P : X → Prop}
    (hstep : ∀ x, P x → P (sigma x)) :
    ∀ n x, P x → P ((sigma ^[n]) x) := by
  intro n
  induction n with
  | zero =>
      intro x hx
      exact hx
  | succ n ih =>
      intro x hx
      rw [Function.iterate_succ_apply']
      exact hstep _ (ih x hx)

/-- A predicate stable under the permutation is global once it is checked on
the stored orbit roots. -/
theorem forall_of_representatives (C : CyclicOrbitCover sigma Rep)
    {P : X → Prop} (hstep : ∀ x, P x → P (sigma x))
    (hroot : ∀ r, P (C.root r)) : ∀ x, P x := by
  intro x
  rw [← C.covers x]
  exact forward_iterate hstep (C.exponent x) _ (hroot (C.representative x))

/-- Every type has the identity one-root-per-element cover.  This model shows
that the cover interface has no hidden transitivity requirement. -/
def identityModel (X : Type u) : CyclicOrbitCover (1 : Equiv.Perm X) X where
  root := id
  representative := id
  exponent := fun _ => 0
  covers := by intro x; rfl

end CyclicOrbitCover

section Assembly

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]

/-- **Kernel-small Singer reduction for `GirthEightChecks`.**

The hypotheses after the three orbit covers are evaluated only on the stored
roots.  The preceding equivariance theorems transport the five clauses to the
full table. -/
theorem girthEightChecks_of_singer_orbits
    {TriangleRep VertexRep PairRep : Type}
    (sigma : Equiv.Perm Generator) (tau : Equiv.Perm TriangleIndex)
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (d : ℕ)
    (hT : TriangleEquivariant sigma tau T)
    (triangleCover : CyclicOrbitCover tau TriangleRep)
    (vertexCover : CyclicOrbitCover (signedPerm sigma) VertexRep)
    (pairCover : CyclicOrbitCover (signedPairPerm sigma) PairRep)
    (hpositive : ∀ r k, (T (triangleCover.root r) k).2 = true)
    (hregular : ∀ r, TriangularHodgeLayer.degree T (vertexCover.root r) = d)
    (hsimple : ∀ r, let p := pairCover.root r
      TriangularHodgeLayer.adjacencyCount T p.1 p.2 ≤ 1)
    (hfour : ∀ r, let p := pairCover.root r
      p.1 ≠ p.2 → linkTwoStep T p.1 p.2 ≤ 1)
    (hsix : ∀ r, let p := pairCover.root r
      TriangularHodgeLayer.adjacencyCount T p.1 p.2 = 0 →
        linkThreeStep T p.1 p.2 ≤ 1) :
    GirthEightChecks T d := by
  have hposAll : ∀ j, ∀ k, (T j k).2 = true :=
    triangleCover.forall_of_representatives (P := fun j => ∀ k, (T j k).2 = true)
      (by
        intro j hj k
        rw [hT j k]
        exact hj k)
      hpositive
  have hregAll : ∀ u, TriangularHodgeLayer.degree T u = d :=
    vertexCover.forall_of_representatives
      (P := fun u => TriangularHodgeLayer.degree T u = d)
      (by
        intro u hu
        rw [degree_signedPerm hT]
        exact hu)
      hregular
  have hsimpleAll : ∀ p : (Generator × Bool) × (Generator × Bool),
      TriangularHodgeLayer.adjacencyCount T p.1 p.2 ≤ 1 :=
    pairCover.forall_of_representatives
      (P := fun p => TriangularHodgeLayer.adjacencyCount T p.1 p.2 ≤ 1)
      (by
        intro p hp
        change TriangularHodgeLayer.adjacencyCount T
          (signedPerm sigma p.1) (signedPerm sigma p.2) ≤ 1
        rw [adjacencyCount_signedPerm hT]
        exact hp)
      hsimple
  have hfourAll : ∀ p : (Generator × Bool) × (Generator × Bool),
      p.1 ≠ p.2 → linkTwoStep T p.1 p.2 ≤ 1 :=
    pairCover.forall_of_representatives
      (P := fun p => p.1 ≠ p.2 → linkTwoStep T p.1 p.2 ≤ 1)
      (by
        intro p hp hne
        simp only [signedPairPerm_apply] at hne ⊢
        have hne' : p.1 ≠ p.2 := fun h => hne (congrArg (signedPerm sigma) h)
        rw [linkTwoStep_signedPerm hT]
        exact hp hne')
      hfour
  have hsixAll : ∀ p : (Generator × Bool) × (Generator × Bool),
      TriangularHodgeLayer.adjacencyCount T p.1 p.2 = 0 →
        linkThreeStep T p.1 p.2 ≤ 1 :=
    pairCover.forall_of_representatives
      (P := fun p => TriangularHodgeLayer.adjacencyCount T p.1 p.2 = 0 →
        linkThreeStep T p.1 p.2 ≤ 1)
      (by
        intro p hp hzero
        simp only [signedPairPerm_apply] at hzero ⊢
        have hzero' : TriangularHodgeLayer.adjacencyCount T p.1 p.2 = 0 := by
          rw [← adjacencyCount_signedPerm hT]
          exact hzero
        rw [linkThreeStep_signedPerm hT]
        exact hp hzero')
      hsix
  refine ⟨hposAll, hregAll, ?_, ?_, ?_⟩
  · intro u v
    exact hsimpleAll (u, v)
  · intro u v hne
    exact hfourAll (u, v) hne
  · intro u v hzero
    exact hsixAll (u, v) hzero

end Assembly
end KazhdanHyp
end GroupApproximation

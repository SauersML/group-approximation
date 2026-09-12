import GroupApproximation.GGT.VanKampen.CactusMap
import Mathlib.Tactic.Ring

/-!
# Orbit counts for the polygon cactus

This file identifies the vertex and face orbits of the explicit cactus
rotation system.  Vertices are the vertices of the outer polygon together
with the vertices of every relator polygon.  Faces are the outer polygon,
one face for each relator polygon, and the complementary face.  These
identifications give the Euler count used by the cactus realization.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

open Equiv

namespace OrbitClassifier

/-- A classifier invariant under one permutation step is constant on every
permutation orbit. -/
theorem eq_of_sameCycle {D I : Type*} [Finite D]
    (p : Perm D) (classify : D → I)
    (hinvariant : ∀ d, classify (p d) = classify d)
    {d e : D} (hde : p.SameCycle d e) : classify d = classify e := by
  obtain ⟨n, hn⟩ := hde.exists_nat_pow_eq
  have hpow : ∀ (m : ℕ) (x : D),
      classify ((p ^ m) x) = classify x := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
        intro x
        rw [pow_succ, Perm.mul_apply]
        exact (ih (p x)).trans (hinvariant x)
  calc
    classify d = classify ((p ^ n) d) := (hpow n d).symm
    _ = classify e := congrArg classify hn

/-- A complete orbit classifier gives an equivalence from the orbit quotient
to its finite index type. -/
noncomputable def orbitEquiv {D I : Type*} [Finite D]
    (p : Perm D) (classify : D → I) (representative : I → D)
    (hinvariant : ∀ d, classify (p d) = classify d)
    (hrepresentative : ∀ i, classify (representative i) = i)
    (hcomplete : ∀ d, p.SameCycle (representative (classify d)) d) :
    CombMap.Orbit p ≃ I where
  toFun := Quotient.lift classify fun _ _ h ↦
    eq_of_sameCycle p classify hinvariant h
  invFun i := Quotient.mk'' (representative i)
  left_inv q := by
    refine Quotient.inductionOn' q ?_
    intro d
    apply Quotient.sound
    exact hcomplete d
  right_inv i := hrepresentative i

/-- An intertwining map sends same-cycle pairs to same-cycle pairs. -/
theorem sameCycle_map {I D : Type*} [Finite I]
    (q : Perm I) (p : Perm D) (f : I → D)
    (happly : ∀ i, p (f i) = f (q i))
    {i j : I} (hij : q.SameCycle i j) : p.SameCycle (f i) (f j) := by
  obtain ⟨n, hn⟩ := hij.exists_nat_pow_eq
  have hpow : ∀ (m : ℕ) (x : I),
      p.SameCycle (f x) (f ((q ^ m) x)) := by
    intro m
    induction m with
    | zero => intro x; exact Equiv.Perm.SameCycle.rfl
    | succ m ih =>
        intro x
        rw [pow_succ, Perm.mul_apply]
        have hstep : p.SameCycle (f x) (f (q x)) := by
          refine ⟨1, ?_⟩
          simpa using happly x
        exact hstep.trans (ih (q x))
  have h := hpow n i
  rw [hn] at h
  exact h

end OrbitClassifier

namespace CactusShape

/-- Every two indices of a positive cyclic polygon lie in the same rotation
orbit. -/
theorem finRotate_sameCycle {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    (finRotate n).SameCycle i j := by
  by_cases hone : n = 1
  · have hij : i = j := by
      subst n
      exact Subsingleton.elim _ _
    exact hij.sameCycle (finRotate n)
  · have htwo : 2 ≤ n := by omega
    apply (isCycle_finRotate_of_le htwo).sameCycle
    · rw [← Equiv.Perm.mem_support, support_finRotate_of_le htwo]
      exact Finset.mem_univ i
    · rw [← Equiv.Perm.mem_support, support_finRotate_of_le htwo]
      exact Finset.mem_univ j

/-- Vertex indices of the cactus: outer vertices followed by all relator
polygon vertices. -/
abbrev VertexIndex (S : CactusShape) :=
  Fin S.boundaryLength ⊕ Σ i : Fin S.cellCount, Fin (S.relatorLength i)

/-- The polygon vertex incident to a dart. -/
def vertexClass (S : CactusShape) : CactusDart S → S.VertexIndex
  | .outerForward j => Sum.inl j
  | .outerBackward j => Sum.inl (nextFin S.boundaryLength j)
  | .relatorForward i j => Sum.inr ⟨i, j⟩
  | .relatorBackward i j =>
      Sum.inr ⟨i, nextFin (S.relatorLength i) j⟩
  | .stemOut _ => Sum.inl S.boundaryZero
  | .stemIn i => Sum.inr ⟨i, S.relatorZero i⟩

/-- A canonical forward dart at each cactus vertex. -/
def vertexRepresentative (S : CactusShape) : S.VertexIndex → CactusDart S
  | Sum.inl j => .outerForward j
  | Sum.inr ⟨i, j⟩ => .relatorForward i j

theorem vertexClass_representative (S : CactusShape) (v : S.VertexIndex) :
    S.vertexClass (S.vertexRepresentative v) = v := by
  cases v with
  | inl j => rfl
  | inr q => cases q; rfl

/-- Vertex rotation preserves the explicit vertex classifier. -/
theorem vertexClass_sigma (S : CactusShape) (d : CactusDart S) :
    S.vertexClass (S.sigma d) = S.vertexClass d := by
  cases d with
  | outerForward j =>
      by_cases hj : j = S.boundaryZero
      · subst j
        by_cases hn : 0 < S.cellCount
        · simp [sigma, sigmaFun, vertexClass, hn]
        · simp [sigma, sigmaFun, vertexClass, hn, nextFin_prevFin]
      · simp [sigma, sigmaFun, vertexClass, hj, nextFin_prevFin]
  | outerBackward j => rfl
  | relatorForward i j =>
      by_cases hj : j = S.relatorZero i
      · subst j
        simp [sigma, sigmaFun, vertexClass]
      · simp [sigma, sigmaFun, vertexClass, hj, nextFin_prevFin]
  | relatorBackward i j => rfl
  | stemOut i =>
      let hpos : 0 < S.cellCount := Nat.zero_lt_of_lt i.isLt
      by_cases hi : nextFin S.cellCount i = S.cellZero hpos
      · simp [sigma, sigmaFun, vertexClass, hi, nextFin_prevFin]
      · simp [sigma, sigmaFun, vertexClass, hi]
  | stemIn i =>
      simp [sigma, sigmaFun, vertexClass, nextFin_prevFin]

/-- A single permutation step gives a same-cycle pair. -/
theorem sameCycle_apply (p : Perm α) (d : α) : p.SameCycle d (p d) :=
  ⟨1, by simp⟩

/-- Before the final stem, repeated vertex rotation visits all outgoing
stems in increasing index order. -/
theorem stemOut_sameCycle (S : CactusShape) (hpos : 0 < S.cellCount)
    (i : Fin S.cellCount) :
    S.sigma.SameCycle (.stemOut (S.cellZero hpos)) (.stemOut i) := by
  obtain ⟨k, hk⟩ := i
  induction k with
  | zero =>
      have heq : (⟨0, hk⟩ : Fin S.cellCount) = S.cellZero hpos := by
        apply Fin.ext
        rfl
      rw [heq]
  | succ k ih =>
      have hk' : k < S.cellCount := lt_trans (Nat.lt_succ_self k) hk
      have hprevious := ih hk'
      let previous : Fin S.cellCount := ⟨k, hk'⟩
      let current : Fin S.cellCount := ⟨k + 1, hk⟩
      haveI : NeZero S.cellCount := ⟨Nat.ne_of_gt hpos⟩
      have hnext : nextFin S.cellCount previous = current := by
        apply Fin.ext
        simp [nextFin, previous, current, finRotate_apply,
          Fin.add_def, Nat.mod_eq_of_lt hk]
      have hnot : nextFin S.cellCount previous ≠
          S.cellZero (Nat.zero_lt_of_lt previous.isLt) := by
        rw [hnext]
        intro hzero
        have hval := congrArg Fin.val hzero
        simp [current, cellZero] at hval
      have hsigma : S.sigma (.stemOut previous) = .stemOut current := by
        change (if _h : nextFin S.cellCount previous =
            S.cellZero (Nat.zero_lt_of_lt previous.isLt) then
              CactusDart.outerBackward
                (prevFin S.boundaryLength S.boundaryZero)
            else CactusDart.stemOut (nextFin S.cellCount previous)) =
          CactusDart.stemOut current
        rw [dif_neg hnot, hnext]
      have hstep : S.sigma.SameCycle (.stemOut previous) (.stemOut current) := by
        simpa [hsigma] using sameCycle_apply S.sigma (.stemOut previous)
      exact hprevious.trans hstep

/-- Every dart is in the vertex cycle of its canonical forward dart. -/
theorem vertexRepresentative_sameCycle (S : CactusShape) (d : CactusDart S) :
    S.sigma.SameCycle (S.vertexRepresentative (S.vertexClass d)) d := by
  cases d with
  | outerForward j => exact Equiv.Perm.SameCycle.rfl
  | outerBackward j =>
      exact (sameCycle_apply S.sigma (.outerBackward j)).symm
  | relatorForward i j => exact Equiv.Perm.SameCycle.rfl
  | relatorBackward i j =>
      exact (sameCycle_apply S.sigma (.relatorBackward i j)).symm
  | stemIn i =>
      have h₁ := sameCycle_apply S.sigma (.stemIn i)
      have h₂ := sameCycle_apply S.sigma
        (.relatorBackward i (prevFin (S.relatorLength i) (S.relatorZero i)))
      have htarget : S.sigma
          (.relatorBackward i (prevFin (S.relatorLength i) (S.relatorZero i))) =
          .relatorForward i (S.relatorZero i) := by
        simp [sigma, sigmaFun, nextFin_prevFin]
      rw [htarget] at h₂
      exact (h₁.trans h₂).symm
  | stemOut i =>
      let hpos : 0 < S.cellCount := Nat.zero_lt_of_lt i.isLt
      have hstart : S.sigma.SameCycle
          (.outerForward S.boundaryZero)
          (.stemOut (S.cellZero hpos)) := by
        have hsigma : S.sigma (.outerForward S.boundaryZero) =
            .stemOut (S.cellZero hpos) := by
          simp [sigma, sigmaFun, hpos]
        rw [← hsigma]
        exact sameCycle_apply S.sigma (.outerForward S.boundaryZero)
      have hall : S.sigma.SameCycle
          (.stemOut (S.cellZero hpos)) (.stemOut i) := by
        exact S.stemOut_sameCycle hpos i
      exact hstart.trans hall

/-- Vertex orbits are exactly the explicit polygon vertices. -/
noncomputable def vertexEquiv (S : CactusShape) :
    S.toCombMap.Vertex ≃ S.VertexIndex :=
  OrbitClassifier.orbitEquiv S.sigma S.vertexClass S.vertexRepresentative
    S.vertexClass_sigma S.vertexClass_representative
    S.vertexRepresentative_sameCycle

/-- The cactus has the sum of the polygon vertex counts. -/
theorem vertexCount_eq (S : CactusShape) :
    S.toCombMap.vertexCount =
      S.boundaryLength + ∑ i : Fin S.cellCount, S.relatorLength i := by
  rw [CombMap.vertexCount, Nat.card_congr S.vertexEquiv]
  simp [VertexIndex]

/-! ## Edge orbits -/

/-- Edge indices of the cactus: outer polygon edges, relator polygon edges,
and stems. -/
abbrev EdgeIndex (S : CactusShape) :=
  (Fin S.boundaryLength ⊕
    Σ i : Fin S.cellCount, Fin (S.relatorLength i)) ⊕
      Fin S.cellCount

/-- The unoriented edge containing a cactus dart. -/
def edgeClass (S : CactusShape) : CactusDart S → S.EdgeIndex
  | .outerForward j => Sum.inl (Sum.inl j)
  | .outerBackward j => Sum.inl (Sum.inl j)
  | .relatorForward i j => Sum.inl (Sum.inr ⟨i, j⟩)
  | .relatorBackward i j => Sum.inl (Sum.inr ⟨i, j⟩)
  | .stemOut i => Sum.inr i
  | .stemIn i => Sum.inr i

/-- A canonical orientation of every cactus edge. -/
def edgeRepresentative (S : CactusShape) : S.EdgeIndex → CactusDart S
  | Sum.inl (Sum.inl j) => .outerForward j
  | Sum.inl (Sum.inr ⟨i, j⟩) => .relatorForward i j
  | Sum.inr i => .stemOut i

theorem edgeClass_representative (S : CactusShape) (e : S.EdgeIndex) :
    S.edgeClass (S.edgeRepresentative e) = e := by
  rcases e with (e | i)
  · rcases e with (j | q)
    · rfl
    · rcases q with ⟨i, j⟩
      rfl
  · rfl

/-- Edge reversal preserves the explicit edge classifier. -/
theorem edgeClass_alpha (S : CactusShape) (d : CactusDart S) :
    S.edgeClass (S.alpha d) = S.edgeClass d := by
  cases d <;> rfl

/-- The canonical representative and a dart with the same edge index are
equal or reverses. -/
theorem edgeRepresentative_related (S : CactusShape) (d : CactusDart S) :
    DartPairRel S.alpha (S.edgeRepresentative (S.edgeClass d)) d := by
  cases d with
  | outerForward j => exact Or.inl rfl
  | outerBackward j => exact Or.inr rfl
  | relatorForward i j => exact Or.inl rfl
  | relatorBackward i j => exact Or.inr rfl
  | stemOut i => exact Or.inl rfl
  | stemIn i => exact Or.inr rfl

/-- Edge pairs are exactly the explicitly indexed polygon edges and stems. -/
noncomputable def edgeEquiv (S : CactusShape) :
    S.toCombMap.Edge ≃ S.EdgeIndex where
  toFun := Quotient.lift S.edgeClass fun d e hde ↦ by
    rcases hde with hde | hde
    · exact congrArg S.edgeClass hde
    · calc
        S.edgeClass d = S.edgeClass (S.alpha d) := (S.edgeClass_alpha d).symm
        _ = S.edgeClass e := congrArg S.edgeClass hde
  invFun e := Quotient.mk'' (S.edgeRepresentative e)
  left_inv q := by
    refine Quotient.inductionOn' q ?_
    intro d
    apply Quotient.sound
    exact S.edgeRepresentative_related d
  right_inv e := S.edgeClass_representative e

/-- The cactus has all polygon edges and one stem edge per cell. -/
theorem edgeCount_eq (S : CactusShape) :
    S.toCombMap.edgeCount =
      S.boundaryLength +
        (∑ i : Fin S.cellCount, S.relatorLength i) + S.cellCount := by
  rw [CombMap.edgeCount, Nat.card_congr S.edgeEquiv]
  simp [EdgeIndex]

/-! ## Face orbits -/

/-- The outer face, one relator face per cell, and the complementary face. -/
inductive FaceIndex (S : CactusShape)
  | outer
  | relator : Fin S.cellCount → FaceIndex S
  | big
  deriving DecidableEq, Fintype

/-- A sum presentation used to compute the number of face indices. -/
def faceIndexEquiv (S : CactusShape) :
    S.FaceIndex ≃ (Unit ⊕ Fin S.cellCount) ⊕ Unit where
  toFun
    | .outer => Sum.inl (Sum.inl ())
    | .relator i => Sum.inl (Sum.inr i)
    | .big => Sum.inr ()
  invFun
    | Sum.inl (Sum.inl _) => .outer
    | Sum.inl (Sum.inr i) => .relator i
    | Sum.inr _ => .big
  left_inv f := by cases f <;> rfl
  right_inv q := by
    rcases q with (q | q)
    · rcases q with (q | i)
      · rcases q with ⟨⟩
        rfl
      · rfl
    · rcases q with ⟨⟩
      rfl

/-- The explicit face containing a cactus dart. -/
def faceClass (S : CactusShape) : CactusDart S → S.FaceIndex
  | .outerForward _ => .outer
  | .relatorForward i _ => .relator i
  | .outerBackward _ => .big
  | .relatorBackward _ _ => .big
  | .stemOut _ => .big
  | .stemIn _ => .big

/-- One canonical dart in every cactus face. -/
def faceRepresentative (S : CactusShape) : S.FaceIndex → CactusDart S
  | .outer => .outerForward S.boundaryZero
  | .relator i => .relatorForward i (S.relatorZero i)
  | .big => .outerBackward S.boundaryZero

theorem faceClass_representative (S : CactusShape) (f : S.FaceIndex) :
    S.faceClass (S.faceRepresentative f) = f := by
  cases f <;> rfl

@[simp] theorem facePerm_outerForward (S : CactusShape)
    (j : Fin S.boundaryLength) :
    S.toCombMap.facePerm (.outerForward j) =
      .outerForward (nextFin S.boundaryLength j) := rfl

@[simp] theorem facePerm_relatorForward (S : CactusShape)
    (i : Fin S.cellCount) (j : Fin (S.relatorLength i)) :
    S.toCombMap.facePerm (.relatorForward i j) =
      .relatorForward i (nextFin (S.relatorLength i) j) := rfl

/-- Face rotation preserves the explicit face classifier. -/
theorem faceClass_facePerm (S : CactusShape) (d : CactusDart S) :
    S.faceClass (S.toCombMap.facePerm d) = S.faceClass d := by
  cases d with
  | outerForward j => rfl
  | relatorForward i j => rfl
  | outerBackward j =>
      change S.faceClass (S.sigmaFun (S.alphaFun (.outerBackward j))) =
        S.faceClass (.outerBackward j)
      by_cases hj : j = S.boundaryZero
      · subst j
        by_cases hn : 0 < S.cellCount
        · simp [alphaFun, sigmaFun, faceClass, hn]
        · simp [alphaFun, sigmaFun, faceClass, hn]
      · simp [alphaFun, sigmaFun, faceClass, hj]
  | relatorBackward i j =>
      change S.faceClass (S.sigmaFun (S.alphaFun (.relatorBackward i j))) =
        S.faceClass (.relatorBackward i j)
      by_cases hj : j = S.relatorZero i
      · subst j
        simp [alphaFun, sigmaFun, faceClass]
      · simp [alphaFun, sigmaFun, faceClass, hj]
  | stemOut i => rfl
  | stemIn i =>
      change S.faceClass (S.sigmaFun (S.alphaFun (.stemIn i))) =
        S.faceClass (.stemIn i)
      by_cases hi : nextFin S.cellCount i =
          S.cellZero (Nat.zero_lt_of_lt i.isLt)
      · simp [alphaFun, sigmaFun, faceClass, hi]
      · simp [alphaFun, sigmaFun, faceClass, hi]

/-- Away from the distinguished outer vertex, the complementary face moves
one outer edge backward. -/
theorem facePerm_outerBackward_of_ne (S : CactusShape)
    (j : Fin S.boundaryLength) (hj : j ≠ S.boundaryZero) :
    S.toCombMap.facePerm (.outerBackward j) =
      .outerBackward (prevFin S.boundaryLength j) := by
  change S.sigmaFun (.outerForward j) = _
  rw [sigmaFun, dif_neg hj]

/-- With at least one cell, the complementary face leaves the distinguished
outer vertex along the first stem. -/
theorem facePerm_outerBackward_zero (S : CactusShape)
    (hpos : 0 < S.cellCount) :
    S.toCombMap.facePerm (.outerBackward S.boundaryZero) =
      .stemOut (S.cellZero hpos) := by
  change S.sigmaFun (.outerForward S.boundaryZero) = _
  rw [sigmaFun, dif_pos rfl, dif_pos hpos]

/-- Away from its distinguished vertex, a relator loop moves one edge
backward in the complementary face. -/
theorem facePerm_relatorBackward_of_ne (S : CactusShape)
    (i : Fin S.cellCount) (j : Fin (S.relatorLength i))
    (hj : j ≠ S.relatorZero i) :
    S.toCombMap.facePerm (.relatorBackward i j) =
      .relatorBackward i (prevFin (S.relatorLength i) j) := by
  change S.sigmaFun (.relatorForward i j) = _
  rw [sigmaFun, dif_neg hj]

/-- At the distinguished relator vertex, the complementary face enters the
return orientation of the stem. -/
theorem facePerm_relatorBackward_zero (S : CactusShape)
    (i : Fin S.cellCount) :
    S.toCombMap.facePerm (.relatorBackward i (S.relatorZero i)) =
      .stemIn i := by
  change S.sigmaFun (.relatorForward i (S.relatorZero i)) = _
  rw [sigmaFun, dif_pos rfl]

/-- Before the final stem, the complementary face proceeds to the next
outgoing stem. -/
theorem facePerm_stemIn_of_ne (S : CactusShape) (i : Fin S.cellCount)
    (hi : nextFin S.cellCount i ≠
      S.cellZero (Nat.zero_lt_of_lt i.isLt)) :
    S.toCombMap.facePerm (.stemIn i) =
      .stemOut (nextFin S.cellCount i) := by
  change S.sigmaFun (.stemOut i) = _
  rw [sigmaFun, dif_neg hi]

/-- Backward outer darts lie in the complementary face without using the
wrap step at the distinguished vertex. -/
theorem outerBackward_sameCycle (S : CactusShape)
    (j : Fin S.boundaryLength) :
    S.toCombMap.facePerm.SameCycle (.outerBackward S.boundaryZero)
      (.outerBackward j) := by
  obtain ⟨k, hk⟩ := j
  induction k with
  | zero =>
      have heq : (⟨0, hk⟩ : Fin S.boundaryLength) = S.boundaryZero := by
        apply Fin.ext
        rfl
      rw [heq]
  | succ k ih =>
      have hk' : k < S.boundaryLength := lt_trans (Nat.lt_succ_self k) hk
      have hprevious := ih hk'
      let previous : Fin S.boundaryLength := ⟨k, hk'⟩
      let current : Fin S.boundaryLength := ⟨k + 1, hk⟩
      haveI : NeZero S.boundaryLength := ⟨Nat.ne_of_gt S.boundary_pos⟩
      have hnext : nextFin S.boundaryLength previous = current := by
        apply Fin.ext
        simp [nextFin, previous, current, finRotate_apply,
          Fin.add_def, Nat.mod_eq_of_lt hk]
      have hprev : prevFin S.boundaryLength current = previous := by
        rw [← hnext]
        exact prevFin_nextFin S.boundaryLength previous
      have hne : current ≠ S.boundaryZero := by
        intro hzero
        have hval := congrArg Fin.val hzero
        simp [current, boundaryZero] at hval
      have hface : S.toCombMap.facePerm (.outerBackward current) =
          .outerBackward previous := by
        rw [S.facePerm_outerBackward_of_ne current hne, hprev]
      have hstep : S.toCombMap.facePerm.SameCycle
          (.outerBackward previous) (.outerBackward current) := by
        have h := sameCycle_apply S.toCombMap.facePerm (.outerBackward current)
        rw [hface] at h
        exact h.symm
      exact hprevious.trans hstep

/-- Backward darts of one relator polygon lie in one segment of the
complementary face. -/
theorem relatorBackward_sameCycle (S : CactusShape) (i : Fin S.cellCount)
    (j : Fin (S.relatorLength i)) :
    S.toCombMap.facePerm.SameCycle
      (.relatorBackward i (S.relatorZero i)) (.relatorBackward i j) := by
  obtain ⟨k, hk⟩ := j
  induction k with
  | zero =>
      have heq : (⟨0, hk⟩ : Fin (S.relatorLength i)) = S.relatorZero i := by
        apply Fin.ext
        rfl
      rw [heq]
  | succ k ih =>
      have hk' : k < S.relatorLength i := lt_trans (Nat.lt_succ_self k) hk
      have hprevious := ih hk'
      let previous : Fin (S.relatorLength i) := ⟨k, hk'⟩
      let current : Fin (S.relatorLength i) := ⟨k + 1, hk⟩
      haveI : NeZero (S.relatorLength i) := ⟨Nat.ne_of_gt (S.relator_pos i)⟩
      have hnext : nextFin (S.relatorLength i) previous = current := by
        apply Fin.ext
        simp [nextFin, previous, current, finRotate_apply,
          Fin.add_def, Nat.mod_eq_of_lt hk]
      have hprev : prevFin (S.relatorLength i) current = previous := by
        rw [← hnext]
        exact prevFin_nextFin (S.relatorLength i) previous
      have hne : current ≠ S.relatorZero i := by
        intro hzero
        have hval := congrArg Fin.val hzero
        simp [current, relatorZero] at hval
      have hface : S.toCombMap.facePerm (.relatorBackward i current) =
          .relatorBackward i previous := by
        rw [S.facePerm_relatorBackward_of_ne i current hne, hprev]
      have hstep : S.toCombMap.facePerm.SameCycle
          (.relatorBackward i previous) (.relatorBackward i current) := by
        have h := sameCycle_apply S.toCombMap.facePerm
          (.relatorBackward i current)
        rw [hface] at h
        exact h.symm
      exact hprevious.trans hstep

/-- Traversing a stem and the adjacent relator loop reaches the incoming
orientation of that stem. -/
theorem stemOut_sameCycle_stemIn (S : CactusShape) (i : Fin S.cellCount) :
    S.toCombMap.facePerm.SameCycle (.stemOut i) (.stemIn i) := by
  let last := prevFin (S.relatorLength i) (S.relatorZero i)
  have hout : S.toCombMap.facePerm (.stemOut i) =
      .relatorBackward i last := by rfl
  have h₁ := sameCycle_apply S.toCombMap.facePerm (.stemOut i)
  rw [hout] at h₁
  have hsegment := S.relatorBackward_sameCycle i last
  have hzero : S.toCombMap.facePerm
      (.relatorBackward i (S.relatorZero i)) = .stemIn i := by
    exact S.facePerm_relatorBackward_zero i
  have h₂ := sameCycle_apply S.toCombMap.facePerm
    (.relatorBackward i (S.relatorZero i))
  rw [hzero] at h₂
  exact h₁.trans (hsegment.symm.trans h₂)

/-- The complementary face reaches every outgoing stem in increasing cell
order. -/
theorem big_sameCycle_stemOut (S : CactusShape) (i : Fin S.cellCount) :
    S.toCombMap.facePerm.SameCycle (.outerBackward S.boundaryZero)
      (.stemOut i) := by
  let hpos : 0 < S.cellCount := Nat.zero_lt_of_lt i.isLt
  obtain ⟨k, hk⟩ := i
  induction k with
  | zero =>
      have heq : (⟨0, hk⟩ : Fin S.cellCount) = S.cellZero hpos := by
        apply Fin.ext
        rfl
      rw [heq]
      have hface : S.toCombMap.facePerm (.outerBackward S.boundaryZero) =
          .stemOut (S.cellZero hpos) := by
        exact S.facePerm_outerBackward_zero hpos
      simpa [hface] using sameCycle_apply S.toCombMap.facePerm
        (.outerBackward S.boundaryZero)
  | succ k ih =>
      have hk' : k < S.cellCount := lt_trans (Nat.lt_succ_self k) hk
      have hprevious := ih hk'
      let previous : Fin S.cellCount := ⟨k, hk'⟩
      let current : Fin S.cellCount := ⟨k + 1, hk⟩
      haveI : NeZero S.cellCount := ⟨Nat.ne_of_gt hpos⟩
      have hnext : nextFin S.cellCount previous = current := by
        apply Fin.ext
        simp [nextFin, previous, current, finRotate_apply,
          Fin.add_def, Nat.mod_eq_of_lt hk]
      have hnot : nextFin S.cellCount previous ≠
          S.cellZero (Nat.zero_lt_of_lt previous.isLt) := by
        rw [hnext]
        intro hzero
        have hval := congrArg Fin.val hzero
        simp [current, cellZero] at hval
      have hin : S.toCombMap.facePerm (.stemIn previous) = .stemOut current := by
        rw [S.facePerm_stemIn_of_ne previous hnot, hnext]
      have hstep := sameCycle_apply S.toCombMap.facePerm (.stemIn previous)
      rw [hin] at hstep
      exact hprevious.trans ((S.stemOut_sameCycle_stemIn previous).trans hstep)

/-- Every dart lies in the face cycle of its canonical representative. -/
theorem faceRepresentative_sameCycle (S : CactusShape) (d : CactusDart S) :
    S.toCombMap.facePerm.SameCycle
      (S.faceRepresentative (S.faceClass d)) d := by
  cases d with
  | outerForward j =>
      apply OrbitClassifier.sameCycle_map (finRotate S.boundaryLength)
        S.toCombMap.facePerm CactusDart.outerForward
      · exact S.facePerm_outerForward
      · exact finRotate_sameCycle S.boundary_pos S.boundaryZero j
  | relatorForward i j =>
      apply OrbitClassifier.sameCycle_map (finRotate (S.relatorLength i))
        S.toCombMap.facePerm (CactusDart.relatorForward i)
      · exact S.facePerm_relatorForward i
      · exact finRotate_sameCycle (S.relator_pos i) (S.relatorZero i) j
  | outerBackward j => exact S.outerBackward_sameCycle j
  | stemOut i => exact S.big_sameCycle_stemOut i
  | stemIn i =>
      exact (S.big_sameCycle_stemOut i).trans (S.stemOut_sameCycle_stemIn i)
  | relatorBackward i j =>
      let last := prevFin (S.relatorLength i) (S.relatorZero i)
      have hout : S.toCombMap.facePerm (.stemOut i) =
          .relatorBackward i last := by rfl
      have hstep := sameCycle_apply S.toCombMap.facePerm (.stemOut i)
      rw [hout] at hstep
      exact (S.big_sameCycle_stemOut i).trans
        (hstep.trans ((S.relatorBackward_sameCycle i last).symm.trans
          (S.relatorBackward_sameCycle i j)))

/-- Face orbits are exactly the outer, relator, and complementary faces. -/
noncomputable def faceEquiv (S : CactusShape) :
    S.toCombMap.Face ≃ S.FaceIndex :=
  OrbitClassifier.orbitEquiv S.toCombMap.facePerm S.faceClass
    S.faceRepresentative S.faceClass_facePerm S.faceClass_representative
    S.faceRepresentative_sameCycle

/-- The cactus has one outer face, one face per cell, and one complementary
face. -/
theorem faceCount_eq (S : CactusShape) :
    S.toCombMap.faceCount = S.cellCount + 2 := by
  rw [CombMap.faceCount, Nat.card_congr S.faceEquiv,
    Nat.card_eq_fintype_card]
  rw [Fintype.card_congr S.faceIndexEquiv]
  simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
  omega

/-! ## Connectedness and Euler characteristic -/

/-- One face-rotation step is a reversal followed by a vertex-rotation step,
so it lies in the connectivity relation of the map. -/
theorem eqvGen_facePerm_apply (S : CactusShape) (d : CactusDart S) :
    Relation.EqvGen S.toCombMap.Adjacent d (S.toCombMap.facePerm d) := by
  have halpha : Relation.EqvGen S.toCombMap.Adjacent d
      (S.toCombMap.alpha d) :=
    Relation.EqvGen.rel _ _ (Or.inl rfl)
  have hsigma : Relation.EqvGen S.toCombMap.Adjacent
      (S.toCombMap.alpha d) (S.toCombMap.sigma (S.toCombMap.alpha d)) :=
    Relation.EqvGen.rel _ _ (Or.inr rfl)
  exact Relation.EqvGen.trans _ _ _ halpha hsigma

/-- Darts in one face orbit are connected by elementary reversal and vertex
rotation moves. -/
theorem eqvGen_of_faceSameCycle (S : CactusShape) {d e : CactusDart S}
    (hde : S.toCombMap.facePerm.SameCycle d e) :
    Relation.EqvGen S.toCombMap.Adjacent d e := by
  obtain ⟨n, hn⟩ := hde.exists_nat_pow_eq
  have hpow : ∀ (m : ℕ) (x : CactusDart S),
      Relation.EqvGen S.toCombMap.Adjacent x
        ((S.toCombMap.facePerm ^ m) x) := by
    intro m
    induction m with
    | zero => intro x; exact Relation.EqvGen.refl x
    | succ m ih =>
        intro x
        rw [pow_succ, Perm.mul_apply]
        exact Relation.EqvGen.trans _ _ _ (S.eqvGen_facePerm_apply x)
          (ih (S.toCombMap.facePerm x))
  have h := hpow n d
  rw [hn] at h
  exact h

/-- Every cactus dart is connected to the canonical dart of the complementary
face. -/
theorem bigRepresentative_connected (S : CactusShape) (d : CactusDart S) :
    Relation.EqvGen S.toCombMap.Adjacent
      (.outerBackward S.boundaryZero) d := by
  cases d with
  | outerBackward j =>
      exact S.eqvGen_of_faceSameCycle (S.outerBackward_sameCycle j)
  | relatorBackward i j =>
      exact S.eqvGen_of_faceSameCycle
        (S.faceRepresentative_sameCycle (.relatorBackward i j))
  | stemOut i =>
      exact S.eqvGen_of_faceSameCycle (S.big_sameCycle_stemOut i)
  | stemIn i =>
      exact S.eqvGen_of_faceSameCycle
        ((S.big_sameCycle_stemOut i).trans (S.stemOut_sameCycle_stemIn i))
  | outerForward j =>
      have hback := S.eqvGen_of_faceSameCycle (S.outerBackward_sameCycle j)
      have hedge : Relation.EqvGen S.toCombMap.Adjacent
          (.outerForward j) (.outerBackward j) :=
        Relation.EqvGen.rel _ _ (Or.inl rfl)
      exact Relation.EqvGen.trans _ _ _ hback
        (Relation.EqvGen.symm _ _ hedge)
  | relatorForward i j =>
      have hback := S.eqvGen_of_faceSameCycle
        (S.faceRepresentative_sameCycle (.relatorBackward i j))
      have hedge : Relation.EqvGen S.toCombMap.Adjacent
          (.relatorForward i j) (.relatorBackward i j) :=
        Relation.EqvGen.rel _ _ (Or.inl rfl)
      exact Relation.EqvGen.trans _ _ _ hback
        (Relation.EqvGen.symm _ _ hedge)

/-- The polygon cactus is connected. -/
theorem connected (S : CactusShape) : S.toCombMap.IsConnected := by
  intro d e
  exact Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.symm _ _ (S.bigRepresentative_connected d))
    (S.bigRepresentative_connected e)

/-- The explicit orbit counts give Euler characteristic two. -/
theorem eulerCharacteristic_eq_two (S : CactusShape) :
    S.toCombMap.eulerCharacteristic = 2 := by
  rw [CombMap.eulerCharacteristic, S.vertexCount_eq, S.edgeCount_eq,
    S.faceCount_eq]
  push_cast
  ring

/-- The closed cactus rotation system is planar. -/
theorem planar (S : CactusShape) : S.toCombMap.IsPlanar :=
  ⟨S.connected, S.eulerCharacteristic_eq_two⟩

/-! ## Small executable shapes -/

/-- A triangle with no attached relator polygons. -/
def zeroCellModel : CactusShape where
  boundaryLength := 3
  boundary_pos := by omega
  cellCount := 0
  relatorLength i := i.elim0
  relator_pos i := i.elim0

/-- At zero factors the model has one polygon and its two sides as faces. -/
theorem zeroCellModel_counts :
    zeroCellModel.toCombMap.vertexCount = 3 ∧
    zeroCellModel.toCombMap.edgeCount = 3 ∧
    zeroCellModel.toCombMap.faceCount = 2 := by
  constructor
  · simpa [zeroCellModel] using zeroCellModel.vertexCount_eq
  · constructor
    · simpa [zeroCellModel] using zeroCellModel.edgeCount_eq
    · simpa [zeroCellModel] using zeroCellModel.faceCount_eq

/-- The zero-factor model is planar by the explicit Euler computation. -/
theorem zeroCellModel_planar : zeroCellModel.toCombMap.IsPlanar :=
  zeroCellModel.planar

/-- A digon with one triangular relator polygon attached by one stem. -/
def oneCellModel : CactusShape where
  boundaryLength := 2
  boundary_pos := by omega
  cellCount := 1
  relatorLength _ := 3
  relator_pos _ := by omega

/-- The one-factor model has five vertices, six edges, and three faces. -/
theorem oneCellModel_counts :
    oneCellModel.toCombMap.vertexCount = 5 ∧
    oneCellModel.toCombMap.edgeCount = 6 ∧
    oneCellModel.toCombMap.faceCount = 3 := by
  constructor
  · simpa [oneCellModel] using oneCellModel.vertexCount_eq
  · constructor
    · simpa [oneCellModel] using oneCellModel.edgeCount_eq
    · simpa [oneCellModel] using oneCellModel.faceCount_eq

/-- The one-factor model is planar by the explicit Euler computation. -/
theorem oneCellModel_planar : oneCellModel.toCombMap.IsPlanar :=
  oneCellModel.planar

end CactusShape

end VanKampen
end GGT
end GroupApproximation

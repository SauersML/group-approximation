import GroupApproximation.GGT.VanKampen.CactusMap

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

end CactusShape

end VanKampen
end GGT
end GroupApproximation

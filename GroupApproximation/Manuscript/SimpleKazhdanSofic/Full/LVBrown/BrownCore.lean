import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVBrown.BrownRep
import Mathlib.Algebra.Group.Action.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Brown's criterion: representatives respect the Brown relations (T1d)

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735, leaf **T1d** (Khanh,
arXiv:2609.08428, Thm 5.1; K. S. Brown 1984, Thm 1).  This file builds on `LVBrown/BrownRep.lean`.

The Brown relations for the fundamental domain `{v0}` are `[a][b] = [ab]`, one for each cell
`(v0, a•v0, ab•v0)`.  Here `rel_rep` shows that the candidate images `Rep` are multiplicative
along such a relation.  When `a = kτm` and `b = k'τm'` both pass through `τ`, the cell becomes
`(v0, v1, τ n • v1)` with `n = mk' ∈ J`.  The core lemma `rep_core` computes a representative of
`τ n τ` from that cell.
* When the cell is an ordered triangle, triangle transitivity gives `g ∈ J` with `g•v1 = v1` and
  `g•h•v1 = τ n•v1`.  Conjugating by `τ` factors `n = G' h P`, where `G'` and `P` fix `v1`.  The
  edge relation and the braid relation `t h t = h t h` then compute the image.
* When the cell is degenerate, `n` fixes `v1` and the edge relation together with `t² = f(τ²)`
  suffices.
-/

namespace GroupApproximation.Full.LVBrown

open GroupApproximation.Full.LVFrame

variable {G V Q : Type*} [Group G] [MulAction G V] [Group Q]

/-- Conjugating an element of `J ∩ Stab v1` by `τ`, together with the edge relation. -/
theorem conj_stab {v0 v1 : V} {τ : G} (hτ0 : τ • v0 = v1) (hτ1 : τ • v1 = v0)
    (f : MulAction.stabilizer G v0 →* Q) (t : Q)
    (hedge : ∀ a b : MulAction.stabilizer G v0, (a : G) • v1 = v1 → (b : G) = τ * a * τ⁻¹ →
      t * f a * t⁻¹ = f b)
    (x : MulAction.stabilizer G v0) (hx1 : (x : G) • v1 = v1) :
    ∃ x' : MulAction.stabilizer G v0, (x' : G) = τ⁻¹ * (x : G) * τ ∧ (x' : G) • v1 = v1 ∧
      t * f x' * t⁻¹ = f x := by
  have hτinv1 : τ⁻¹ • v1 = v0 := by rw [← hτ0, inv_smul_smul]
  have hτinv0 : τ⁻¹ • v0 = v1 := by rw [← hτ1, inv_smul_smul]
  have hm : τ⁻¹ * (x : G) * τ ∈ MulAction.stabilizer G v0 := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hτ0, hx1, hτinv1]
  have h1 : (τ⁻¹ * (x : G) * τ) • v1 = v1 := by
    rw [mul_smul, mul_smul, hτ1, smul_stab x, hτinv0]
  have hconj : (x : G) = τ * (τ⁻¹ * (x : G) * τ) * τ⁻¹ := by group
  exact ⟨⟨τ⁻¹ * (x : G) * τ, hm⟩, rfl, h1, hedge ⟨τ⁻¹ * (x : G) * τ, hm⟩ x h1 hconj⟩

/-- The representative of `τ n τ` for `n ∈ J ∩ Stab v1`. -/
theorem rep_of_stab1 {v0 v1 : V} {τ : G} (hτ1 : τ • v1 = v0)
    (f : MulAction.stabilizer G v0 →* Q) (t : Q)
    (hedge : ∀ a b : MulAction.stabilizer G v0, (a : G) • v1 = v1 → (b : G) = τ * a * τ⁻¹ →
      t * f a * t⁻¹ = f b)
    (hτ2 : (τ * τ) • v0 = v0) (ht2 : t * t = f ⟨τ * τ, hτ2⟩)
    (n : MulAction.stabilizer G v0) (hn1 : (n : G) • v1 = v1) :
    Rep v0 τ f t (τ * (n : G) * τ) (t * f n * t) := by
  have hτinv0 : τ⁻¹ • v0 = v1 := by rw [← hτ1, inv_smul_smul]
  have hb : τ * (n : G) * τ⁻¹ ∈ MulAction.stabilizer G v0 := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hτinv0, hn1, hτ1]
  have he : t * f n * t⁻¹ = f ⟨τ * (n : G) * τ⁻¹, hb⟩ := hedge n ⟨τ * (n : G) * τ⁻¹, hb⟩ hn1 rfl
  refine Or.inl ⟨(⟨τ * (n : G) * τ⁻¹, hb⟩ : MulAction.stabilizer G v0) *
    (⟨τ * τ, hτ2⟩ : MulAction.stabilizer G v0), ?_, ?_⟩
  · show τ * (n : G) * τ⁻¹ * (τ * τ) = τ * (n : G) * τ
    group
  · rw [map_mul, ← he, ← ht2]
    group

/-- **Core lemma.**  A cell `(v0, v1, τ n • v1)` with `n ∈ J` yields a representative of
`τ n τ`. -/
theorem rep_core {X : OrderedTwoComplex V} {v0 v1 : V} {τ h : G}
    (hτ0 : τ • v0 = v1) (hτ1 : τ • v1 = v0) (hh0 : h • v0 = v0)
    (hbraid : τ * h * τ = h * τ * h)
    (tri_transitive : ∀ a b c, X.tri a b c → ∃ g : G, g • v0 = a ∧ g • v1 = b ∧ g • (h • v1) = c)
    (f : MulAction.stabilizer G v0 →* Q) (t : Q)
    (hedge : ∀ a b : MulAction.stabilizer G v0, (a : G) • v1 = v1 → (b : G) = τ * a * τ⁻¹ →
      t * f a * t⁻¹ = f b)
    (hτ2 : (τ * τ) • v0 = v0) (ht2 : t * t = f ⟨τ * τ, hτ2⟩)
    (hbr : t * f ⟨h, hh0⟩ * t = f ⟨h, hh0⟩ * t * f ⟨h, hh0⟩)
    (n : MulAction.stabilizer G v0) (hc : Cell X v0 v1 (τ • (n : G) • v1)) :
    Rep v0 τ f t (τ * (n : G) * τ) (t * f n * t) := by
  have hτinv1 : τ⁻¹ • v1 = v0 := by rw [← hτ0, inv_smul_smul]
  rcases hc with htri | ⟨-, -, -, hdeg⟩
  · obtain ⟨g, hg0, hg1, hgh⟩ := tri_transitive _ _ _ htri
    obtain ⟨G1, rfl⟩ : ∃ G1 : MulAction.stabilizer G v0, (G1 : G) = g :=
      ⟨⟨g, MulAction.mem_stabilizer_iff.mpr hg0⟩, rfl⟩
    have hτh : τ • h • v1 = h • v1 := by
      calc τ • h • v1 = (τ * h * τ) • v0 := by rw [mul_smul, mul_smul, hτ0]
        _ = (h * τ * h) • v0 := by rw [hbraid]
        _ = h • v1 := by rw [mul_smul, mul_smul, hh0, hτ0]
    obtain ⟨G', hG'c, -, E1⟩ := conj_stab hτ0 hτ1 f t hedge G1 hg1
    have hτG : τ * (τ⁻¹ * (G1 : G) * τ) = (G1 : G) * τ := by group
    have hg'h : (G' : G) • h • v1 = (n : G) • v1 := by
      apply smul_left_cancel τ
      rw [← mul_smul, hG'c, hτG, mul_smul, hτh, hgh]
    obtain ⟨P, hP⟩ : ∃ P : MulAction.stabilizer G v0, (P : G) = h⁻¹ * (G' : G)⁻¹ * (n : G) :=
      ⟨(⟨h, hh0⟩ : MulAction.stabilizer G v0)⁻¹ * G'⁻¹ * n, rfl⟩
    have hp1 : (P : G) • v1 = v1 := by
      rw [hP, mul_smul, mul_smul, ← hg'h, inv_smul_smul, inv_smul_smul]
    obtain ⟨P', hP'c, -, E2⟩ := conj_stab hτ0 hτ1 f t hedge P hp1
    have hn_eq : (n : G) = (G' : G) * h * (P : G) := by
      rw [hP]
      group
    have hfn : n = G' * (⟨h, hh0⟩ : MulAction.stabilizer G v0) * P := by
      apply Subtype.ext
      show (n : G) = (G' : G) * h * (P : G)
      exact hn_eq
    have hGside : τ * (n : G) * τ = (G1 : G) * h * τ * (h * (P' : G)) := by
      calc τ * (n : G) * τ = (G1 : G) * (τ * h * τ) * τ⁻¹ * (P : G) * τ := by
            rw [hn_eq, hG'c]
            group
        _ = (G1 : G) * (h * τ * h) * τ⁻¹ * (P : G) * τ := by rw [hbraid]
        _ = (G1 : G) * h * τ * (h * (P' : G)) := by
            rw [hP'c]
            group
    refine Or.inr ⟨G1 * (⟨h, hh0⟩ : MulAction.stabilizer G v0),
      (⟨h, hh0⟩ : MulAction.stabilizer G v0) * P', ?_, ?_⟩
    · exact hGside
    · rw [hfn]
      simp only [map_mul]
      exact alg_tri E1 E2 hbr
  · have hw : τ • (n : G) • v1 = v0 := by
      rcases hdeg with h01 | h12 | h02
      · rw [← h01, smul_stab n, hτ0]
        exact h01.symm
      · have e : (n : G) • v1 = v0 := by
          calc (n : G) • v1 = τ⁻¹ • τ • (n : G) • v1 := (inv_smul_smul τ _).symm
            _ = τ⁻¹ • v1 := by rw [← h12]
            _ = v0 := hτinv1
        exact h12.symm.trans (smul_left_cancel (n : G) (e.trans (smul_stab n).symm))
      · exact h02.symm
    have hn1 : (n : G) • v1 = v1 := by
      apply smul_left_cancel τ
      rw [hw, hτ1]
    exact rep_of_stab1 hτ1 f t hedge hτ2 ht2 n hn1

/-- **Multiplicativity along a Brown relation.**  Let `a` and `b` have representatives, and let
`(v0, a•v0, ab•v0)` be a cell.  Then the product of the representatives represents `ab`. -/
theorem rel_rep {X : OrderedTwoComplex V} (hX : X.Action G) {v0 v1 : V} {τ h : G}
    (hτ0 : τ • v0 = v1) (hτ1 : τ • v1 = v0) (hh0 : h • v0 = v0)
    (hbraid : τ * h * τ = h * τ * h)
    (tri_transitive : ∀ a b c, X.tri a b c → ∃ g : G, g • v0 = a ∧ g • v1 = b ∧ g • (h • v1) = c)
    (f : MulAction.stabilizer G v0 →* Q) (t : Q)
    (hedge : ∀ a b : MulAction.stabilizer G v0, (a : G) • v1 = v1 → (b : G) = τ * a * τ⁻¹ →
      t * f a * t⁻¹ = f b)
    (hτ2 : (τ * τ) • v0 = v0) (ht2 : t * t = f ⟨τ * τ, hτ2⟩)
    (hbr : t * f ⟨h, hh0⟩ * t = f ⟨h, hh0⟩ * t * f ⟨h, hh0⟩)
    {a b c : G} {qa qb : Q} (ha : Rep v0 τ f t a qa) (hb : Rep v0 τ f t b qb) (hab : a * b = c)
    (hcell : Cell X v0 (a • v0) (c • v0)) : Rep v0 τ f t c (qa * qb) := by
  rcases ha with ⟨j, rfl, rfl⟩ | ⟨k, m, rfl, rfl⟩
  · subst hab
    exact rep_mul_left j hb
  · rcases hb with ⟨j, rfl, rfl⟩ | ⟨k', m', rfl, rfl⟩
    · subst hab
      exact rep_mul_right j (Or.inr ⟨k, m, rfl, rfl⟩)
    · subst hab
      have e1 : ((k : G) * τ * (m : G)) • v0 = (k : G) • v1 := by
        rw [mul_smul, smul_stab m, mul_smul, hτ0]
      have hprod : (k : G) * τ * (m : G) * ((k' : G) * τ * (m' : G)) =
          (k : G) * τ * ((m : G) * (k' : G)) * τ * (m' : G) := by group
      have e2 : ((k : G) * τ * (m : G) * ((k' : G) * τ * (m' : G))) • v0 =
          (k : G) • τ • ((m : G) * (k' : G)) • v1 := by
        rw [hprod, mul_smul, smul_stab m', mul_smul, hτ0, mul_smul, mul_smul]
      rw [e1, e2] at hcell
      have hc' : Cell X v0 v1 (τ • ((m * k' : MulAction.stabilizer G v0) : G) • v1) := by
        refine (cell_smul_iff hX (k : G)).mp ?_
        rw [smul_stab k]
        exact hcell
      have hcore := rep_core hτ0 hτ1 hh0 hbraid tri_transitive f t hedge hτ2 ht2 hbr (m * k') hc'
      have hg : (k : G) * (τ * ((m * k' : MulAction.stabilizer G v0) : G) * τ * (m' : G)) =
          (k : G) * τ * (m : G) * ((k' : G) * τ * (m' : G)) := by
        show (k : G) * (τ * ((m : G) * (k' : G)) * τ * (m' : G)) =
          (k : G) * τ * (m : G) * ((k' : G) * τ * (m' : G))
        group
      have hq : f k * (t * f (m * k') * t * f m') = f k * t * f m * (f k' * t * f m') := by
        rw [map_mul]
        group
      exact rep_congr (rep_mul_left k (rep_mul_right m' hcore)) hg hq

#audit_axioms GroupApproximation.Full.LVBrown.rel_rep

end GroupApproximation.Full.LVBrown

import GroupApproximation.GGT.VanKampen.Estimating.Embedded
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, inner pocket: sub-arcs of a cyclic arc

Infrastructure for lane gl-p07-14 (the normal form of `InnerPocketEnclosedTwoArcStatement`,
`GreendlingerLeaf/P07LakeExclusion/InnerTwoArcLong.lean`).  Certifies no printed sentence on its
own; it serves `thm:hull` (tex 1636, through Osin's Lemma 9.7) via the Greendlinger leaf.

A contiguous piece of a cyclic arc is again a cyclic arc of the same carrier cycle.

**Proof.**  Let `A` have base position `s` and length `L` on the cycle `c` of length `n`, and
let `A.darts = (c.rotate s).take L = u ++ v ++ z`.  Put `B.start := (s + |u|) mod n` and
`B.length := |v|`; `|v| ≤ L ≤ n`.  The base position is `< n + 1`: for `n > 0` by `Nat.mod_lt`,
and for `n = 0` because `s ≤ 0` and `|u| ≤ L ≤ 0`.  Writing
`c.rotate s = u ++ (v ++ (z ++ (c.rotate s).drop L))`, we get
`c.rotate ((s + |u|) mod n) = (c.rotate s).rotate |u| = v ++ (z ++ rest) ++ u`
by `List.rotate_mod`, `List.rotate_rotate` and `List.rotate_append_length_eq`, whose first `|v|`
darts are `v`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe v

namespace CyclicArc

variable {Dart : Type v} {cyc : List Dart}

/-- The three pieces of a split arc add up to the arc length. -/
theorem length_add_of_darts_eq (A : Embedded.CyclicArc cyc) {u w z : List Dart}
    (h : A.darts = u ++ w ++ z) : u.length + w.length + z.length = A.length := by
  rw [← A.darts_length, h, List.length_append, List.length_append]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.CyclicArc.length_add_of_darts_eq

/-- The base position `(A.start + k) mod |cyc|` of a sub-arc that skips `k ≤ A.length` darts. -/
def subArcStart (A : Embedded.CyclicArc cyc) (k : ℕ) (hk : k ≤ A.length) :
    Fin (cyc.length + 1) :=
  ⟨(A.start.1 + k) % cyc.length, by
    have hs := A.start.2
    have hl := A.length_le
    have hmod := Nat.mod_le (A.start.1 + k) cyc.length
    rcases Nat.eq_zero_or_pos cyc.length with h0 | hpos
    · generalize (A.start.1 + k) % cyc.length = m at hmod ⊢
      omega
    · have hlt := Nat.mod_lt (A.start.1 + k) hpos
      generalize (A.start.1 + k) % cyc.length = m at hmod hlt ⊢
      omega⟩

/-- The sub-arc of `A` reading the middle piece `w` of a split `A.darts = u ++ w ++ z`. -/
def subArcArc (A : Embedded.CyclicArc cyc) (u w z : List Dart) (h : A.darts = u ++ w ++ z) :
    Embedded.CyclicArc cyc where
  start := subArcStart A u.length (by have := length_add_of_darts_eq A h; omega)
  length := w.length
  length_le := by
    have h₁ := length_add_of_darts_eq A h
    have h₂ := A.length_le
    omega

theorem subArcArc_start (A : Embedded.CyclicArc cyc) (u w z : List Dart)
    (h : A.darts = u ++ w ++ z) :
    (subArcArc A u w z h).start.1 = (A.start.1 + u.length) % cyc.length :=
  rfl

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.CyclicArc.subArcArc_start

theorem subArcArc_length (A : Embedded.CyclicArc cyc) (u w z : List Dart)
    (h : A.darts = u ++ w ++ z) : (subArcArc A u w z h).length = w.length :=
  rfl

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.CyclicArc.subArcArc_length

/-- The rotated cycle of an arc splits as the arc followed by the rest of the cycle. -/
theorem rotate_start_eq_append (A : Embedded.CyclicArc cyc) {u w z : List Dart}
    (h : A.darts = u ++ w ++ z) :
    cyc.rotate A.start.1 = u ++ (w ++ (z ++ (cyc.rotate A.start.1).drop A.length)) := by
  have hdarts : (cyc.rotate A.start.1).take A.length = u ++ w ++ z := by
    rw [← A.rotated_eq_rotate]
    exact h
  calc cyc.rotate A.start.1
      = (cyc.rotate A.start.1).take A.length ++ (cyc.rotate A.start.1).drop A.length :=
        (List.take_append_drop _ _).symm
    _ = u ++ (w ++ (z ++ (cyc.rotate A.start.1).drop A.length)) := by
        simp only [hdarts, List.append_assoc]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.CyclicArc.rotate_start_eq_append

/-- **The sub-arc reads the middle piece.** -/
theorem subArcArc_darts (A : Embedded.CyclicArc cyc) (u w z : List Dart)
    (h : A.darts = u ++ w ++ z) : (subArcArc A u w z h).darts = w := by
  show (subArcArc A u w z h).rotated.take w.length = w
  rw [Embedded.CyclicArc.rotated_eq_rotate, subArcArc_start, List.rotate_mod,
    ← List.rotate_rotate, rotate_start_eq_append A h, List.rotate_append_length_eq,
    List.append_assoc]
  exact List.take_left

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.CyclicArc.subArcArc_darts

/-- **Sub-arc tool.**  A contiguous piece `w` of a cyclic arc `A` is the dart list of a cyclic arc
of the same carrier. -/
def subArc (A : Embedded.CyclicArc cyc) (u w z : List Dart) (h : A.darts = u ++ w ++ z) :
    Σ' B : Embedded.CyclicArc cyc, B.darts = w :=
  ⟨subArcArc A u w z h, subArcArc_darts A u w z h⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.CyclicArc.subArc

/-- Propositional form of the sub-arc tool. -/
theorem exists_subArc (A : Embedded.CyclicArc cyc) {u w z : List Dart}
    (h : A.darts = u ++ w ++ z) : ∃ B : Embedded.CyclicArc cyc, B.darts = w :=
  ⟨subArcArc A u w z h, subArcArc_darts A u w z h⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.CyclicArc.exists_subArc

/-- A prefix of a cyclic arc is a cyclic arc. -/
theorem exists_subArc_prefix (A : Embedded.CyclicArc cyc) {w z : List Dart}
    (h : A.darts = w ++ z) : ∃ B : Embedded.CyclicArc cyc, B.darts = w :=
  exists_subArc A (u := []) (by rw [h, List.nil_append])

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.CyclicArc.exists_subArc_prefix

/-- A suffix of a cyclic arc is a cyclic arc. -/
theorem exists_subArc_suffix (A : Embedded.CyclicArc cyc) {u w : List Dart}
    (h : A.darts = u ++ w) : ∃ B : Embedded.CyclicArc cyc, B.darts = w :=
  exists_subArc A (z := []) (by rw [h, List.append_nil])

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.CyclicArc.exists_subArc_suffix

end CyclicArc

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

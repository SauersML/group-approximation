import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Function.Iterate
import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Minsky

/-!
# The Kharlampovich group `G(M)` of a Minsky machine

Input for `thm:fixed-radical-membership` of `non_mf_group_notes.tex`.  That
theorem uses Kharlampovich's finitely presented solvable group with undecidable
word problem.  We follow Kharlampovich--Myasnikov--Sapir, *Algorithmically
complex residually finite groups* (arXiv:1204.6506), Sec. 4.1 "The construction"
(relations G1--G8), with prime `p = 2`.

This file holds only definitions: the generators, the relator families G1--G8,
the group `KhGroup M`, and the configuration words
`x_{q_i A_0} * a_1^{(m_1)} * ⋯ * a_K^{(m_K)} * A_1 * ⋯ * A_K`
of KMS Theorem `tmm`(b).

Indexing.
* `x j S` is the letter `x_u` for `u = q_j ∏_{i ∈ S} A_i`, with `S ⊆ {0, …, K}`.
* `bigA i` is `A_i` for `i = 0, …, K`.  Glass `n : Fin K` of the machine is
  glass number `n.succ`, so it uses the letters `a n`, `a' n` and `bigA n.succ`.
* `ta n` and `ta' n` are the letters `ã_{n+1}` and `ã'_{n+1}`.
* The blocks are `M_0 = {ã_i, ã'_i, A_0}` and `M_{n+1} = {a_n, a'_n, A_{n+1}}`.

Conventions, as in the source: `u^g = g⁻¹ u g`, `[f, A] = f⁻¹ A⁻¹ f A`,
`f * A = [f, A]`, and `f * a = f⁻¹ f^{a} (f^{a⁻¹})⁻¹ f^{(a')⁻¹}`.

Machine relations (G8) are single-glass, matching `Minsky.Instr`:
* `i → Add(n); j`: `x_{q_i A_0} = x_{q_j A_0} * a_n`;
* `i, ε_n > 0 → Sub(n); j`: `x_{q_i A_0} * a_n = x_{q_j A_0}`;
* `i, ε_n = 0 → j`: `x_{q_i A_0} * A_n = x_{q_j A_0} * A_n`.
-/

namespace GroupApproximation.Full.Kharlampovich

namespace KMS

/-- The generators `L_0 ∪ L_1 ∪ L_2` of `G(M)` (KMS Sec. 4.1). -/
inductive KhGen (K N : ℕ) : Type where
  /-- `x_u` for `u = q_j ∏_{i ∈ S} A_i`. -/
  | x (j : Fin (N + 1)) (S : Finset (Fin (K + 1))) : KhGen K N
  /-- `A_i`, `i = 0, …, K`. -/
  | bigA (i : Fin (K + 1)) : KhGen K N
  /-- `a_{n+1}`. -/
  | a (n : Fin K) : KhGen K N
  /-- `a'_{n+1}`. -/
  | a' (n : Fin K) : KhGen K N
  /-- `ã_{n+1}`. -/
  | ta (n : Fin K) : KhGen K N
  /-- `ã'_{n+1}`. -/
  | ta' (n : Fin K) : KhGen K N

variable {K N : ℕ}

/-- The letters of `L_2`. -/
def KhGen.IsSmall : KhGen K N → Prop
  | .a _ => True
  | .a' _ => True
  | .ta _ => True
  | .ta' _ => True
  | .x _ _ => False
  | .bigA _ => False

/-- The block `M_i` containing a letter of `L_1 ∪ L_2`; `none` for `x`-letters. -/
def KhGen.block : KhGen K N → Option (Fin (K + 1))
  | .x _ _ => none
  | .bigA i => some i
  | .a n => some n.succ
  | .a' n => some n.succ
  | .ta _ => some 0
  | .ta' _ => some 0

/-! ## Operations in an arbitrary group -/

section Ops

variable {G H : Type*} [Group G] [Group H]

/-- Conjugation `u^g = g⁻¹ u g`. -/
def khConj (u g : G) : G := g⁻¹ * u * g

/-- The commutator `[u, v] = u⁻¹ v⁻¹ u v`, which is also `u * A` for `A`-letters. -/
def khComm (u v : G) : G := u⁻¹ * v⁻¹ * u * v

/-- The operation `f * a = f⁻¹ f^{a} (f^{a⁻¹})⁻¹ f^{(a')⁻¹}` of G8. -/
def khStar (f a a' : G) : G := f⁻¹ * khConj f a * (khConj f a⁻¹)⁻¹ * khConj f a'⁻¹

theorem map_khConj (φ : G →* H) (u g : G) : φ (khConj u g) = khConj (φ u) (φ g) := by
  simp only [khConj, map_mul, map_inv]

theorem map_khComm (φ : G →* H) (u v : G) : φ (khComm u v) = khComm (φ u) (φ v) := by
  simp only [khComm, map_mul, map_inv]

theorem map_khStar (φ : G →* H) (f a a' : G) :
    φ (khStar f a a') = khStar (φ f) (φ a) (φ a') := by
  simp only [khStar, khConj, map_mul, map_inv]

end Ops

/-! ## Letters as free group elements -/

/-- The free group element `x_{q_j ∏_{i ∈ S} A_i}`. -/
abbrev gx (j : Fin (N + 1)) (S : Finset (Fin (K + 1))) : FreeGroup (KhGen K N) :=
  FreeGroup.of (KhGen.x j S)

/-- The free group element `A_i`. -/
abbrev gA (i : Fin (K + 1)) : FreeGroup (KhGen K N) := FreeGroup.of (KhGen.bigA i)

/-- The free group element `a_{n+1}`. -/
abbrev ga (n : Fin K) : FreeGroup (KhGen K N) := FreeGroup.of (KhGen.a n)

/-- The free group element `a'_{n+1}`. -/
abbrev ga' (n : Fin K) : FreeGroup (KhGen K N) := FreeGroup.of (KhGen.a' n)

/-- The free group element `ã_{n+1}`. -/
abbrev gta (n : Fin K) : FreeGroup (KhGen K N) := FreeGroup.of (KhGen.ta n)

/-- The free group element `ã'_{n+1}`. -/
abbrev gta' (n : Fin K) : FreeGroup (KhGen K N) := FreeGroup.of (KhGen.ta' n)

/-- `t_1^{α_1 - 1} ⋯ t_K^{α_K - 1}` for `α : Fin K → Fin 3`, i.e. all products
`t_1^{ε_1} ⋯ t_K^{ε_K}` with `ε_i ∈ {-1, 0, 1}` (used in G4 and G7). -/
def zword (t : Fin K → FreeGroup (KhGen K N)) (α : Fin K → Fin 3) : FreeGroup (KhGen K N) :=
  List.foldl (fun (h : FreeGroup (KhGen K N)) (n : Fin K) ↦ h * t n ^ (((α n).val : ℤ) - 1)) 1
    (List.finRange K)

/-! ## Relator families -/

/-- G1: `H_0` and `H_1` are abelian of exponent `2`, and `H_2` is abelian. -/
def g1Relators (K N : ℕ) : Set (FreeGroup (KhGen K N)) :=
  {r | ∃ (j : Fin (N + 1)) (S : Finset (Fin (K + 1))), r = gx j S ^ 2} ∪
  {r | ∃ (j j' : Fin (N + 1)) (S S' : Finset (Fin (K + 1))), r = khComm (gx j S) (gx j' S')} ∪
  {r | ∃ i : Fin (K + 1), r = gA (N := N) i ^ 2} ∪
  {r | ∃ i i' : Fin (K + 1), r = khComm (gA (N := N) i) (gA i')} ∪
  {r | ∃ s t : KhGen K N, s.IsSmall ∧ t.IsSmall ∧ r = khComm (FreeGroup.of s) (FreeGroup.of t)}

/-- G2: letters from different blocks commute. -/
def g2Relators (K N : ℕ) : Set (FreeGroup (KhGen K N)) :=
  {r | ∃ (s t : KhGen K N) (i i' : Fin (K + 1)), s.block = some i ∧ t.block = some i' ∧
    i ≠ i' ∧ r = khComm (FreeGroup.of s) (FreeGroup.of t)}

/-- G3: `(a'_i)⁻¹` is a BR-conjoint to `a_i⁻¹` with respect to `{A_i}`:
`A_i^{a_i⁻¹} A_i⁻¹ = A_i^{(a'_i)⁻¹}` and `[A_i^{a_i^{±1}}, A_i] = 1`. -/
def g3Relators (K N : ℕ) : Set (FreeGroup (KhGen K N)) :=
  {r | ∃ n : Fin K, r = khConj (gA (N := N) n.succ) (ga n)⁻¹ * (gA n.succ)⁻¹ *
    (khConj (gA n.succ) (ga' n)⁻¹)⁻¹} ∪
  {r | ∃ n : Fin K, r = khComm (khConj (gA (N := N) n.succ) (ga n)) (gA n.succ)} ∪
  {r | ∃ n : Fin K, r = khComm (khConj (gA (N := N) n.succ) (ga n)⁻¹) (gA n.succ)}

/-- G4: the `(ã'_i)⁻¹` are BR-conjoints to the `ã_i⁻¹` with respect to `{A_0}`. -/
def g4Relators (K N : ℕ) : Set (FreeGroup (KhGen K N)) :=
  {r | ∃ n : Fin K, r = khConj (gA (K := K) (N := N) 0) (gta n)⁻¹ * (gA 0)⁻¹ *
    (khConj (gA 0) (gta' n)⁻¹)⁻¹} ∪
  {r | ∃ α : Fin K → Fin 3,
    r = khComm (khConj (gA (K := K) (N := N) 0) (zword gta α)) (gA 0)}

/-- G5 a): `[x_u, A_i] = x_{u A_i}` when `A_i ∉ u`. -/
def g5aRelators (K N : ℕ) : Set (FreeGroup (KhGen K N)) :=
  {r | ∃ (j : Fin (N + 1)) (S : Finset (Fin (K + 1))) (i : Fin (K + 1)), i ∉ S ∧
    r = khComm (gx j S) (gA i) * (gx j (insert i S))⁻¹}

/-- G5 b): `x_u^{a_i} x_u⁻¹ = x_u^{a'_i}` when `A_i ∉ u`, `i ≥ 1`. -/
def g5bRelators (K N : ℕ) : Set (FreeGroup (KhGen K N)) :=
  {r | ∃ (j : Fin (N + 1)) (S : Finset (Fin (K + 1))) (n : Fin K), n.succ ∉ S ∧
    r = khConj (gx j S) (ga n) * (gx j S)⁻¹ * (khConj (gx j S) (ga' n))⁻¹}

/-- G5 c): `[x_u, z] = 1` when `A_i ∈ u` and `z ∈ M_i`. -/
def g5cRelators (K N : ℕ) : Set (FreeGroup (KhGen K N)) :=
  {r | ∃ (j : Fin (N + 1)) (S : Finset (Fin (K + 1))) (s : KhGen K N) (i : Fin (K + 1)),
    i ∈ S ∧ s.block = some i ∧ r = khComm (gx j S) (FreeGroup.of s)}

/-- G6: `x_{q_j}^{a_i} = x_{q_j}^{ã_i}` and `x_{q_j}^{a'_i} = x_{q_j}^{ã'_i}`. -/
def g6Relators (K N : ℕ) : Set (FreeGroup (KhGen K N)) :=
  {r | ∃ (j : Fin (N + 1)) (n : Fin K),
    r = khConj (gx (K := K) j ∅) (ga n) * (khConj (gx j ∅) (gta n))⁻¹} ∪
  {r | ∃ (j : Fin (N + 1)) (n : Fin K),
    r = khConj (gx (K := K) j ∅) (ga' n) * (khConj (gx j ∅) (gta' n))⁻¹}

/-- G7: `[x_u^{a_1^{ε_1} ⋯ a_K^{ε_K}}, x_v] = 1` for `ε_i ∈ {-1, 0, 1}`. -/
def g7Relators (K N : ℕ) : Set (FreeGroup (KhGen K N)) :=
  {r | ∃ (j j' : Fin (N + 1)) (S S' : Finset (Fin (K + 1))) (α : Fin K → Fin 3),
    r = khComm (khConj (gx j S) (zword ga α)) (gx j' S')}

/-- The letter `x_{q_j A_0}`. -/
abbrev gxA0 (j : Fin (N + 1)) : FreeGroup (KhGen K N) := gx j {0}

/-- G8: the relator of one numbered instruction `(i, command)`. -/
def instrRelator : Fin (N + 1) × Minsky.Instr K N → FreeGroup (KhGen K N)
  | (i, .add n j) => gxA0 i * (khStar (gxA0 j) (ga n) (ga' n))⁻¹
  | (i, .sub n j) => khStar (gxA0 i) (ga n) (ga' n) * (gxA0 j)⁻¹
  | (i, .zero n j) => khComm (gxA0 i) (gA n.succ) * (khComm (gxA0 j) (gA n.succ))⁻¹

/-- G8: the relators built from the program of `M`. -/
def machineRelators (M : Minsky.Machine K N) : Set (FreeGroup (KhGen K N)) :=
  {r | ∃ c ∈ M.prog, r = instrRelator c}

/-- All defining relators G1--G8 of `G(M)`. -/
def relators (M : Minsky.Machine K N) : Set (FreeGroup (KhGen K N)) :=
  g1Relators K N ∪ g2Relators K N ∪ g3Relators K N ∪ g4Relators K N ∪ g5aRelators K N ∪
    g5bRelators K N ∪ g5cRelators K N ∪ g6Relators K N ∪ g7Relators K N ∪ machineRelators M

/-- The group `G(M)` of KMS Sec. 4.1. -/
abbrev KhGroup (M : Minsky.Machine K N) : Type := PresentedGroup (relators M)

/-! ## Configuration words -/

/-- The word `x_{q_i A_0} * a_1^{(m_1)} * ⋯ * a_K^{(m_K)} * A_1 * ⋯ * A_K` of a
configuration `(i; m_1, …, m_K)` (KMS Theorem `tmm`(b), with all `α_i = 1`). -/
def configWord (c : Minsky.Cfg K N) : FreeGroup (KhGen K N) :=
  List.foldl (fun (h : FreeGroup (KhGen K N)) (n : Fin K) ↦ khComm h (gA n.succ))
    (List.foldl (fun (h : FreeGroup (KhGen K N)) (n : Fin K) ↦
        Nat.iterate (fun f : FreeGroup (KhGen K N) ↦ khStar f (ga n) (ga' n)) (c.glass n) h)
      (gxA0 c.state) (List.finRange K))
    (List.finRange K)

/-- The image of a configuration word in `G(M)`. -/
def configElem (M : Minsky.Machine K N) (c : Minsky.Cfg K N) : KhGroup M :=
  PresentedGroup.mk (relators M) (configWord c)

theorem mk_eq_one_of_mem_relators (M : Minsky.Machine K N) {r : FreeGroup (KhGen K N)}
    (h : r ∈ relators M) : (PresentedGroup.mk (relators M) r : KhGroup M) = 1 :=
  PresentedGroup.one_of_mem h

theorem instrRelator_mem_relators (M : Minsky.Machine K N)
    {c : Fin (N + 1) × Minsky.Instr K N} (hc : c ∈ M.prog) :
    instrRelator c ∈ relators M := by
  unfold relators
  refine Set.mem_union_right _ ?_
  show ∃ c' ∈ M.prog, instrRelator c = instrRelator c'
  exact ⟨c, hc, rfl⟩

end KMS

end GroupApproximation.Full.Kharlampovich

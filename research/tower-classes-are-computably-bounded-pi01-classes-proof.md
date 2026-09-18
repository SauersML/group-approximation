---
rg: 2
id: tower-classes-are-computably-bounded-pi01-classes-proof
kind: route
title: Level-local conditions give a computable finitely branching tree; the direction-2-to-1 steps of the covering-tower proof never use computability of the families; the language tower only needs upper bounds on the moduli
target: tower-classes-are-computably-bounded-pi01-classes
requires:
  - covering-towers-iff-effective-minimal-free-subshifts
---

**Route. COMPLETE.** This is a hand proof.
- It reuses the steps of `covering-towers-iff-effective-minimal-free-subshifts-proof`
  by number, and checks for each one which hypotheses it actually uses.
- It imports the statement of `covering-towers-iff-effective-minimal-free-subshifts`
  (ESTABLISHED) for the final equivalence.
- Notation is as in the target.

## Step 0: the moduli are finite

Let `Y` be nonempty, minimal and free.
- *`f_Y(r)`.* Fix one of the finitely many patterns `p` on `B(r)` that occur in
  `Y`, say at a point `y ∈ Y`.
  - By minimality, `y` lies in the orbit closure of every `z ∈ Y`, so `p`
    occurs in every `z ∈ Y`.
  - The open sets `U_t = {z : ∃c ∈ B(t), w_r(z,c) = p}` increase with `t` and
    cover `Y`. By compactness one `U_t` contains `Y`.
  - Take the maximum of these `t` over the finitely many `p`.
- *`R_Y(s)`.* The open sets `{z : ∃μ ∈ B(R), z(μ) ≠ z(μs)}` increase with `R`.
  They cover `Y`, because `s.z ≠ z` and `(s.z)(μ) = z(μs)`. Apply compactness.
- *Monotonicity.* If `t` satisfies the defining property of `f_Y(r)`, so does
  every `t' ≥ t`. If `R` satisfies the property defining `R_Y(s)`, so does every
  `R' ≥ R`.

## Step 1: part 1 (the class is Π⁰₁ and computably bounded)

- *Each condition is local in the levels.*
  - (C) and (K) for the index `n` mention only `L_n` and `L_{n+1}`.
  - (A_φ) for the index `n` mentions only `L_n`.
- *Each condition at a given index is decidable.* Balls `B(R)` are computable
  finite lists of normal forms, and products are computable by the solvable word
  problem. In (A_φ) the constraint `|c| ≤ R_n − φ(|s|) − |s|` forces
  `|s| ≤ R_n`, so only finitely many `s` occur, and `s ≠ 1` is decidable.
- *The tree.* A node at depth `N` is a tuple `(L_0, ..., L_N)` of nonempty sets
  `L_n ⊆ A^{B(R_n)}` that satisfies (C) and (K) for every `n < N` and (A_φ) for
  every `n ≤ N`.
  - The tree is computable and closed under prefixes.
  - The number of children of a depth-`N` node is at most `2^{|A|^{|B(R_{N+1})|}}`,
    which is computable.
- *Paths.* By locality, the infinite paths are exactly the members of `T_D`.
- *Nonemptiness.* By König's lemma, `T_D ≠ ∅` iff the tree is infinite. ∎

## Step 2: part 2 (every path gives a subshift)

Fix `L ∈ T_D`, not necessarily computable. Steps 1–5 and Lemma 1 of
`covering-towers-iff-effective-minimal-free-subshifts-proof` use only the
following:
- the inequalities `m_n ≤ R_n ≤ R_{n+1}`, `m_n → ∞` and `R_n − m_n → ∞`;
- conditions (C), (K) and (A) for the given families.

Computability of `L_n` enters only in Step 2 there, which proves the forbidden
set decidable. Re-running those steps:
- *Subshift, nonempty.* Steps 1 and 3 apply verbatim. The downward induction and
  the compactness limit are non-effective and need no computability.
- *Forbidden set.* Step 2 computes `F_n` from `L_n`, uniformly. So the forbidden
  set is decidable relative to `L`.
- *Minimal, with the modulus bound.* Step 4 is verbatim.
  - For `z, z' ∈ Y_L` and `n` with `m_n ≥ r`, the pattern `z|B(r)` occurs in
    `z'` at some `λ` with `d(g,λ) ≤ β_D(r)`, for every `g`.
  - Every pattern `p` on `B(r)` occurring in `Y_L` has the form `z|B(r)` for some
    `z ∈ Y_L`, by shift-invariance.
  - Taking `g = 1` gives `λ ∈ B(β_D(r))` with `w_r(z',λ) = p`.
  - So `f_{Y_L}(r) ≤ β_D(r)`, where `n = n(r)` is the least index with
    `m_n ≥ r`, which is computable.
- *Free, with the radius bound.* Step 5 applies with `R(s) = φ(|s|)`, for which
  (A) is literally (A_φ).
  - Choose `n` with `m_n ≥ φ(|s|) + |s|`.
  - Step 5 then yields, for every `z ∈ Y_L`, some `μ ∈ B(φ(|s|))` with
    `z(μ) ≠ z(μs)`.
  - Hence `R_{Y_L}(s) ≤ φ(|s|)`. ∎

## Step 3: part 3 (every subshift with computable bounds gives a path)

This is Step 8 of the covering-tower proof, with the upper bounds `f̄` and `φ`
in place of the exact moduli. Let `Y`, `f̄` and `φ` be as in part 3.
- *The datum is computable and admissible.* `R_n` and `m_n` are computable
  from `f̄`.
  - `m_{n+1} = R_n + f̄(R_n) ≤ R_{n+1}`.
  - `R_n ≤ R_{n+1}` and `m_n → ∞`.
  - `R_{n+1} − m_{n+1} = R_n + f̄(R_n) → ∞`.
  - `m_{n+1} ≥ R_n`.
  - `m_0 = 1 ≤ R_0 = 2`.
- *The families.* `L_n = L(Y) ∩ A^{B(R_n)}` is finite, and nonempty because
  `Y ≠ ∅`. It need not be computable.
- *(C).* Let `q ∈ L_{n+1}` and `|g| ≤ R_{n+1} − m_{n+1}`.
  - Then `|g| ≤ R_{n+1} − R_n`, because `m_{n+1} ≥ R_n`.
  - Take `h = g`, so `d(g,h) = 0 ≤ R_n − m_n`.
  - Write `q = z|B(R_{n+1})` with `z ∈ Y`.
  - By (I1), `w_{R_n}(q,g) = w_{R_n}(z,g) = w_{R_n}(g.z, 1)`, and `g.z ∈ Y`. So
    the window lies in `L_n`.
- *(K).* Let `q = z|B(R_{n+1})` with `z ∈ Y`, and `p ∈ L_n`.
  - By the definition of `f_Y` and Step 0 monotonicity, `p = w_{R_n}(z,c)` for
    some `|c| ≤ f̄(R_n) ≤ R_{n+1} − R_n`.
  - For `|μ| ≤ R_n` we have `|μc| ≤ R_{n+1}`, so `w_{R_n}(q,c) = p`.
- *(A_φ).* Let `q = z|B(R_n)` with `z ∈ Y`, `s ≠ 1` and
  `|c| ≤ R_n − φ(|s|) − |s|`.
  - Since `c.z ∈ Y` and `R_Y(s) ≤ φ(|s|)`, Step 0 monotonicity gives
    `μ ∈ B(φ(|s|))` with `(c.z)(μ) ≠ (c.z)(μs)`, that is `z(μc) ≠ z(μsc)`.
  - Both `|μc|` and `|μsc|` are at most `φ(|s|) + |s| + |c| ≤ R_n`, so
    `q(μc) ≠ q(μsc)`. ∎

## Step 4: part 4 (the split)

*First equivalence.*
- (⇐) Take `L ∈ T_D`. By part 2, `Y_L` is a nonempty minimal free subshift with
  `f_{Y_L} ≤ β_D` and `R_{Y_L}(s) ≤ φ(|s|)`, and both bounds are computable.
- (⇒) Part 3 gives `L ∈ T_{D_Y}`.

*Second equivalence.*
- (⇐) A computable `L ∈ T_D` is a margin covering tower in the sense of
  `covering-towers-iff-effective-minimal-free-subshifts`, with the function
  `R(s) = φ(|s|)`, for which (A) is (A_φ). By its Theorem (2 ⇒ 1), `G` carries a
  nonempty effectively closed minimal free subshift.
- (⇒) Let `Y` be nonempty, effectively closed, minimal and free.
  - By Steps 6 and 7 of the covering-tower proof, `L(Y)` is decidable, and `f_Y`
    and `R_Y` are computable. (Step 7's `f` and `R` coincide with `f_Y` and
    `R_Y`, because every `L(Y)`-pattern extends to a point of `Y`.)
  - Put `φ(0) = 0` and `φ(k) = max{R_Y(s) : 1 ≠ s ∈ B(k)}`, with `max ∅ = 0`.
    This is computable, because `B(k)` is a computable finite list and
    `s ≠ 1` is decidable. It is nondecreasing, and `R_Y(s) ≤ φ(|s|)`.
  - Apply part 3 with `f̄ = f_Y`. The datum `D_Y` is computable.
  - The language tower `L_n = L(Y) ∩ A^{B(R_n)}` is uniformly computable,
    because `L(Y)` is decidable. So it is a computable member of `T_{D_Y}`. ∎

## Remarks (not part of the established statement)

- The low basis and hyperimmune-free basis theorems (Jockusch–Soare 1972,
  context only, not imported) apply to computably bounded Π⁰₁ classes.
- The existence of nonempty such classes with no computable member (context
  only) shows that path selection is not automatic.

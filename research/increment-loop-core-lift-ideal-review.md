---
rg: 2
id: increment-loop-core-lift-ideal-review
kind: claim
title: Referee review of aecdf34e2f ((c) holds for the non-contracting increment-loop core Q) — PASS; the descent to Z * Z/2, the root-permutation bound m ≥ 2, the section formulas and the strict decrease of L at every vertex all check, so N_Q is the lift closure of ⟨⟨b²⟩⟩ and V_3(Q) is finitely presented; two small repairs, to the induction's bookkeeping and to the "still open" paragraph, where u and s_*^u die or change at †-letters
distinct_from:
  birget-question-via-decidable-bartholdi-mitrofanov-hosts: that is the lane node; this reviews only the core theorem added to it in aecdf34e2f, and the node itself stays OPEN for Birget.
  birget-wall-letter-tests-review: that review checks the corrected recursions of 524f38586f that this theorem builds on.
---

**ESTABLISHED (referee bh-ref-f, 2026-09-19; review of the theorem bh-birget added in aecdf34e2f).** No code
was run; every computation below was done by hand. No priority search was made. I know of no earlier result
covering this Q: it is non-contracting, and its generator a has exponential activity, since a|₁ = a|_h = a. So
neither Nekrashevych's FP2 nor Belk–Hyde–Matucci's bounded-automata theorem applies.

Notation: letters 0, 1, h; left action; sections listed at 0, 1, h; a = (0 1)(1,a,a), b = (1 h)(b,1,1).

## 1. The steps

- **Descent: correct.**
  - b² = (b², 1, 1), with trivial root permutation.
  - Sections of conjugates of b² are conjugates of b² by sections of the conjugator. So ⟨⟨b²⟩⟩ is carried into
    itself, and the wreath recursion descends to Γ = ⟨a⟩ * ⟨b | b²⟩.
- **Kernel shape: correct.**
  - a has infinite order: a² = (a, a, a²), which forces ord a = 2·ord a².
  - b and b·a^i with i ≠ 0 have nontrivial root permutation: (1 h), or (1 h)(0 1) of order 3.
  - So every nontrivial cyclically reduced element of N̄ is b a^{i_1} ⋯ b a^{i_m} with m ≥ 2 and every i_j ≠ 0.
- **Sections: correct.**
  - a^{2k} = (a^k, a^k, a^{2k}) and a^{2k+1} = (0 1)(a^k, a^{k+1}, a^{2k+1}).
  - Sections have length at most |i|, with equality only at h.
  - The only nontrivial section of b is b, at 0.
- **Strict decrease: correct.** Read w from the right at a vertex x.
  - **Every b survives.** Then each b reads 0. So a^{i_m}(x) = 0, and the m−1 ≥ 1 exponents i_1, …, i_{m−1}
    between consecutive b's are even.
    - Those powers read 0, and their sections are a^{i_j/2}.
    - The section of a^{i_m} has length at most ⌈|i_m|/2⌉.
    - So L drops by at least m − 1 ≥ 1.
  - **Some b dies.** It reads 1 or h, and contributes nothing. Every a-power contributes at most its own length,
    so L drops by at least 1.
  - The case x = h always falls here: a^{i_m} fixes h, so the last b reads h.
- **Induction and conclusion: correct, with one bookkeeping repair.**
  - Relators trivial in Γ lie in ⟨⟨b²⟩⟩.
  - A relator with cyclically reduced nontrivial image has all of its first-level sections in M by induction, so it
    lies in M by lift closure.
  - Hence N_Q = M = ⟨⟨b²⟩⟩_lift.
  - The refereed sufficiency half (235a8af31d) then gives V_3(Q) finitely presented. The refereed transfer lemma
    (ab22b01462) gives the simple host.

## 2. Repairs

1. **Induction bookkeeping.** The induction is over all relators, but L is defined only on cyclically reduced
   normal forms.
   - Define L(g) for every g ∈ Γ as the L of the cyclic reduction of g. Cyclic reduction never increases length,
     so the decrease still holds.
   - Say that M is normal, so a relator lies in M iff its cyclically reduced conjugate does.
2. **The "still open for G_1" paragraph** needs the corrected recursions (review 524f38586f).
   - u dies at every †-letter: u|_† = 1, by "Φ(a,u) = (ε,a) for a ∉ {0,1}".
   - So s_*^u = u s_* u has section s_* at †₁, not s_*^u.
   - Past the first †, only ⟨s_*⟩ persists. The two-odometer interplay of s_* and s_*^u happens only before the
     first †, and the paragraph should say so. It is marked "not done", which is correct.

## 3. What the theorem does and does not give

- **It gives the first non-contracting test case of (c).** Condition (c) holds for Q, and V_3(Q) is finitely
  presented, although Q is neither contracting nor known to be finitely presented.
- **It says nothing about hardness.** Q is an automaton group, so its word problem is easy.
- **It does not settle (c) for the full increment loop G_1**, as the node says.

---
rg: 2
id: birget-wall-letter-tests-review
kind: claim
title: Referee review of 524f38586f (Birget route, corrected tests for the wall letter 1) — PASS with repairs; the wall rule is confirmed at source, Test 2's recursions, non-contraction, dihedral head group and the ternary core Q all check, and V_3(Q) is correctly left open; but u's recursion is wrong in both tests (u has trivial sections at non-{0,1} letters), which breaks Test 1's "bounded automaton" argument, though Test 1's conclusion (contracting, so (c)) holds by a direct argument
distinct_from:
  birget-question-via-decidable-bartholdi-mitrofanov-hosts: that is the lane node under review; this checks its corrected tests of condition (c).
  birget-lift-ideal-transfer-review: that review (ab22b01462) checked the transfer lemma; this checks the corrected Tests 1 and 2.
---

**ESTABLISHED (referee bh-ref-f, 2026-09-19; review of 524f38586f by bh-birget, which supersedes the
tests in 99e3f37a25).** No code was run; the computations were done by hand. Bartholdi–Mitrofanov
(arXiv:1710.10109) §2.1 was read on 2026-09-19 via ar5iv.

## 1. The rules at source

Verbatim, from §2.1:
- **Default:** "Whenever a value of Φ𝐌 is unspecified, we take it to mean Φ𝐌(a,s)=(s,a)."
- **Wall and u-stop:** "for all g∈S∖{u} we put Φ𝐌(1,g)=(ϵ,1), and for all a∈A∖{0,1} we put Φ𝐌(a,u)=(ϵ,a)."
- **u, s_†:** "Φ𝐌(0,u)=(u,1); Φ𝐌(1,u)=(u,0)" and "Φ𝐌(0,s†)=(ϵ,†1); Φ𝐌(†1,s†)=(ϵ,0)".
- **Type I:** "Φ𝐌(0,si)=(sj,𝐢1); Φ𝐌(𝐢1,si)=(ϵ,0); Φ𝐌(𝐢1,x)=(x²,𝐢1); Φ𝐌(𝐢1,y)=(y,𝐢1)."

So the withdrawal of the old crux is correct. Letter 1 is a wall for every generator except u.

## 2. Test 2 (the increment loop): passes

Sections below are listed at 0, 1, †₁, †₂, 𝐢₁ and use the left action.

- **The recursions.** s_* = (0 𝐢₁)(s_*,1,s_*,s_*,1), s_† = (0 †₁)(1,1,1,1,s_†) and t = (†₁ †₂)(t,1,1,1,t) all
  match the rules.
- **Repair: u is wrong.** The second half of the u-stop rule gives u = (0 1)(u,u,**1,1,1**), not
  (0 1)(u,u,u,u,u). Nothing in Test 2 depends on u, so only the display needs fixing.
- **Not contracting: correct.** s_* fixes †₁ with section s_*, so s_*^k|_{†₁} = s_*^k. The generator s_* has infinite
  order, being an odometer on the digit letters, so the nucleus is infinite.
- **[s_*, t] = 1: correct.** Both stop at the first wall. Before it, s_* reads and changes only digits, and t reads
  and changes only the first marker.
- **⟨s_†, t⟩ is dihedral of order 12: correct.** Let c₁ be the first letter in {0,†₁,†₂} before the wall, and m the
  first marker after it.
  - On the six states (c₁, m), s_† and t form the alternating path C₁–B₁–A₁–A₂–B₂–C₂, where A = 0, B = †₁,
    C = †₂.
  - With no marker after c₁, they form a path of three states.
  - One further state has no such letter at all, and both generators fix it.
  - So the group is the dihedral group with (s_†t)⁶ = 1, of order 12, acting on 9 nontrivial head states.
- **The core Q on {d0 = 𝐢₁, d1 = 0, m1 = †₁}: correct.**
  - The subtree is invariant, since neither generator produces 1 or †₂.
  - a = (d0 d1)(1,a,a), b = (d1 m1)(b,1,1), a² = (a,a,a²), ab = (d0 d1 m1)(b,a,a) and
    a²b = (d1 m1)(ab,a²,a) all check.
  - (ab)³ = (a²b, ba², aba), all conjugate to a²b. The order argument then forces ab to have infinite order.
  - The pair (n, H) formulas check in both cases:
    - with k < h₀, the 1-bit b_k becomes a hole at gap k, and later holes lose one bit;
    - with h₀ ≤ k, the first hole becomes the 1-bit at index h₀, giving 2n + 2^{h₀}, and later holes gain one.
  - Self-replicating at d0: Stab(d0) ∋ a², b with a²|_{d0} = a and b|_{d0} = b, and Q acts transitively on level 1.
  - Not contracting at m1: a|_{m1} = a.
  - ([a, bab],1,1) ∈ Q: it equals the commutator [a², (bab)²], using bab = (d0 m1)(b,a,ba), (bab)² = (bab,a²,a) and
    b² = 1.
  - It is nontrivial: a·bab(d0^∞) = m1 d1 d0^∞, while bab·a(d0^∞) = d1 d1 d0^∞.
- **The open question stays open.** "Is V_3(Q) finitely presented?" is correctly left open. So is how Q sits in
  G_1. The Theorem A equivalence applies, since Q is finite-state.

## 3. Test 1 (calibration): the conclusion holds, but the argument has to be replaced

Sections below are listed at 0, 1, †₁, †₂.

- **u is wrong here too.** With the u-stop rule, u = (0 1)(u,u,1,1).
- **So K is not a bounded automaton group.** Then s^u = usu = (1 †₁)(1,u,u,1):
  - usu(1w) = †₁·u(w);
  - usu(†₁w) = 1·u(w);
  - usu(0w) = 0w.

  Because u|₀ = u|₁ = u, u has exponential activity (2^k nontrivial sections at level k). So s^u is not bounded,
  and the claim "K = ⟨s, s^u, t, t^u⟩ is a bounded automaton group" fails. So does "u|_a = u".
- **Correct replacement argument.** Let D = ⟨u, t⟩.
  - u² = t² = 1, and (ut)² = (t, utu, 1, 1), so (ut)⁴ = 1 and D is finite, of order at most 8.
  - D is closed under sections, since u| and t| lie in {u, t, 1}.
  - s = (0 †₁)(1,1,1,1) is finitary. So every word in u, s, t has all its level-1 sections in D.
  - Hence G = ⟨x,y,t,u,s⟩ is contracting, with nucleus inside D.
- **Consequence.** Nekrashevych's FP2 and the necessity half of the lift criterion then give (c), as the node says.
  The remarks t = (†₁ †₂)(t,1,1,1) (bounded) and t^u = (†₁ †₂)(1,t^u,1,1) check. The bookkeeping "x, y ∈ R" also
  checks, since x|₀ = x.

## 4. Minor

- **Deleting x and y.** Theorem A is used for G_1 as a finite-state group, but S also contains x and y, which act
  trivially with word-level section x² at 𝐢₁. Say in one line that (c) for S and for S ∖ {x, y} are equivalent:
  add x and y to R.

## 5. Repairs, in order

1. Replace u by (0 1)(u,u,1,1) in Test 1 and by (0 1)(u,u,1,1,1) in Test 2.
2. Replace Test 1's K argument with the D argument of §3.
3. Add the one-line x, y bookkeeping for Theorem A.

---
rg: 2
id: ak3-capped-stabilisation-bound-refutes-rank2-ac
kind: claim
title: The short part of the AK(3) capped component always stabilises as the cap grows, but a tower-type bound on the cap at which it stabilises would refute the Andrews–Curtis conjecture in rank 2, because a capped path multiplies the area of the generators by at most 3 per move
distinct_from:
  ak3-rank2-capped-component-at-total-length-26: that computes S_26 and S_28 and finds that the part of length at most 24 grows with the cap; this proves that the growth always stops, and that no tower-type bound on where it stops can be proved unless AC fails in rank 2
  ak3-two-tunnel-excursions-above-cap-24: that closes S_24 under excursions above the cap and finds no goal; this bounds from below, by area, how far above its length a path from a given state must go
---

**Proposed ESTABLISHED**, through `ak3-capped-stabilisation-bound-refutes-rank2-ac-proof`.
Unreviewed. It uses one published theorem as input: Lishak, *Balanced finite presentations
of the trivial group*, arXiv:1504.00418, Theorem 2.3. It is an obstruction to one kind of
proof. It proves no triviality and no non-triviality of AK(3).

## Setting

States, the moves (M1) and (M2), and the capped component S_C are those of
`ak3-rank2-capped-component-at-total-length-26`, in rank 2.

- For a state s, T_{C,L}(s) is the set of states of S_C(s) of total length ≤ L. Here S_C(s)
  is the capped component of s at cap C.
- For two states s and t in one component of the uncapped graph, the **connection cap**
  κ(s, t) is the least C such that s and t lie in one capped component S_C.
- For AK(3), write T_{C,L} = T_{C,L}(AK(3)) and T_{∞,L} for the union over C. Let σ(L)
  be the least C with T_{C,L} = T_{∞,L}.
- Every state (r_1, r_2) in these components presents the trivial group. Its **area** A(s)
  is the larger of the areas of x and y over the presentation ⟨x, y | r_1, r_2⟩. The area of
  a word is the least number of relator cells in a van Kampen diagram for it.
- E_0 = 1 and E_{k+1} = 2^{E_k} is the tower function.

## Claim

1. **Stabilisation always holds.** For every L, T_{C,L} grows with C inside the finite
   set of states of length ≤ L. So σ(L) is finite, and σ is non-decreasing in L. There is
   no infinite family of states of one length whose connection caps grow. What can grow
   is σ(L) as a function of L.
2. **Certifying stabilisation settles AK(3).** Fix L ≥ 2. AK(3) is joined to the basis
   pair (x, y) by moves (M1) and (M2) if and only if (x, y) ∈ T_{∞,L}. So take one explicit
   C with (x, y) ∉ T_{C,L}. A proof that T_{C,L} = T_{∞,L} proves that AK(3) is not
   trivial under (M1) and (M2). Conversely, if AK(3) is not trivial, such a C exists, namely
   σ(L).
   - At C = 26 and L = 24 the basis pair is absent: the minimum length is 13
     (`ak3-rank2-capped-component-at-total-length-26`).
   - That node also shows σ(24) ≥ 27, since S_28 has 2261 states of length ≤ 24 that are
     not in S_26.
3. **Area moves slowly along capped paths.** Let s and t be states in one capped
   component S_C with C ≥ 3. Then
   log_3 A(s) ≤ log_3 A(t) + 9^C, so
   κ(s, t) ≥ log_9 (log_3 A(s) − log_3 A(t)).
4. **Lishak's presentations need enormous caps.** For n ≥ 6 let P_n be the state
   (y⁻¹xyx⁻², a'_n). Here Lishak's relator a_n is a word in x, y, t. The word a'_n is the
   cyclic reduction of the word obtained from a_n by replacing y with xt, and then
   renaming t as y. Then P_n presents the trivial group, has total length at most
   5 + 200 · 2ⁿ, and satisfies A(P_n) > E_{n−1} / (1 + 100 · 2ⁿ).
   - So a path of moves (M1) and (M2) from P_n to the basis pair must pass through total
     length at least E_{n−3}/4.
   - The same holds for a path to AK(3), up to a constant that does not depend on n.
   - For n ≥ 8 this exceeds E_4 = 65536 and every fixed tower of the length of P_n, as n
     grows.
5. **The obstruction.** Suppose that for some k and L_0, σ(L) ≤ E_k(L) for all L ≥ L_0.
   Then AK(3) is not trivial under (M1) and (M2), or some P_n is not. Either way, some
   balanced presentation of the trivial group on two generators is not trivial under
   (M1) and (M2). Each move (M1) or (M2) is a composite of AC moves and automorphisms, but
   the converse is not claimed. So this conclusion is about the moves (M1) and (M2), and
   item 6 gives the AC version.
6. **The same holds for Andrews–Curtis moves on words.** Take states to be pairs of freely
   reduced words, with the moves (AC1)–(AC3), and optionally the automorphisms of F_2, and
   define σ^AC in the same way. A tower-type bound on σ^AC, for all large L, refutes the
   Andrews–Curtis conjecture in rank 2: AK(3) or some P_n is then a counterexample.

## What it rules out

- A proof of item 2's kind at the caps computed so far. Showing that the length-≤24 part
  stops growing after cap 26 or 28 is not a smaller problem than AK(3) itself. It is the
  non-triviality of AK(3) under (M1) and (M2).
- Any strategy that bounds the cap needed to join a short state to AK(3) by an elementary
  function of its length, or by any fixed tower. For the caps of (M1) and (M2), such a
  bound would show that some two-generator presentation of the trivial group is not
  trivial under these moves (item 5). For caps of AC moves on words, it would disprove the
  conjecture in rank 2 (item 6).
- The inference "the short part of S_C changes less and less, so it has stabilised". The
  counts 4036 at caps 25–26 and 2261 at caps 27–28 are compatible with new states
  appearing at caps of tower size, if AK(3) is trivial.

## Not claimed

- That any P_n is trivial under (M1) and (M2), or under AC moves. Lishak's theorem counts
  Tietze moves, which include adding and deleting a generator.
- That the moves (M1) and (M2), with one-letter conjugators, give the same equivalence on
  cyclic words as the AC moves on words. Item 6 is stated for AC moves directly.
- Any bound on σ for the class of AK(3) when AK(3) is not trivial.
- A lower bound for small n. At n = 6 item 4 gives only 4.

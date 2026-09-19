---
rg: 2
id: ak3-capped-stabilisation-bound-refutes-rank2-ac-proof
kind: route
title: Each capped move multiplies the area of the generators by at most 3, a shortest capped path has fewer than 9^C moves, and Lishak's two-generator presentations have area above a tower
target: ak3-capped-stabilisation-bound-refutes-rank2-ac
requires: []
---

Notation is that of the claim. Areas are taken over presentations of the trivial group. So
every word has an area, and the area is subadditive: Area(uv) ≤ Area(u) + Area(v).

## Item 1

- T_{C,L} ⊂ T_{C+1,L}, since a capped move at cap C is a capped move at cap C + 1.
- Every T_{C,L} lies in the finite set of states of length ≤ L.
- So the chain is eventually constant, and its final value is T_{∞,L}. Hence σ(L) is finite.
- If T_{C,L'} = T_{∞,L'} and L ≤ L', then T_{C,L} = T_{C,L'} ∩ {length ≤ L} = T_{∞,L}.
  So σ(L) ≤ σ(L').

## Item 2

The basis pair has length 2. If AK(3) is joined to it by moves (M1) and (M2), then some
path does it inside some cap C. Then (x, y) ∈ T_{C,L} ⊂ T_{∞,L} for every L ≥ 2. The converse
holds by the definition of T_{∞,L}.

Now take C with (x, y) ∉ T_{C,L}. If T_{C,L} = T_{∞,L}, then (x, y) ∉ T_{∞,L}, so AK(3) is
not trivial. If AK(3) is not trivial, then C = σ(L) works, by item 1.

## Item 3: one move changes the area by a factor of at most 3

For a state s = (r_1, r_2), write Area_s for the area over ⟨x, y | r_1, r_2⟩. Put
A(s) = max(Area_s(x), Area_s(y)). Then Area_s(w) ≤ |w| · A(s) for every word w, by
subadditivity. Inverse letters have the same area.

**(a) Symmetries.** These are swapping the entries, rotating or inverting an entry, and
the signed permutations of the generators.
- Rotating or inverting an entry does not change which cyclic words label cells. Swapping
  the entries does not either.
- A signed permutation π of the generators carries a diagram for w over s to a diagram for
  π(w) over π(s) with the same number of cells. It permutes {x^{±1}, y^{±1}}.
- So A is a function of the class of s, and a path in the graph of classes lifts to a path
  of pairs in which each step is a move followed by a symmetry.

**(b) (M1).** Let s′ = (u″, v), where u″ is the cyclic reduction of u′ g v′^ε g⁻¹. Here u′
and v′ are rotations of u and v, and g is empty or one letter.
- In F_2, u″ is conjugate to (c u c⁻¹) · (d v d⁻¹)^{±1} for some words c and d. So a cell
  labelled u″ can be replaced by two cells of s. This gives Area_s(w) ≤ 2 Area_{s′}(w).
- Also u is conjugate to u″ · (d′ v d′⁻¹)^{∓1} for some word d′. So
  Area_{s′}(w) ≤ 2 Area_s(w).

Hence A(s′) ≤ 2 A(s) and A(s) ≤ 2 A(s′).

**(c) (M2).** Let s′ = (φ(r_1), φ(r_2)) up to cyclic reduction, where φ is a Whitehead
automorphism of the second kind.
- Apply φ to an equality w = ∏ g_i r_{j_i}^{±1} g_i⁻¹ in F_2. It gives
  φ(w) = ∏ φ(g_i) φ(r_{j_i})^{±1} φ(g_i)⁻¹. So Area_{s′}(φ(w)) ≤ Area_s(w).
- Then Area_{s′}(x) = Area_{s′}(φ(φ⁻¹(x))) ≤ Area_s(φ⁻¹(x)) ≤ |φ⁻¹(x)| · A(s), and the same
  holds for y.
- φ⁻¹ is again a Whitehead automorphism of the second kind. Such an automorphism sends each
  generator to one of g, ga, a⁻¹g or a⁻¹ga, where a is a letter. So |φ⁻¹(x)| ≤ 3 and
  |φ⁻¹(y)| ≤ 3.

Hence A(s′) ≤ 3 A(s), and by symmetry (φ⁻¹ is also a move (M2)) A(s) ≤ 3 A(s′).

**(d) Length of a shortest capped path.** A shortest path in the graph of classes visits
each class once. A class of length ≤ C has an ordered representative pair of cyclically
reduced words of lengths a, b ≥ 1 with a + b ≤ C. There are at most 4 · 3^{a−1} words of
length a. So the number of classes is at most

  Σ_{n=2}^{C} (n − 1) · 16 · 3^{n−2} ≤ 16 (C − 1) · 3^{C−1} / 2 = 8 (C − 1) 3^{C−1} < 9^C,

using Σ_{n≤C} 3^{n−2} ≤ 3^{C−1}/2. So a shortest path in S_C between s and t has
N < 9^C moves.

**(e) Conclusion.** By (a)–(c), A changes by a factor of at most 3 per move of a lifted
path. So A(s) ≤ 3^N A(t) < 3^{9^C} A(t), that is, log_3 A(s) − log_3 A(t) < 9^C. Taking C =
κ(s, t) gives κ(s, t) > log_9 (log_3 A(s) − log_3 A(t)) whenever the right side is defined.
The hypothesis C ≥ 3 is not needed for (d). It is kept in the claim only for safety of the
count.

## Item 4: Lishak's presentations

Lishak (arXiv:1504.00418, Theorem 2.3 and its proof, which uses n > 5) considers
μ_n = ⟨x, y, t | y⁻¹xyx⁻², xty⁻¹, a_n⟩. This presents the trivial group, and
l(a_n) < 100 · 2ⁿ. He proves Area_{μ_n}(x) > E_{n−1}.

Let μ′_n = ⟨x, t | ρ_1, ρ_2⟩, where ρ_1 = t⁻¹xtx⁻² and ρ_2 is a_n with y replaced by xt.
Note that ρ_1 is y⁻¹xyx⁻² with y replaced by xt, freely reduced.
- A diagram over μ′_n becomes one over μ_n. Replace each cell labelled ρ_j by a cell
  labelled the original relator, together with one cell xty⁻¹ for each occurrence of y in
  it. This needs at most 1 + l(a_n) ≤ 1 + 100 · 2ⁿ cells of μ_n per cell of μ′_n, and the
  boundary word x contains no y.
- So Area_{μ′_n}(x) ≥ Area_{μ_n}(x) / (1 + 100 · 2ⁿ) > E_{n−1} / (1 + 100 · 2ⁿ).

Rename t as y. Cyclic reduction of ρ_2 changes no area. This gives the state P_n, with
A(P_n) ≥ Area(x) > E_{n−1} / (1 + 100 · 2ⁿ) and length at most 5 + 2 · 100 · 2ⁿ.

The bound, for n ≥ 6:
- log_3 E_{n−1} = E_{n−2} log_3 2 ≥ 0.63 E_{n−2}.
- log_3 (1 + 100 · 2ⁿ) ≤ 4.3 + 0.64 n.
- E_{n−2} ≥ E_4 = 65536. So log_3 A(P_n) ≥ E_{n−2}/2.
- By item 3 with t the basis pair (A = 1), κ ≥ log_9 (E_{n−2}/2) = (E_{n−3} − 1) log_9 2.
  Since log_9 2 > 0.315 and E_{n−3} ≥ 16, this is at least E_{n−3}/4.
- For AK(3) in place of the basis pair, subtract the constant log_3 A(AK(3)) inside the
  logarithm. A(AK(3)) is finite, because AK(3) presents the trivial group.

Let L_n = |P_n| ≤ 2^{n+8}. Then n ≥ log_2 L_n − 8, so κ ≥ E_{⌈log_2 L_n⌉ − 11} / 4. For each
fixed k this exceeds E_k(L_n) for all large n.

## Item 5

Suppose σ(L) ≤ E_k(L) for all L ≥ L_0, and suppose that AK(3) and every P_n with n ≥ n_0
are trivial under (M1) and (M2). Then P_n lies in the component of AK(3). So
κ(P_n, AK(3)) ≤ σ(L_n) ≤ E_k(L_n) for large n. This contradicts item 4.

## Item 6

Run items 1–5 in the graph whose states are pairs of freely reduced words, with the moves
(AC1)–(AC3), optionally with Whitehead automorphisms.
- (AC3) and (AC2) do not change areas.
- (AC1) changes them by a factor of at most 2, as in (b).
- Automorphisms change them by a factor of at most 3, as in (c).
- The count of (d) holds for pairs of nonempty freely reduced words. A relator of a
  two-relator presentation of the trivial group on two generators is never empty.

A pair that is not trivial under the larger set of moves (with automorphisms) is not
trivial under (AC1)–(AC3) alone. So in either version, the conclusion of item 5 produces a
counterexample to the Andrews–Curtis conjecture in rank 2.

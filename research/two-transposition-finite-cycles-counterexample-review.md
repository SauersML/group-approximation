---
rg: 2
id: two-transposition-finite-cycles-counterexample-review
kind: claim
title: Referee review of 82aa08a416 (refutation of (P2)) — PASS; τ_{1(12),0(4)}·τ_{0(2),1(4)} has only finite cycles, of every even length 2S (orbit graph checked explicitly, including the worked path from 24, negative integers and {0,1}); infinite order is Bardakov–Iskra's Theorem 1.2(1) (equal residues 0 and 1 after writing τ_{1(12),0(4)} = τ_{0(4),1(12)}, ratios 1/2 ≠ 1/3); Lemmas T and S, used for the equivalent forms, also check
distinct_from:
  two-transposition-product-finite-cycles-infinite-order: that is the lane counterexample under review; this checks it explicitly.
  two-class-transposition-products-with-finite-cycles-are-periodic: that is the crux node marked REFUTED; this confirms the refutation and its Lemmas T and S.
---

**ESTABLISHED (referee bh-ref-e, 2026-09-19; review of the lane nodes by bh-p2, landed in 82aa08a416).** No priority
claimed.
- **Read at source:** both nodes on origin/main; Bardakov–Iskra, arXiv:2504.08595, abstract and arXiv HTML
  (Theorem 1.2).
- **No code was run.** Every integer check below is by hand.

## 1. The maps

- `a = τ_{0(2),1(4)}`: `2k ↦ 1 + 4k` and `1 + 4k ↦ 2k`, and it fixes `3(4)`.
- `b = τ_{1(12),0(4)}`: `4k ↦ 1 + 12k` and `1 + 12k ↦ 4k`, and it fixes everything else.
- Both pairs of classes are disjoint. The formulas in the node match.

## 2. The cycle structure

**Chains from `e ≡ 0 (4)`, `e = 2^α 3^β u`.** Correct.
- **b-then-a.** Since `12 | 3e`, we have `3e + 1 ≡ 1 (12)` and `≡ 1 (4)`, and `a` sends it to
  `3e/2 = 2^(α−1) 3^(β+1) u`. The path stops when `α − 1 = 1`, since then `3e/2 ≡ 2 (4)`, which `b` fixes.
- **a-then-b.** `2e + 1 ≡ 1 (4)`, and it is `≡ 1 (12)` iff `6 | e`. `b` then sends it to `2e/3 ≡ 0 (4)`. The path
  stops when `β = 0`.
- **The count.** Both moves preserve `u` and `α + β = S`. So there are `S` even vertices
  (`2^(α′) 3^(S−α′) u`, `1 ≤ α′ ≤ S`) and `S` odd vertices, for `2S` in all.

**Worked path from `24`.** `54 → 109 → 36 → 73 → 24 → 49 → 16 → 33`.
- `109 ≡ 1 (12)`, `73 ≡ 1 (12)` and `49 ≡ 1 (12)`.
- The endpoints are `54 ≡ 2 (4)`, fixed by `b`, and `33 ≡ 9 (12)`, fixed by `b`.
- That is 8 vertices, so `S = 4`.

**Negative check.** `e = −4` gives `−6 – −11 – −4 – −7`.
- `−11 ≡ 1 (12)`, `−7 ≡ 5 (12)`, and `−6 ≡ 2 (4)`.
- That is 4 vertices, so `S = 2`.

**The remaining residues.** Correct.
- `3(4)` is fixed.
- `n ≡ 2 (4)` with `3 ∤ n` gives the 2-vertex path `{n, 2n + 1}`, since `2n + 1 ≢ 1 (12)`. This is the case `S = 1`.
- `n ≡ 2 (4)` with `3 | n` is a chain endpoint.
- `1(4)` points are odd chain vertices.
- `{0, 1}` is a 2-cycle of the graph, since `a` and `b` both swap it. There `g = id`.

**Conclusion.**
- Each vertex has at most one edge of each label, so the components are finite paths or cycles, and `g` acts as a
  `2S`-cycle on a `2S`-vertex path.
- Cycle lengths `2S`, for every `S ≥ 1`, occur: `2^S` for `S ≥ 2`, and `2u` for `S = 1`.
- So `g` has only finite cycles and infinite order. (P2) is false.

## 3. Credit for infinite order: correct and now confirmed at source

- **Theorem 1.2(1) of Bardakov–Iskra, arXiv:2504.08595, verbatim.** `ord(τ_{l(m₁),r(m₂)} · τ_{l(m₃),r(m₄)}) = ∞`
  when `m₁/m₂ ≠ m₃/m₄`.
- **Why it covers this pair.** Write `b = τ_{0(4),1(12)}`, since class transpositions are symmetric. Then
  `a = τ_{0(2),1(4)}` and `b` have equal residues `l = 0` and `r = 1`, with ratios `2/4 = 1/2 ≠ 1/3 = 4/12`.
- The order of the product does not depend on the order of the factors.
- The node's "read from the abstract and HTML, not verbatim" can now cite the theorem verbatim. What is new in the
  node is only the finiteness of every cycle, which is correctly credited that way.

## 4. The equivalent forms

- **Lemma S.** Correct. A point of `C ∖ σ^k(C)` on a cycle of length `ℓ` would lie in `σ^k(C)`.
- **Lemma T.** Correct. It uses Kohl's tame characterization, and positive slopes make a class-fixing affine bijection
  a translation.
- **Consequences.** `g` is wild, so "every wild product has an infinite cycle" is false. (P2)′ is false too, because
  it would give an infinite cycle via Lemma S.

## Verdict

**PASS.**
- The refutation is explicit and correct.
- Infinite order is Bardakov–Iskra's Theorem 1.2(1), confirmed at source.
- The crux node is rightly marked REFUTED.
- No repairs, except upgrading the Bardakov–Iskra citation to the verbatim theorem.

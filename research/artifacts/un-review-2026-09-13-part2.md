# UN review, part 2: simple rings are stably finite iff the unit is not paradoxical

Verifier `un-verify` (UN swarm), 2026-09-13. Subject: lane `un-middle`, landing `4db95cef51`, artifact
`research/artifacts/un-middle-stable-paradox-threshold-2026-09-13.md` §3. Tip at review: `32d340ab71`.

| item | node | verdict |
|---|---|---|
| (2) | `simple-ring-stably-finite-iff-unit-not-paradoxical` (+ `-proof`) | PASS |
| (2′) | `kmp-tarski-theorem-preordered-monoids` (+ `-citation`) | PASS (verbatim) |

No false establishment.

## 1. The KMP import, checked verbatim

Source: arXiv:2502.17190v3 [math.OA], 28 Jul 2026 (Kwaśniewski–Meyer–Prasad), fetched 2026-09-13 and read from the PDF
text layer (`pdftotext -layout`). The header line reads "arXiv:2502.17190v3 [math.OA] 28 Jul 2026".

- **Definition 2.6:** "If (n + 1)x ≤ ny for some n ≥ 1, we call x stably dominated by y and write x <s y (see [56,
  Definition 2.2]). An element x ∈ S \ {0} is paradoxical if x <s x. The preordered monoid S is almost unperforated if
  x <s y implies x ≤ y for all x, y ∈ S." This matches the citation node.
- **Definition 2.9:** "A state on an ordered abelian monoid S is an additive and order-preserving map ν : S → [0, ∞]
  with ν(0) = 0 or, equivalently, ν ̸≡ ∞." This matches. Remark 2.10 transfers states to preordered monoids, as the
  node says.
- **Corollary 2.16 (Tarski's Theorem):** "In any preordered abelian monoid S, an element y ∈ S \ {0} is not
  paradoxical if and only if there is a state ν : S → [0, ∞] with ν(y) = 1." This matches. It is proved by applying
  Theorem 2.14 to x = y, and Remark 2.17 gives the second proof via injectivity of [0, ∞]. Both are as the node says.
- **Applicability:** `V(R)` with the algebraic preorder `x ≤ y ⟺ y = x + z` is a preordered abelian monoid (the
  preorder is translation invariant), so Corollary 2.16 applies to `y = [R] ≠ 0` whenever `R ≠ 0`.

## 2. Re-derivation of the equivalence

Let `R ≠ 0` be a simple unital ring. Countability is not used.
- **(b) ⟺ (c).** This is Corollary 2.16 at `y = [R]`. KMP's "paradoxical" is exactly the claim's
  `(n+1)[R] ≤ n[R]` for some `n ≥ 1`.
- **(a) ⇒ (b), contrapositive.** Suppose `(n+1)[R] ≤ n[R]`, i.e. `R^n ≅ R^{n+1} ⊕ Q = R^n ⊕ (R ⊕ Q)`. Take `s` as the
  inclusion of the first summand followed by the inverse isomorphism, and `t` as the isomorphism followed by the
  projection. In `End(R^n) = M_n(R)` this gives `ts = 1`, and `1 − st` projects onto `P = R ⊕ Q ≠ 0`, so `st ≠ 1`.
  So `M_n(R)` is not directly finite.
- **(b) ⇒ (a), contrapositive.** Suppose `M_n(R)` is not directly finite, with `ts = 1 ≠ st`.
  - Then `R^n = stR^n ⊕ (1−st)R^n`, and `stR^n ≅ R^n` via `s` and `t`, so `R^n ≅ R^n ⊕ P` with `P ≠ 0` f.g.
    projective.
  - The trace ideal `T(P) = {Σ f_i(p_i) : f_i ∈ Hom_R(P, R)}` is a two-sided ideal: `r f(p) = (rf)(p)` and
    `f(p) r = f(pr)`. It is nonzero because `P ⊆ R^n` has a nonzero coordinate functional, so it equals `R`.
  - So `1 = Σ_{i≤k} f_i(p_i)`. The right-linear map `P^k → R`, `(q_i) ↦ Σ f_i(q_i)`, has image a right submodule
    containing `1`, so it is onto, and it splits because `R_R` is projective. Hence `P^k ≅ R ⊕ Q′`.
  - Substituting `R^n ≅ R^n ⊕ P` into itself `k` times gives `R^n ≅ R^n ⊕ P^k ≅ R^n ⊕ R ⊕ Q′`, i.e. `(n+1)[R] ≤ n[R]`.
- **Levels.** Both contrapositive arguments keep the same `n`. So `{n : (n+1)[R] ≤ n[R]} = {n : M_n(R) not directly
  finite}`, and their minima `p(R)` agree, as the claim states.

**Model tests.**
- `L_k(1,2)`: `R ≅ R^2`, so `2[R] ≤ [R]`, `p = 1`, and `R` is not directly finite. Consistent.
- Pestov ring `LC(X,F_q) ⋊ Z`: the normalized matricial rank from its ultraproduct embedding gives a state with value 1
  at `[R]`, and the ring is stably finite. Consistent.
- A field: `V(k) = N`, with no paradox and stable finiteness. Consistent.

## 3. Display check

Recomputed each displayed formula in the claim and route:
- `p(R) = min{n : (n+1)[R] ≤ n[R]} = min{n : M_n(R) not directly finite}`;
- `R^n ≅ R^n ⊕ (R ⊕ Q)`;
- `1 = Σ f_i(p_i)` with `P^k → R` onto and split;
- `R^n ≅ R^n ⊕ P^k ≅ R^n ⊕ R ⊕ Q′`.

The claim's closing sentence is consistent with the ring theorem: not stably finite means `p(R) < ∞`, and then
`EL_N(R)` has full MF radical for `N ≥ 2p(R)`.

## 4. Subsumption scan (untruncated)

Scanned every `research/*.md` claim node at `origin/main`:
- 540 claims matching stably finite / paradoxical / Tarski / directly finite / `V(R)` / Dedekind infinite;
- targeted co-occurrence greps: "stably finite" with state/paradox/Tarski (≈190 claims), and "directly finite" with
  simple and `V(R)`/projective (6 claims).

Findings:
- **No older ESTABLISHED claim states this ring-level equivalence.** The C*- and groupoid-level analogues are distinct
  statements, and the item (2) claim names the KMP one in `distinct_from`:
  - `kmp-plain-paradox-groupoid-dichotomy`;
  - `rainone-sims-type-semigroup-dichotomy`;
  - `quasitrace-iff-not-stably-properly-infinite`.
- **Consumer:** `mf-elementary-groups-force-stably-finite-simple-rings` (un-converse, 417904a22b) already cites it in
  `distinct_from` as the ring-level equivalence behind its group-level statement.
- **Nothing refutes the claim or an open neighbour.**

**Duplication note for the reconciler.** The group-level threshold theorem appears in four places, with the same
content up to hypothesis equivalence:
- un-middle `paradoxical-ring-el-n-full-mf-radical-from-twice-level`, hypothesis `(n+1)[R] ≤ n[R]`;
- un-paradox `stably-infinite-ring-elementary-groups-have-no-mf-quotient`, hypothesis `2n[1] ≤ n[1]`;
- un-converse `full-defect-in-m-by-m-kills-mf-quotients-of-el-2m`;
- item 1 of un-converse `mf-elementary-groups-force-stably-finite-simple-rings`, the simple case.

The hypotheses agree at the same `n`:
- `(n+1)x ≤ nx` implies `(n+k)x ≤ nx` for every `k` (KMP Remark 2.7), in particular `2nx ≤ nx`;
- conversely `(n+1)x ≤ 2nx ≤ nx` for `n ≥ 1`;
- and both are equivalent to a properly infinite unit in `M_n(R)` (un-paradox Lemma 1).

These are reviewed separately in part 3.

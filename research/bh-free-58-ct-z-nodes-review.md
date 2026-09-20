---
rg: 2
id: bh-free-58-ct-z-nodes-review
kind: claim
title: Referee review of four bh-free-58 CT(Z) nodes (c91baed93, 1c4a8a43c, 99e1c5dc3, 4f611e3b3) — all PASS; repairs are small (symmetric generating sets for the positive-ray bounds, the N_0-invariance line for orbit minima, the promise form of the torsion-case conjugacy algorithm, and the profinite completion and scope of the coarse-action barrier)
distinct_from:
  ct-p-z-positive-ray-torsion-and-finiteness-are-decidable: lane node c91baed93 under review here.
  ct-z-orbit-transversal-counterexamples-need-unbounded-orbits: lane node 1c4a8a43c under review here.
  ct-z-finite-subgroups-are-classified-by-stabilizer-sets: lane node 99e1c5dc3 under review here.
  ct-z-21-74a-reductions-must-move-coarse-components: lane node 4f611e3b3 under review here.
---

**ESTABLISHED (referee bh-ref-d, 2026-09-19; review of four lane nodes by bh-free-58, listed as
unreviewed in its hand-off ce7ab8f74).** No priority claimed. Read on origin/main:
- the four nodes;
- the input theorem `periodic-k-graph-subgroups-with-ray-cocycle-are-finite`, with its proof checked;
- `ct-p-z-is-a-one-vertex-k-graph-full-group` (referee PASS, 09-18);
- the Kourovka Notebook texts of 20.44, 21.73 and 21.74, from the 21st-issue LaTeX source (arXiv
  1401.0300v46) as extracted by lane bh-kourovka. All three match the nodes' usage.

## c91baed93 (`ct-p-z-positive-ray-torsion-and-finiteness-are-decidable`): PASS

- **The input theorem.** Its proof checks.
  - Heights change by at most `K` per step, so `ht(m) > KC` gives more than `C` record times, and
    pigeonhole finds two in one degree-`E` cylinder.
  - Between record times every intermediate cylinder has degree `≥ E ≥ D·1`, so each step acts as a
    single piece. With `v ≥ 0` the return is a proper subcylinder, and the contraction lemma applies.
- **The constants.** `n = D + 2B‖v‖_∞ = L + B‖v‖_∞`. The number of cylinders of degrees `n·1 + κv`,
  `|κ| ≤ B`, is at most `(2B+1) m_(n·1+Bv)`, because `v ≥ 0` makes `κ = B` the largest. So
  `N(S)` is right.
- **Items 1–3.** They follow: the exponent of `Sym(N)`, powering of rcwa tables, and ball growth
  against `N(S)!`, using the decidable word problem.
- **Repair.** The input theorem fixes a **symmetric** generating set. So `D` and `K` in the bound must
  range over the tables of `S ∪ S^(-1)`, and for item 2 over `g` and `g^(-1)`. Say so.

## 1c4a8a43c (`ct-z-orbit-transversal-counterexamples-need-unbounded-orbits`): PASS

- **Step 1.** An affine piece `(an+b)/c` with `a, c > 0` is the identity or has at most one fixed
  point.
- **Step 2.** An orbit of at most `s` points has Schreier diameter `≤ s − 1`. So the criterion "the
  radius-`s` ball has `≤ s` points and is `S`-closed" is exact. It is decided by equalities among words
  of length `≤ s + 1`, i.e. by membership in `Fix(w'^(-1)w)` with `|w'^(-1)w| ≤ 2s + 2`.
- **Step 3.** The counting checks.
- **Repair.** Justify "their minima in `N_0` are at most `N`". Every class transposition
  `r_1 + t m_1 ↔ r_2 + t m_2`, with `0 ≤ r_i < m_i`, preserves the sign of `t`, so `CT(Z)` preserves
  `N_0`. An orbit through a point of `[1, N]` therefore has its minimum in `[0, N]`. Also mark item
  (iii), the Terras–Everett remark, heuristic.

## 99e1c5dc3 (`ct-z-finite-subgroups-are-classified-by-stabilizer-sets`): PASS

- **Lemma A.** PASS. Positive rational slopes make `λ^k = 1` force `λ = 1`. Every fixed point is
  interior to an identity piece, so fixed sets are clopen and consist of the identity classes.
- **Lemma B.** PASS, by box splitting.
- **Lemma C.** PASS. The greedy transversal's pieces `U_j ∖ W·Y_(j−1)` have pairwise disjoint
  translates, and `W·Y_j ⊇ U_j`.
- **Item 1.**
  - `N_F(K)/K` acts freely on the stratum `X_K`.
  - `(fK, y) ↦ ρ̂(f)y` is a bijection: if `gy = y′` with both stabilizers equal to `K`, then
    `g ∈ N(K)`, and the transversal forces `y = y′` and `g ∈ K`.
  - `ĉ` is well defined, equivariant, piecewise canonical and preserves `Z`.
  - Membership in `CT_P(Z)` uses item 3 of `ct-p-z-is-a-one-vertex-k-graph-full-group`, which has a
    referee PASS.
- **Item 2.** PASS. The order is the lcm of the cycle lengths, so equal cycle-length sets give equal
  orders and item 1 applies with `F = Z/n`. The realization in `V` by 2-adic boxes checks.
- **Item 3 is a promise algorithm.** It needs to be told *which* input has finite order; the search for
  `ord(g)` does not halt otherwise. Torsion in `CT(Z)` is decided here only on the positive-ray class
  (c91baed93). **Repair:** state item 3 and the title as "decidable for pairs in which a given element
  has finite order".
- **Discussion.** The "blind multiplication" paragraph ("multiplying by a rational coprime to the
  machine primes … is itself in `CT(Z)`") is a sketch; multiplication by a rational is not a
  permutation of `Z`. **Repair:** mark it heuristic.
- **Consistency.** The prediction that undecidable 21.73 instances have infinite order is consistent
  with the later `ct-z-conjugacy-problem-is-undecidable` (a95cb1edf, PASS).

## 4f611e3b3 (`ct-z-21-74a-reductions-must-move-coarse-components`): PASS for the principle

- **Principle.** PASS. Every part of a permuted finite partition is fixed by `ĝ^(|𝒫|!)`, so it lies in
  `𝒞(g)`, and `ĝ′` agrees with `ĝ` there.
- **Repair: the completion.** 21.74(a) allows residue classes of **any** modulus. So `Ẑ` in this node
  must be the profinite completion over every prime involved: those of `g`, of `g′`, and of the
  partition's moduli, or simply the full profinite completion of `Z`. Only then is every part clopen.
  With `Ẑ = ∏_(p∈P′) Z_p` for `g`'s own `P` the principle misses partitions with other moduli.
- **Corollaries.**
  - Corollary 2 matches the restricted positive-ray theorem (1ccef1e94) and correctly states the
    neutral-prime exception.
  - Corollary 3 cites a stated theorem.
  - Corollary 1 is correct only as a statement about the **known** counter and FRACTRAN encodings
    (71b76e027, a95cb1edf), via the thin-sets node. **Repair:** scope the title's "machine encodings
    change only thin sets" to "the known encodings", since no general theorem is proved.
- **Citations.** The Belk–Bleak Theorem 6.8 citation is recorded from another node and was not checked
  by me.

## Verdicts

| node | verdict | repair |
|---|---|---|
| c91baed93 | PASS | bounds over `S ∪ S^(-1)` |
| 1c4a8a43c | PASS | `CT(Z)` preserves `N_0`; mark (iii) heuristic |
| 99e1c5dc3 | PASS | promise form of item 3; mark the blind-multiplication paragraph heuristic |
| 4f611e3b3 | PASS (principle) | full profinite completion; scope Corollary 1 to known encodings |

---
rg: 2
id: ct-p-z-mixed-ray-nodes-review
kind: claim
title: Referee review of the two mixed-sign-ray CT_P(Z) nodes (2c9cda58b on Kourovka 19.46, 59f44f3c5 on 20.44) — both PASS; the 19.46 node's item 2 needs a corrected proof of "H infinite iff some orbit has unbounded potential" (per-orbit bounds need not be uniform; use a point with no frozen degree), and its "equivalent to" summary is a reduction, not an equivalence
distinct_from:
  ct-p-z-mixed-ray-torsion-reduces-to-sweeping-orbits: lane node 2c9cda58b under review here.
  ct-p-z-mixed-ray-frozen-tails-force-finite-orbits: lane node 59f44f3c5 under review here.
---

**ESTABLISHED (referee bh-ref-d, 2026-09-19; review of two lane nodes by bh-free-58).** No priority
claimed. Read on origin/main:
- both nodes;
- the setting of `ct-p-z-ray-cocycle-subgroups-satisfy-kourovka-20-44` (tails, tracking, reading, `C_K`,
  `M_K`);
- the Kourovka Notebook text of 19.46 and 20.44, from the LaTeX source of the 21st issue (arXiv
  1401.0300v46), as extracted by lane bh-kourovka.

**Problem texts.** Both match what the nodes use.
- **19.46 (Kohl):** "Does the group CT(Z) have finitely generated infinite periodic subgroups? (See the
  definition of CT(Z) in 17.57)."
- **20.44 (Kohl):** "…either has only finitely many orbits on Z or there is a set of representatives for
  its orbits on Z which has positive density?"

## 59f44f3c5 (`ct-p-z-mixed-ray-frozen-tails-force-finite-orbits`): PASS

- **Item 1.** If `n` is not consumable from `x`, then no prefix of any word reads the tail at `n`.
  - Each step moves it by `d(μ) − d(λ) ∈ Zv` and keeps it in `N^k`, since the new degree is `≥ d(μ)`. So
    it lands in the finite segment `Seg(n)`.
  - `σ^p y = σ^n x` gives `y = ρ + m_p z` with `0 ≤ ρ < m_p`, which is at most `A(n)` choices.
  - The argument is valid on `Ẑ` as well.
- **Item 2.**
  - For `x ≥ 0`, `z = σ^n x = ⌊x/m_n⌋ ≥ 0`, so the whole orbit lies in `N_0`.
  - Its minimum is therefore in `[0, x] ⊆ [0, jM_n)`, and distinct orbits have distinct minima. The
    count `δ_n jM_n / A(n)` and the choice `j = ⌊N/M_n⌋` then give the stated bound.
  - Negatives are symmetric, with the whole orbit lying in the negatives.
  - A transversal containing these minima has positive lower density, which is exactly 20.44's
    requirement.
- **Item 3.** Each "fixed word reads `n`" set is clopen, so compactness applies. Every infinite orbit
  reads every depth, by item 1.
- **Example.** `τ_{0(4),1(6)}` has degree change `(1,1) − (2,0) = (−1,1)`, and the two classes are
  disjoint by parity.
- **Discussion section.**
  - The measure-preservation convexity step checks. With slope `s_i` on a piece of measure `μ_i`,
    `Σ μ_i/s_i = 1`, so Jensen gives mean log-slope `≥ 0`.
  - "If every integer's anchor tail were read at the 2-adic end, every orbit would meet a fixed finite
    set" is argued in one line and not proved. **Minor repair:** mark it heuristic, or give the descent
    argument.

## 2c9cda58b (`ct-p-z-mixed-ray-torsion-reduces-to-sweeping-orbits`): PASS with repairs

- **Item 1 (finite ⟺ finitely many slopes ⟺ every point has a frozen tail).** PASS.
  - (b) ⇒ (c): an unread tail sits at `n + c(prefix, x)·v`, and `|c| ≤ B` keeps every coordinate
    `≥ D`, so induction shows it is never read.
  - (c) ⇒ (a): the `Y_n` are clopen, so finitely many cover `Ẑ`. Orbits then have at most
    `A = max A(n_i)` points, by 59f44f3c5 item 1 on `Ẑ`. The stabilizers are among the finitely many
    subgroups of index `≤ A`, so they intersect in a finite-index subgroup that acts trivially on `Ẑ`.
    That subgroup is trivial, since `H` acts faithfully on `Z ⊂ Ẑ`.
- **Item 2: the potential.** Well defined, PASS.
  - Elements of `CT_P(Z)` have positive-slope affine germs.
  - At a fixed point `x ∈ Ẑ` of a torsion element, the germ is `y ↦ x + γ^t(y − x)` with
    `γ = m_v ≠ 1`, so `t = 0`.
- **Item 2: "H infinite iff some orbit has unbounded potential".** The conclusion holds, but the proof
  has a gap.
  - The proof says "the cocycle is bounded iff every potential is bounded". The direction "every
    potential bounded ⇒ cocycle bounded" is not justified. Bounds per orbit need not be uniform across
    orbits.
  - **Repair: correct proof.**
    - If `H` is infinite, item 1 gives a point `x ∈ Ẑ` with no frozen degree.
    - Consuming the tail at `n` from `x` needs a prefix whose cocycle satisfies
      `|c| ≥ min_p (n_p − D)/|v_p|`, since reading needs some coordinate of `n + cv` below `D`.
    - `n` is arbitrary, so the potential on `H·x` is unbounded.
    - Conversely, an unbounded potential gives infinitely many slopes, so `H` is infinite by item 1.
  - The same argument shows that an orbit with unbounded potential has no frozen degree, since frozen
    points have finite orbits (59f44f3c5, item 1). So it reads every depth. The node's citation "by (c)"
    should point to that item.
- **Item 3 (hyperbolic returns).** PASS.
  - Where `r v_p > 0`, the image ball is smaller and meets `B_p`, so it lies inside it, and a contraction
    gives the fixed point. Where `r v_p < 0`, apply the same argument to the inverse. The hypothesis
    `v_p ≠ 0` is exactly what excludes the isometric case.
  - For fixed `N`, points close enough to `y*` keep their first `N` iterates in `Z(τ)`, so `h^N` is
    `A^N` there and `h^N ≠ 1`.
- **"Why pumping stops" section.**
  - The sentence "so 19.46 on the mixed ray is equivalent to this: find, or exclude…" is a reduction
    heuristic, not an equivalence proved in the node. **Repair:** say "reduces to (heuristically)".
  - The Barbieri–Kari–Salo citation (arXiv:2303.17270) was not checked by me.

## Verdicts

| node | verdict |
|---|---|
| 59f44f3c5 | PASS (one discussion sentence to mark heuristic) |
| 2c9cda58b | PASS with repairs (item 2's proof; "equivalent" → "reduces to") |

The conclusions downstream lanes use all stand: finite ⟺ frozen everywhere; infinite periodic ⇒ an orbit
with unbounded potential reading every depth; drifting returns give infinite order.

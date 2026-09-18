---
rg: 2
id: twisted-brin-thompson-type-fn-criterion
kind: claim
title: For a faithful action, the twisted Brin--Thompson group SV_G is of type F_n exactly when the action is of type (A_n), which proves the Belk--Zaremsky conjecture
distinct_from:
  twisted-brin-thompson-finite-presentation-criterion: that is Zaremsky's n = 2 case (finite presentation iff type (A)); this is the characterization for every n, whose new content is sufficiency for 3 <= n < infinity.
  twisted-brin-thompson-type-fn-implies-type-an: that is the necessity half, proved by Fournier-Facio--Wu--Zaremsky for all n; this adds the sufficiency half in the faithful case.
  stein-complex-elementary-intervals-are-grid-spheres: that is the local homotopy computation of Stein intervals; this is the global finiteness theorem it feeds.
  type-a-action-gives-boone-higman-for-subgroups: that is Zaremsky's finitely presented simple envelope for subgroups of type (A) actors; this gives type F_n simple envelopes for subgroups of type (A_n) actors.
---

**ESTABLISHED** by `twisted-bt-type-fn-interval-filtration-proof` (lane proof, 2026-09-18,
**not yet reviewed**). No priority claimed beyond the literature check below.

## The conjecture

Belk--Zaremsky, *Twisted Brin--Thompson groups*, arXiv:2001.04579 (Geom. Topol. 26 (2022)),
introduction, TeX lines 220–227 (read on MSI), for a group `G` acting faithfully on a
countable set `S`:

> "The group SV_G is of type F_n if and only if the following conditions hold:
> (1) The action of G on S has finitely many orbits of n-element subsets.
> (2) G is of type F_n.
> (3) For each 1 ≤ k < n, the stabilizer in G of any k-element subset of S is of type
> F_{n−k}."

Fournier-Facio--Wu--Zaremsky, arXiv:2603.24687v2, lines 1188–1193: "We know that the converse
of Corollary 4.18 holds for n = 1,2,∞, so a natural question is whether it holds when
3 ≤ n < ∞, i.e., whether in these cases G ↷ S being of type [A_n] is sufficient for SV_G to be
of type F_n. Indeed, this is even unknown in the faithful case, see Conjecture H of [BZ22],
where this direction is still open. Similarly one would expect G ↷ S being of type [HA_n] to
be sufficient for SV_G to be of type FP_n."

## Statement

Let `G` act faithfully on a countable set `S`, and let `n ∈ N`.
1. **(F_n)** `SV_G` is of type `F_n` iff `G ↷ S` is of type `(A_n)`: `G` is of type `F_n`,
   `Stab_G(T)` is of type `F_{n−|T|}` for every finite `T ⊆ S` with `|T| < n`, and `G` has
   finitely many orbits on `S^n`.
2. **(FP_n)** `SV_G` is of type `FP_n` iff `G ↷ S` is of type `(HA_n)`, the same conditions
   with `FP` in place of `F`.
3. **(BZ's form)** Conditions (1)–(3) of the conjecture are equivalent to type `(A_n)`, so the
   conjecture holds.
   - Type `(A_n)` gives (1)–(3) directly.
   - Conversely, (1) gives finitely many orbits on `k`-subsets for every `k ≤ n`, by
     Cameron's monotonicity theorem for infinite permutation groups (P. J. Cameron,
     Math. Z. 148 (1976); not read at source). For finite `S` this is automatic.
   - Hence (1) gives finitely many orbits on `S^n`.
4. **(Exact length)** `SV_G` is of type `F_n` but not `F_{n+1}` iff `G ↷ S` is of type
   `(A_n)` but not `(A_{n+1})`.

Only sufficiency is new, and only for `3 ≤ n < ∞`:
- necessity for all `n` is `twisted-brin-thompson-type-fn-implies-type-an` (FFWZ Cor 4.18);
- `n = 1` is BZ Theorem `thm:FinitelyGeneratedTheorem`;
- `n = 2` is `twisted-brin-thompson-finite-presentation-criterion` (Zaremsky);
- `n = ∞` is BZ with FFWZ Theorem B.

## Why the Stein complex was thought insufficient, and what fixes it

FFWZ (lines 919–927) explain that for `3 ≤ n < ∞` the action on the Stein complex does not
reveal type `F_n` "since not all simplex stabilizers have the right finiteness
properties". Brown's criterion needs `p`-cell stabilizers of type `F_{n−p}`, but a long edge
whose tree splits one cube in three colors has stabilizer commensurable to the stabilizer of
a 3-element set. Under `(A_n)` that is only of type `F_{n−3}`.

The proof does not use simplices as cells. It filters the Stein complex by interval length,
as BZ do to prove contractibility. Every filtration quotient then splits over elementary
intervals, and `stein-complex-elementary-intervals-are-grid-spheres` shows:
- a non-grid interval contributes nothing;
- a grid interval with `e` colors in total contributes one copy of `Z`, in homological degree
  `e`.

The stabilizer of a grid interval is commensurable to `∏ Stab_G(C_i)` with `|C_i| ≤ e`
(BZ Proposition `prop:stabs`). So it is of type `F_{n−e}`, which is exactly what a
homological Brown criterion for filtered complexes needs. The proof then gets `FP_n`, and
`F_n` follows because `SV_G` is already finitely presented.

## Scope

- **Non-faithful actions stay open.** FFWZ conjecture the same characterization for
  abstract twisted Brin--Thompson groups. The proof uses the connectivity of the Stein
  complex sublevel sets (FFWZ Proposition 4.8(ii)), which is proved only for faithful
  actions.
- **Literature check (2026-09-18).** FFWZ v2 records the problem as open. One web search
  ("twisted Brin–Thompson type F_n ... 2026") found no later resolution. No MathSciNet
  search was done.

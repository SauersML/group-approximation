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

**ESTABLISHED** by `twisted-bt-type-fn-interval-filtration-proof` (lane proof, 2026-09-18).
Referee a (proof gaps): **PASS**,
`research/artifacts/gq-referee-a-twisted-brin-thompson-type-fn-criterion.md` (16bd2d9b5),
with nits N1–N6 applied. Referee c (independent second proof-gap pass): **PASS**,
`research/artifacts/gq-referee-c-twisted-brin-thompson-type-fn-criterion.md` (b74ee10f0), at
version 329a4461c. A citation pass (gq-referee-b) is pending, for FFWZ Cor 4.18, Cameron, and
the wreath-product equivalence. No priority claimed beyond the literature check below.

## The conjecture, and what BZ proved

BZ prove a sufficient condition, not the characterization. Their Theorem
`thm:FinitenessTheorem` (TeX l.178–184) says: "Let G be an oligomorphic group of permutations
of a countable set S. Let n ∈ N ∪ {∞}, and suppose that (1) G is of type F_n, and (2) The
stabilizer in G of every finite subset of S is of type F_n. Then SV_G is of type F_n as well."
- That theorem asks for finitely many orbits on `k`-subsets for **every** `k`, and for every
  finite-set stabilizer to be of type `F_n`.
- They then write (l.218): "Theorem [FinitenessTheorem] does not appear to be sharp. We
  conjecture the following precise characterization".
- The conjecture weakens both hypotheses to the graded ones below. It is this conjecture that
  FFWZ record as open.

Belk--Zaremsky, *Twisted Brin--Thompson groups*, arXiv:2001.04579 (Geom. Topol. 26 (2022)),
introduction, TeX lines 220–227 (read on MSI), for a group `G` acting faithfully on a
countable set `S` (the conjecture itself):

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

## Lesson for general BH

**The twisted Brin--Thompson route loses no finiteness.** For faithful actions, FFWZ Cor 4.18
together with this node gives:
`SV_G` is `F_n`  ⟺  `(A_n)`  ⟺  `Z ≀_S G` is `F_n`,
the last step by de Cornulier and Bartholdi--de Cornulier--Kochloukova.
- So the simple group has exactly the finiteness of the lamplighter over the same action.
  Building finitely presented, or `F_n`, simple envelopes through `SV` becomes the problem of
  building a faithful actor `G ⊇ H` whose permutational wreath product `Z ≀_S G` is finitely
  presented, or `F_n`. The simplicity costs nothing.
- For every `n` this gives an `F_n` form of permutational Boone--Higman with the same shape:
  `H` embeds in an `F_n` simple twisted Brin--Thompson group iff `H` embeds in an
  `(A_n)`-actor.
  - `⇐` is this node.
  - `⇒` (referee c asked for an argument): if `SV_G` is `F_n`, then `SV_G` is itself an
    `(A_n)`-actor, through its clopen action on the proper nonempty clopen subsets of `C^S`
    (`twisted-btb-clopen-action-is-type-a`). That action is faithful and oligomorphic.
  - The pointwise stabilizer of a finite set of clopens is the product of the copies of
    `SV_G` supported on its Boolean atoms, by fullness (`bbmz-oligomorphic-twisted-questions-proof`,
    Step 1). So it is `F_n`, and so is the finite-index setwise stabilizer.
- **Method.** A Brown-criterion obstruction coming from bad simplex stabilizers can be an
  artifact of the cell structure. Filter by intervals, compute which intervals are
  homologically essential and in which degree, and ask for finiteness only of their
  stabilizers. This transfers to other Stein-type complexes (Röver--Nekrashevych, cloning
  systems, full groups of groupoids) wherever intervals are lattices of partitions.

## Scope

- **Non-faithful actions.** FFWZ conjecture the same characterization for abstract twisted
  Brin--Thompson groups. It is proved in `abstract-twisted-bt-type-fn-criterion` (lane proof,
  unreviewed), by running this argument on the `S`-colored Stein complex of the faithful
  `(S ⊔ G)V_G`.
- **Literature check (2026-09-18).** FFWZ v2 records the problem as open. One web search
  ("twisted Brin–Thompson type F_n ... 2026") found no later resolution. No MathSciNet
  search was done.

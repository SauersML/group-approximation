# Extending Gottschalk past sofic groups: the reduction is complete, and every counting mechanism is dead

Lane `gk3-approx-surjunctive`, 2026-09-14. This is a synthesis and gap map, not a new
theorem. It records why surjunctivity of the next famous approximation classes (linear
sofic, weakly sofic, metric ultraproducts, UQS) is a *complete reduction* to hard open
kernels already on main, and why no counting argument can close the gap. Every statement
below is cited to an established node or artifact; nothing here is claimed as new content.

## 1. The class chain and its surjunctivity claims

All inclusions are landed:

```text
residually finite  <=  sofic  <=  F_p-linear sofic  <=  weakly sofic
```

- residually finite: `residually-finite-groups-are-surjunctive` (Lawton), ESTABLISHED.
- sofic: `sofic-groups-are-surjunctive` (Gromov 1999, Weiss 2000), ESTABLISHED.
- `sofic <= F-linear sofic <= weakly sofic`: `linear-sofic-implies-weakly-sofic-over-every-field`
  and `sofic-implies-linear-sofic-over-every-field`, ESTABLISHED.
- weakly sofic groups are exactly the subgroups of metric ultraproducts of finite groups
  with bi-invariant metrics (Glebsky–Rivera; `glebsky-rivera-w-sofic-criterion`).

The four open extension claims, from strongest to weakest hypothesis on the group:
- `metric-ultraproducts-of-finite-groups-are-surjunctive` (OPEN) — equivalent to
  `weakly-sofic-groups-are-surjunctive` via the intended cycle
  (`bounded-width-closures-from-metric-ultraproduct-surjunctivity`).
- `linear-sofic-groups-are-surjunctive` over `F_p` (OPEN).
- `amenable-extensions-of-uqs-groups-are-surjunctive` (ESTABLISHED) with input
  `surjunctive-groups-are-uniformly-quantitatively-surjunctive` (OPEN).

## 2. The reduction is already exact: the nested reflection kernels

`surjunctivity-of-a-local-class-is-reflection-kernel-membership` (ESTABLISHED) reduces each
claim to reverse-word membership in a reflection kernel of the free group `F(D)` of a strict
rectangle datum `D`. The kernels nest:

```text
N  ⊆  N_ws  ⊆  N_lin(F)  ⊆  N_sof  ⊆  N_lef  ⊆  cl(N)
```

- `N` = normal closure of the forward relators. Gottschalk asks for a reverse word here.
- `N_ws` = bounded-width profinite closure (`weak-sofic-reflection-kernel-is-bounded-width-closure`).
  Weakly-sofic surjunctivity asks for one here.
- `N_lin(F_p)` = the `F_p`-linear-sofic reflection kernel, an exact per-datum rank implication
  (`linear-sofic-surjunctivity-is-a-rank-implication-per-datum`, ESTABLISHED).
- `N_sof` = sofic reflection kernel. Gromov–Weiss already supply a reverse word here for every `D`.
- `cl(N)` = full profinite closure; finite groups being surjunctive put a reverse word here always.

So the whole positive program is: *push the reverse word down from `N_sof` into the smaller
kernel `N_lin(F_p)` or `N_ws`, for every strict datum.* There is nothing left to reduce.

**Corollary (ordering of the open claims).** Since `N_ws ⊆ N_lin(F_p) ⊆ N_sof`, weakly-sofic
surjunctivity is the strongest extension claim and implies both `F_p`-linear-sofic surjunctivity
and Gromov–Weiss; and, at the group level, it also follows from the class inclusion
`F_p`-linear sofic `⊆` weakly sofic. This ordering is already visible in the ladder node and is
not new.

## 3. Why counting is dead (the barrier)

Every recorded positive mechanism certifies membership only in `N_sof`, never in the smaller
kernels:

- **Finite-action / Hamming counting.** `hamming-transports-of-weak-sofic-models-are-soficity`
  (ESTABLISHED): a group admits uniform Hamming transports of its weakly sofic models iff it is
  sofic. The Gromov–Weiss count consumes a finite `H`-set, not the bi-invariant length, so it
  reaches exactly the sofic data. The regular action gives maximal Hamming defect; conjugation
  on simple models degenerates. Counting therefore lands the reverse word in `N_sof` and no lower.
- **Rank-metric counting.** `site-pullbacks-are-discontinuous-in-the-rank-metric` (ESTABLISHED):
  a fixed coordinate algebra is preserved only by permutation matrices, and a rank-one
  perturbation of the identity gives a multiplicativity defect of rank `≥ n−1`. So nonlinear
  local rules have no rank-metric evaluation, and Gromov–Weiss counting has no linear-sofic
  version. `gromov-weiss-is-the-monomial-case-of-the-rank-implication` (ESTABLISHED) confirms
  the count works only on (near-)monomial tuples.
- **Peeling / permanence.** The finitary-split and graph-fold theorems
  (`graph-folds-over-surjunctive-groups-are-surjunctive`,
  `rf-lamp-wreaths-over-surjunctive-bases-are-surjunctive`) prove surjunctivity of the nonsofic
  witnesses `W`, `D` by separating finite quotients stratum by stratum. That argument carries no
  deficit (§4 of `quantitative-surjunctivity-residue-2026-09-12`), so it proves neither UQS/AQS
  nor any counting bound, and `sofic-permanence-closure-omits-simple-fa-nonsofic-groups` shows it
  never reaches the simple hosts `R^x`, `U`.

**Consequence.** A proof that any class `C` with `N_C ⊊ N_sof` is surjunctive must use a
*non-counting* certificate — a rank-visible invariant of the rule pair, or a formalizability
argument on the group side — because every counting certificate stops at `N_sof`.

## 4. Each open route is at least as hard as a named open problem

- **Linear sofic (`N_lin`).** Route `linear-sofic-surjunctivity-via-formalizability-and-ascent`
  = stable finiteness of `F_p[G]` (ESTABLISHED for linear sofic,
  `linear-sofic-group-algebra-is-stably-finite`) + `prime-field-left-inverse-pairs-are-stably-formalizable`
  (OPEN) + alphabet ascent (OPEN). Stable formalizability is open on every group with nontrivial
  memory; `binary-left-inverse-pairs-need-not-be-formalizable` shows the unstabilized form is
  false, so stabilization is necessary at every prime. Moreover no nonsofic group is known to be
  linear sofic (Arzhantseva–Păunescu Question 8.5), so `linear-sofic-groups-are-surjunctive`
  exceeds Gromov–Weiss only conditionally.
- **Weakly sofic (`N_ws`).** `strict-reverse-words-lie-in-bounded-width-profinite-closures`
  (OPEN): needs, per datum, one `n` such that in *every* finite group some reverse word is a
  product of `≤ n` conjugates of forward relators. Finite surjunctivity gives such a word with
  conjugacy width growing in `|H|` (no uniform `n`), and Hamming transports reach only `N_sof`.
  Whether every group is weakly sofic is itself open, and Glebsky–Rivera expect not.
- **UQS (`amenable-extensions-of-uqs-groups-are-surjunctive`).** Established as a permanence
  theorem, but no nonsofic group is known to be UQS or AQS, and the payoff hosts (simple Kazhdan
  groups) have no infinite amenable quotient, so it does not reach `R^x` or `U`. The one route to
  a nonsofic UQS group is `surjunctive-groups-are-uniformly-quantitatively-surjunctive` (OPEN),
  which for the peeled nonsofic witnesses would need a per-track deficit carried through each
  stratum — exactly what peeling does not provide.

## 5. Exact gap

No surjunctivity claim strictly beyond sofic groups is provable here without one of:
1. a positive answer to stable formalizability with nontrivial memory
   (`prime-field-left-inverse-pairs-are-stably-formalizable`), which then gives `N_lin`;
2. a uniform bounded-width closure bound (`strict-reverse-words-lie-in-bounded-width-profinite-closures`),
   which then gives `N_ws`;
3. UQS/AQS for a nonsofic surjunctive kernel
   (`surjunctive-groups-are-uniformly-quantitatively-surjunctive`).
Each is at least as hard as a standing open problem, and §3 shows no counting argument can supply
any of them. The reduction and the barrier are already on main, and this file only assembles them.
The one theorem this lane adds is `uqs-groups-are-closed-under-amenable-extensions`: UQS passes to
extensions with amenable quotient with an explicit constant, so towers over a UQS group stay UQS. It
adds no new surjunctive host (research/artifacts/gk3-approx-surjunctive-2026-09-14.md, Section 3).

Sources pinned to established nodes above; Arzhantseva–Păunescu arXiv:1212.6780 (Question 8.5,
Theorem 8.2) as cited in `linear-sofic-group-algebra-stably-finite-citation` and
`linear-sofic-implies-weakly-sofic-over-every-field`; Glebsky–Rivera arXiv:0709.0026 as cited in
`glebsky-rivera-w-sofic-criterion-citation`.

---
rg: 2
id: dyadic-rordam-tower-realizes-finite-car-corner
kind: claim
refuted_by: [uniformly-doubled-rordam-steps-force-proper-infiniteness]
title: A step-dependent Rordam tower with sparse paired steps gives a simple infinite algebra with a unital CAR of finite projections
distinct_from:
  stw99-lxvi-finite-car-corner-with-infinite-double: that is the abstract construction target (a finite simple CAR-containing algebra with infinite double); this is a specific candidate construction of it inside a Rordam-style inductive limit of multiplier algebras, with an explicit multiset calculus and a verification ledger.
  stw99-lxvi-car-stabilization-destroys-finite-seed: that kills the tensorial insertion of the CAR; this construction inserts the CAR non-tensorially, as dyadic halvings of an evolving direct-sum projection, and is not covered by that obstruction.
  dyadic-rordam-identical-pairing-destroys-sdr: that gives the elementary finite Hall obstruction to this design's V4 ledger; the present node records the now-refuted construction proposal.
artifacts:
  - research/artifacts/stw99-lxvi-dyadic-rordam-design-2026-08-30.md
---

There is an inductive limit `B = lim (M(A), ψ_n)`, `A = C(Z) ⊗ K`,
`Z = (S²)^∞`, of Rørdam type (arXiv math/0204339, Sections 4–5) but with
step-dependent connecting endomorphisms `ψ_n`, such that:

1. `B` is unital and simple, and `1_B` is properly infinite;
2. there are projections `Q_1 ≥-chain data` with `1 ~ Q_1 ⊕ Q_1'`,
   `Q_k ~ Q_{k+1} ⊕ Q_{k+1}'` (orthogonal, equivalent), all `Q_k` nonzero
   and FINITE;
3. hence a unital embedding `M_{2^∞} → B` whose image contains the
   nonzero finite projections `Q_k`;

and a separable simple such `B_0` follows by Blackadar's separabilisation
keeping the CAR, a non-unitary isometry, and the finiteness witnesses.
Establishing this claim solves STW Problem LXVI affirmatively
(`stw99-problem-lxvi-car-embedding-with-finite-projection`), and the
corner `Q_1 B Q_1` realises
`stw99-lxvi-finite-car-corner-with-infinite-double`.

**Design (full detail and ledger in the artifact).**  Branch data per step
is decoupled into (eval-coordinate set, dense eval points, injective
relabeling with fresh range, fresh tensor-set `I` with `|I| ≥ h(step)`),
so the multiset dynamics is `α(J) = ν(J∖E) ∪ I` and every evolved set has
size at least `h(n)`.  The seed is `⊕_i p_{a_i}` over infinitely many
distinct singletons: `θ ↪ ζ_a ⊕ ζ_a` gives `1 ≾ Q_1 ⊕ Q_1`, and
Lemma 4.3 gives `1 ~ Q_1 ⊕ Q_1`.  Sparse "paired" steps duplicate the
entire branch list, making every class exactly 2-divisible there:
`Q_k ~ 2 Q_{k+1}` by multiset matching.  Finiteness of `Q_1` (hence of all
`Q_k`) is Rørdam's Proposition 4.5(i) with the system-of-distinct-
representatives form of Proposition 3.2, which already handles repeated
sets: multiplicities grow as `2^{c(n)}` with `c(n) = O(log n)` while sizes
grow at least linearly, and shared tensor-set elements are avoided by
per-copy private representatives.

## Attempts

Status: REFUTED AS DESIGNED, same day —
`uniformly-doubled-rordam-steps-force-proper-infiniteness` proves the
paired-step halving mechanism forces `Q_1 ~ 1`: sets diverging at an early
step keep bounded early parts while shared tails and multiplicities grow,
and rank then beats half the dimension, embedding a trivial line (the
(V4) risk was real and fatal).  The claim is kept as the record of the
design; the surviving direction is the higher-rank Euler-divisibility
tower sketched in the no-go node and the dossier: blocks `η_m` with
`η_m ≅ 2·η_{m+1}` and `e(η_m) ≠ 0`, whose Euler classes must be classes
with all 2-power roots nonvanishing (these exist in the ring; bundle
realizability over the dynamics is the open crux).  Original ledger:  The remaining verifications, each
expected to mirror Rørdam §5 line by line, are itemised in the artifact:
(V1) the step-map analogues of Proposition 5.2(i)-(ii) (fullness engine
via doubled-singleton tensor branches replacing the `j ≤ 0` relabeling
branches, and density of eval points per step); (V2) Lemma 5.1's `F ~ 1`
via the infinite-multiplicity eval branches; (V3) Lemma 5.4's computation
for decoupled branch data; (V4) the SDR ledger at paired steps (two
disjoint transversal systems per doubling, private-element counting);
(V5) the limit-finiteness transfer (Prop 2.3 corners).  No step is
expected to need a new idea; the risk concentrates in (V4).

There is also an earlier, schedule-independent failure:
`dyadic-rordam-identical-pairing-destroys-sdr`.  Along one fixed branch
history, infinitely many singleton seeds have sets `C union {u_i}` with
only one seed-private coordinate.  An identical branch pair produces two
copies of `C' union {v_i}`; taking both copies for `N>|C'|` seeds gives a
Hall-deficient sublist.  Thus neither a larger finite `h(n)` nor sparser
paired steps can repair V4.

---
rg: 2
id: simplicity-of-finite-presentations-arithmetical-position
kind: claim
title: Simplicity of finite presentations lies in Pi^0_2 and is Sigma^0_1-hard, and it drops to Delta^0_2 if Kuznetsov profiles of finitely presented simple groups are uniformly recursively bounded
distinct_from:
  arithmetical-complexity-table-of-group-properties: that ledger has no row for simplicity; this supplies the row (fp column) with its proofs and an open exact level.
  bh-separators-must-omit-nested-decidable-hosts: that shows uniform Kuznetsov-profile bounds would put all finitely presented simple groups under one word-problem time bound; this shows the same bounds would also lower the arithmetical level of recognizing simplicity, so a Pi^0_2-completeness proof would refute them.
  simple-envelope-forces-solvable-word-problem: that is Kuznetsov's theorem for each simple group; this is about recognizing simplicity from a presentation.
---

**ESTABLISHED** by `simplicity-of-finite-presentations-arithmetical-position-proof`
(lane proof, elementary, not independently reviewed; no novelty claimed, and the
first two items may well be folklore). The exact level is OPEN.

Let `SIMPLE_fp` be the set of codes of finite presentations `P = <X | R>` whose
group `G_P` is simple, meaning nontrivial with no normal subgroups other than
`1` and `G_P`.

1. **Upper bound.** `SIMPLE_fp ∈ Π^0_2`.
2. **Lower bound.** `SIMPLE_fp` is `Σ^0_1`-hard, so it is not co-r.e. and in
   particular undecidable. The reduction `P ↦ V × G_P` is uniform, with `V`
   Thompson's group. The same holds for the set of *infinite* simple ones.
3. **Conditional collapse.** Use the Kuznetsov profile `(δ_S, ν_S)` of
   `bh-separators-must-omit-nested-decidable-hosts` §3. Suppose some recursive `F`
   has `δ_S(n), ν_S(n) <= C·F(C·n)` for every finitely presented simple `S`, with
   `C` depending on the presentation. Then `SIMPLE_fp ∈ Σ^0_2`, hence
   `SIMPLE_fp ∈ Δ^0_2`.

**Consequence.** A proof that `SIMPLE_fp` is `Π^0_2`-complete, or merely not in
`Σ^0_2`, would show that the Kuznetsov profiles of finitely presented simple
groups have no uniform recursive bound. That is a consequence in the same family
as `fp-simple-groups-with-arbitrarily-complex-word-problem` and the Dehn-function
roots (`fp-simple-dehn-functions-have-no-recursive-upper-bound`). It is reached
by an arithmetical rather than a constructive argument.

**Open.** Whether `SIMPLE_fp` is `Π^0_1`-hard, and whether it is
`Π^0_2`-complete.
- A reduction from a `Π^0_1`-complete set must output finitely presented *simple*
  groups on the positive side, and these have solvable word problem. So Rabin-type
  reductions, which embed a group with unsolvable word problem on one side, only
  give item 2.
- A `Π^0_2`-hardness proof must produce finitely presented simple groups
  uniformly from `Π^0_2` data. By item 3 it would already have to realize
  unbounded Kuznetsov profiles.

**Table row (fp column).** simple: `Π^0_2`, `Σ^0_1`-hard; not `Π^0_1`; `Δ^0_2`
under uniform Kuznetsov bounds; exact level OPEN.

DERIVATION
simplicity-of-finite-presentations-arithmetical-position-proof

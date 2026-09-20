---
rg: 2
id: lifted-thompson-t-bounded-area-chromatic-code
kind: claim
title: "The lifted Thompson group T-bar carries a bounded-area infinite-chromatic commutator code for some nontrivial (necessarily non-central) mark"
distinct_from:
  binary-leavitt-bounded-area-chromatic-code: that asks for a bounded-area code in the binary-Leavitt Steinberg group, whose obstacle is stabilizer word length in an orbit section; this asks for one in the torsion-free group T-bar, where the mark cannot be central and the exact skeleton is the wandering table in F.
  lifted-thompson-t-is-not-mf: that is the non-MF conclusion; this is a combinatorial sufficient condition which can fail even if T-bar is not MF, since the commutator-code criterion has no known converse.
  lifted-thompson-t-exact-wandering-commutator-table: that is the exact table and a lower bound for literal shift templates; this asks for a uniform area bound for some choice of words.
---

**OPEN.**  Fix a finite presentation `<S | R>` of `T̄`.  The choice does not matter.
Let `phi` send each old generator to a word in the new generators.  Replacing
every word `w` of a code by `phi(w)` multiplies each area by at most
`max_r Area'(phi(r))`, because each cell of a diagram for `w` becomes a
diagram for `phi(r)`.
Claim: there exist

- a graph `Lambda` with infinite chromatic number,
- words `c_v, h_v, a_v` for `v in Lambda`,
- a word `x` that is nontrivial in `T̄`,
- constants `A_Delta` and `A_0`,

satisfying CCC1 and CCC2 of `infinite-chromatic-commutator-code-kills-mf-mark`:

```text
Area_R([c_v, h_v] (a_v x a_v^(-1))^(-1)) <= A_Delta,
Area_R([c_w, h_v]) <= A_0        on every oriented edge (v,w).
```

## Constraints already proved

- **The mark is not central.**  `x` is not in `<z>`.  In fact `x` must be a
  nontrivial commutator whose conjugacy class meets no nontrivial element of
  `<z>` (`central-marks-escape-chromatic-codes`).
- **An exact skeleton exists.**  The wandering table
  `c_n = x0^n c0 x0^(-n)`, `h_n = x0^n h0 x0^(-n)` on `K_Z` satisfies both
  identities exactly (`lifted-thompson-t-exact-wandering-commutator-table`).
- **Literal words fail.**  For that skeleton, the literal shift words have
  CCC2 area at least linear in the shift, on every subgraph with infinite
  chromatic number.
- **No shortcut through `T`.**  An exact code in `T` lifts to an exact code in
  `T̄` (item 4 of the central-marks node), but not with bounded area, so a code
  for `T` does not directly give this leaf.

## Sufficient test

Find words `C_n` and `H_n` in `T̄` representing `c_n` and `h_n` such that both
of the following are bounded independently of `m != n`:

- `Area([C_m, H_n])`;
- `Area([C_n, H_n] (x0^n y x0^(-n))^(-1))`.

A natural source of candidates is the rotations of `T` and the cone relations
of `T̄`.  For example, write the shift `x0^n` through bounded products of
rotation-conjugated generators whose supports localize, so that each
commutation `[C_m, H_n]` is witnessed inside a bounded window.  The OPEN node
`v-cone-sliding-localizes-disjoint-support-relations` records the analogous
localization in `V` without an area bound.

## How it fails on its own

- **If `T̄` is MF,** the leaf is false by the commutator-code criterion.
- **If `T̄` is not MF,** the leaf may still be false: a non-MF proof by
  another mechanism, for example eigencorners, does not produce a code.
- **Shape of a refutation.**  A presentation-independent invariant of
  `T̄`-diagrams that grows along every infinite-chromatic family of commuting
  pairs, generalizing the bridge count of the exact table, would refute the
  leaf.

## Attempts

**2026-09-19, swarm-0917-w17-w17-ptm-last1.**  Three approaches were tried.

1. **Mark `z` directly.**  Dead at CCC1: no commutator equals `z^k` for
   `k != 0`, by the translation number.
2. **Lift an exact code from `T`.**  The identities survive the lift, but the
   area does not.  Central corrections `w z w^(-1)` with long conjugators `w`
   are not controlled in finite dimension.
3. **Literal shift templates on the wandering table.**  Dead at CCC2: the
   bridge count gives area at least `(4|m-n| - 2(|c0| + |h0|)) / P`.

The next attack must re-express `x0^n` so that the supports of `C_m` and `H_n`
separate within a bounded number of relator cells.  Candidates are the
rotations or the cone relators of `T̄`.  It is deferred.

---
rg: 2
id: simple-group-relator-templates-over-finite-simple-groups-proof
kind: route
title: Pair blocks realize every seed or the identity, so each simple family's covering runs with one fixed block power
target: simple-group-relator-templates-over-finite-simple-groups
requires: [liebeck-shalev-normal-subset-covering, simple-group-relator-width-in-finite-simple-targets, simple-group-psl-width-is-finite-field-linear-soficity, simple-group-classical-width-finite-field-linear-soficity, sofic-implies-linear-sofic-over-every-field]
---

`G = <X | R>` is infinite, finitely presented, simple, and not linear sofic over finite fields. So `G`
is nonsofic (`sofic-implies-linear-sofic-over-every-field`). (E1) is as in
`simple-group-relator-width-in-finite-simple-targets-proof`, and `c`, `c'` are the Liebeck--Shalev and
minimal-degree constants. The special linear and isometry proofs are
`simple-group-psl-width-is-finite-field-linear-soficity-proof` (PSL) and
`simple-group-classical-width-finite-field-linear-soficity-proof` (ISO).

## 1. Blocks

**The block.** Let `B = prod_(r in R) (r, r^-1)`. The evaluations of one pair at `(Q, a)` are the
products `g r(a) g^-1 · g' r(a)^-1 g'^-1`. They include:
- **(P1)** `1`, taking `g' = g`;
- **(P2)** every `Q`-conjugate of a seed `[r(a), y]`, taking conjugators `g` and `g y`;
- **(P3)** every element of `C C^-1`, when `r(a)` normalizes a subgroup `H <= Q` and
  `C = {h r(a) h^-1 : h in H}`.

  Since `h r h^-1 h' r^-1 h'^-1 = (h r h^-1 r^-1)(r h' r^-1 h'^-1)`, the set `C C^-1` lies in `H`. It is an
  `H`-normal subset with `|C C^-1| >= |C|`.

**(L) Covering lemma.** Let `H <= Q` with `H/Z(H)` nonabelian simple. Let `S` be an `H`-normal subset of
`H` whose elements are evaluations of a single pair (by (P2) or (P3)), with image `Sbar != {1}`. Suppose
`N >= c log|H/Z(H)| / log|Sbar|`. Then every `u in H` is `s z`, with `s` an evaluation of `B^N` and
`z in Z(H)`.

*Proof.* Liebeck--Shalev gives `Sbar^N = H/Z(H)`. Use that pair in each copy of `B`, and (P1) for all
other pairs.

**(C) The template.** Put `omega_x = prod_(j<=J) (B^N (B^N)^*) · n_x`. Here `n_x` is read as a template:
its conjugating words become free conjugators.
- **Covered commutators.** Suppose `c_j(a) = s z` with `s` an evaluation of `B^N` and `z` commuting
  with `c'_j(a)`. Then `[c_j(a), c'_j(a)] = s · (c'_j(a) s^-1 c'_j(a)^-1)`, an evaluation of
  `B^N (B^N)^*`.
- **Trivial commutators.** Evaluate the block to `1`.
- **Larger `N`.** Extra blocks evaluate to `1`, so a larger `N` is always allowed.

It suffices to find, for each family, an `N` with this property for every tuple.

## 2. Abelian, bounded and bounded-rank targets

- **Abelian.** For `Q = Z/p`, every commutator is `1` and `n_x(a) = a_x`.
- **Bounded rank.** Let `Q` be nonabelian simple and sporadic, or of order at most `M`, or of Lie type
  of rank at most `8` (so `log|Q| <= 248 log q`), or one of the quasisimple classical groups of
  dimension below the thresholds `N_1` of PSL/ISO.
  - *Central relators.* If every `r(a)` is central, (E1) in `Q/Z(Q)` makes every commutator `1`.
  - *A non-central relator.* Otherwise pick `r*` with `r*(a)` non-central. Pick `y` with `[r*(a), y]`
    non-central: if every `[r*(a), y]` were central, `r*(a) Z` would be central in the simple quotient.
    Take `S` the class of that seed.
  - *Bound.* By the minimal degree bound `|Sbar| - 1 >= c' q`, the ratio in (L) is bounded for
    `q >= q_1`. The finitely many remaining groups have ratio at most `log M'/log 2`.

## 3. Alternating targets `Alt(n)`, `n >= 5`

Let `Omega_0` be the moved set of `a`, `n' = |Omega_0|`, and `eps_0`, `N_0` as in Section 2 of the proof
of `simple-group-relator-width-in-finite-simple-targets`.

- **Small moved set, `n' <= N_0`.**
  - If `n <= N_0 + 5`, Section 2 applies.
  - Otherwise let `H = Alt(Omega_1)` with `Omega_1 ⊇ Omega_0` and `|Omega_1| = N_0 + 5`. Every
    `c_j(a)` lies in `Alt(Omega_0) <= H`.
  - If some `r*(a) != 1`, it lies in `Sym(Omega_0)`, which normalizes `H`. Pick `y in H` not commuting
    with it. The seed `[r*(a), y]` is a nontrivial element of `H`, and `H` has bounded order.
  - If every `r(a) = 1`, then `a = 1`.
- **Large moved set, `n' > N_0`.**
  - Let `H = Alt(Omega_0)`, and `r*` with `s = |supp r*(a)| >= eps_0 n'`. `r*(a)` lies in `Sym(Omega_0)`,
    which normalizes `H`.
  - `C` is its `H`-orbit, `S = C C^-1` by (P3), and `log|S| >= log|C| >= (s/8) log n'` (the class
    estimate there).
  - With `log|H| <= n' log n'`, the ratio in (L) is at most `8/eps_0`.
  - Every `c_j(a)` lies in `<a>' <= Alt(Omega_0) = H`, and `Z(H) = 1`.

## 4. Special linear targets

Run PSL, Sections 3 to 5, with the double-commutator template of (C) in place of the single one.
- **Bounded rank.** Section 2 above.
- **Proportional case.** `H = SL_n(q)` and `h = r*(a) in H`, which normalizes `H`. Take `S = C C^-1`
  with `C = h^H`, by (P3). Then `|Sbar| >= |C|/(q-1)`, and the estimate of PSL Section 4 bounds the
  ratio by `2/eta`. Every `c_j(a) in SL_n(q)`, and `Z(H)` is central in `Q`.
- **Near-scalar case.** `H = SL(W''') x 1`, and the seed is `h = [r*(a), y]` of PSL 5.4, by (P2), with
  `S = h^H`. The ratio is bounded as in PSL 5.5.
  - *Covered elements.* `c_j(b)` lies in `[GL(W), GL(W)] x 1 <= H`, so no determinant correction is
    needed.
  - *Centre.* `Z(H)` consists of scalars on `W'''`, and they commute with `c'_j(a)`: it is a scalar
    times `c'_j(b) in GL(W) x 1`.
  - *Commutator.* `[c_j(a), c'_j(a)] = [c_j(b), c'_j(b)] = s · (c'_j(a) s^-1 c'_j(a)^-1)`.

## 5. Isometry targets

Run ISO, Sections 2 to 4, verbatim. The seeds there are already of the form (P2): `[h, y]` in Section 3,
and `[r*(a), y]` in Section 4. The local groups `H = I(W''')' x 1` have centres commuting with
`c'_j(a)`, and every `c_j(b) in I(W)' x 1 <= H`. Section 2 above replaces ISO Section 2 and 4b.

## 6. Conclusion

`N` is the maximum of the finitely many constants above. `omega_x` then has length
`4 J N |R| + J'` and is valid over `S`. For a direct product, evaluate coordinatewise.

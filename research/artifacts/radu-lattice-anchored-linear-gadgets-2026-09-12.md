# Radu's lattice: anchored linear gadgets over F_2 (w7-vh-anchored, 2026-09-12)

Lane `w7-vh-anchored`. Goal root `strict-automaton-on-lattice-in-product-of-trees`, linear case
`radu-bmw-lattice-group-algebra-not-stably-finite`: matrices `A, B` over `F_p[Gamma_R]` with
`B A = I_n` and `A B != I_n`. Paper work only. This artifact records screens and where candidates
die. It constructs no pair and decides nothing. It does not repeat the Brin--Thompson `2V` host of
`w6-free-neg-d` or the Leavitt pairs of `w6-wf-stage1-a/b`.

Results:
- Lemma 1.1: a factor `I_n + N` with `N` nilpotent is a two-sided unit, so it gives no pair.
- Theorem 1.2: over `F_2`, at size one, with supports in the unit ball, `B A = 1` forces `A = B`
  with `A^2 = 1`.
- Theorem 2.1: a set of letters generates `Gamma_R` or a sofic subgroup, by an exact criterion.
- Section 3: the defect vanishes modulo the finite residual `Gamma_0`. With Remark 3.6 the support
  radii satisfy `r + s >= 4`, and the screen is blind at `r + s = 4`.
- Sections 4--5: where each candidate dies, and the invariant blocking the smallest nonlinear anchored
  gadget.

## 0. Setting and source check

```text
Gamma_R = <a,b,c,x,y,z | a^2, b^2, c^2, x^2, y^2, z^2, axax, ayay, azbz, bxbx, bycy, cxcz>
```

This is presentation `(RE1)` on p. 9 of arXiv:2509.05054v2
(`radu-bmw-lattice-embeds-in-titz-witzel-kernel-citation`). The horizontal letters are
`L_h = {a,b,c}` and the vertical letters `L_v = {x,y,z}`. Put `A = <L_h>` and `V = <L_v>`, both
`C_2 * C_2 * C_2`. `B_r` is the ball of radius `r` in the word metric on the six letters.

**Square table, re-derived from the relators.** A relator `h v h' v'` gives `h v = v' h'`. Its cyclic
shift `h' v' h v` gives `h' v' = v h`. So each relator yields a table entry and its transpose.

| relator | entries `h v = v' h'` |
|---|---|
| `axax` | `ax = xa` |
| `ayay` | `ay = ya` |
| `bxbx` | `bx = xb` |
| `azbz` | `az = zb`, `bz = za` |
| `bycy` | `by = yc`, `cy = yb` |
| `cxcz` | `cx = zc`, `cz = xc` |

These are the nine entries of the RS3 table in
`research/artifacts/titz-witzel-radu-sublattice-2026-09-11.md`. So the table used below agrees with
the presentation read from the source. The map `(h, v) -> (v', h')` is a bijection
`L_h x L_v -> L_v x L_h`, and the commuting pairs are `(a,x)`, `(a,y)` and `(b,x)`.

**Normal forms.** Every element is uniquely `alpha omega`, with `alpha` a reduced word in `L_h` and
`omega` a reduced word in `L_v` (`research/artifacts/radu-lattice-strict-automaton-screens-2026-09-12.md`).
Pushing letters through squares preserves the numbers of horizontal and vertical letters, and free
reduction only shortens. So the length of `alpha omega` is `|alpha| + |omega|`.

## 1. Small gadgets

Convention: `B A = I_n`, `A B != I_n`, and the defect is `D = I_n - A B`. `S_A` and `S_B` are the
unions of the supports of the entries. Then `supp D ⊆ S_A S_B ∪ {1}`.

**Lemma 1.1 (unipotent factors).** If `B = I_n + N` with `N^k = 0`, then `B` is a two-sided unit and
`A = B^(-1)`, so `A B = I_n`. The same holds for `A = I_n + N`.

*Proof.* `I_n - N + N^2 - ... + (-N)^(k-1)` is a two-sided inverse of `I_n + N`. A one-sided inverse
of a two-sided unit is its inverse. □

At `p = 2` every involution `t` gives `(1+t)^2 = 0`, and `I_n + (1+t) X (1+t)` is unipotent for every
`X`. So the torsion gadgets `1 + a`, and every conjugate or product-sandwich built from them, give
units and never one-sided pairs. A witness has neither factor in `I_n + nilpotents`.

**Theorem 1.2 (unit ball, size one, `p = 2`).** Let `alpha, beta in F_2[Gamma_R]` be supported in
`B_1 = {1} ∪ L_h ∪ L_v`. If `beta alpha = 1`, then `alpha = beta`, and `alpha` is `1`, a letter, or
`1 + h + v` with `(h, v)` a commuting pair. Each of these has `alpha^2 = 1`. So the window
`(B_1, B_1)` carries no one-sided pair at size one.

*Proof.* Write `alpha = alpha_0 + sum_s alpha_s s` and `beta = beta_0 + sum_s beta_s s`, with `s`
running over the six letters. The products of two letters are of four kinds.
1. `s s = 1`.
2. `s t`, with `s != t` of the same type, is a reduced word of length two. Distinct ordered pairs give
   distinct elements.
3. `h v` is in normal form, so the nine products `h v` are distinct.
4. `v' h' = h v` for the unique table entry, so each `v h` is one of the nine `h v`.

By uniqueness of normal forms, kinds 2 and 3 are disjoint from each other, from `1` and from the
letters. Comparing coefficients in `beta alpha = 1`:

```text
(E1) beta_0 alpha_0 + sum_s beta_s alpha_s = 1
(E2) beta_0 alpha_s + beta_s alpha_0 = 0              for every letter s
(E3) beta_s alpha_t = 0                               for s != t of the same type
(E4) beta_h alpha_v + beta_(v') alpha_(h') = 0        for each entry h v = v' h'
```

- *`alpha_0 != beta_0`.* If `alpha_0 = 1` and `beta_0 = 0`, then (E2) gives `beta_s = 0` for every
  `s`. So `beta = 0`, against (E1). The other case is symmetric.
- *`alpha_0 = beta_0 = 1`.* (E2) gives `alpha = beta`. By (E3), `alpha` has at most one horizontal and
  at most one vertical letter. By (E1) the number of letters is even. If it is zero, `alpha = 1`.
  Otherwise `alpha = 1 + h + v`, and (E4) at the entry `h v = v' h'` reads
  `1 + alpha_(v') alpha_(h') = 0`. So `v' = v` and `h' = h`, and the pair commutes. Then
  `(1 + h + v)^2 = 1 + 1 + 1 + hv + vh = 1`.
- *`alpha_0 = beta_0 = 0`.* By (E3), at most one horizontal and at most one vertical `s` have
  `alpha_s = beta_s = 1`, so by (E1) exactly one does. Say it is `h`; the vertical case is symmetric.
  By (E3) the horizontal parts of `alpha` and `beta` are both `h`. Let `P` and `Q` be the vertical
  parts of `alpha` and `beta`. By (E3), if `P` and `Q` are both nonempty they are one singleton
  `{v}`, and then (E1) has two nonzero terms, a contradiction. If `v in P`, (E4) at `h v = v' h'`
  reads `1 + beta_(v') alpha_(h') = 0`, which needs `Q` nonempty. If `v in Q`, (E4) at the entry
  `h'' v'' = v h` reads `beta_(h'') alpha_(v'') + 1 = 0`, which needs `P` nonempty. So
  `P = Q = ∅` and `alpha = beta = h`. □

**Remarks.**
- The proof uses only a one-vertex complete square complex with involutive letters, so it holds for
  every such group. Only `F_2` and size one are checked.
- By Corollary 3 of `one-sided-inverse-pairs-transfer-to-table-realizations`, the table group of the
  window `(B_1, B_1)` is `Gamma_R` itself. So no table screen reaches this window, and the computation
  has to be done inside `Gamma_R`. Section 3 excludes the window at every size, given Remark 3.6.

## 2. Letter subgroups

**Theorem 2.1.** For a set `L'` of letters, `<L'> = Gamma_R` if and only if `y in L'`, `L'` meets
`{x, z}`, and `L'` either meets `{b, c}` or contains `{a, z}`. Otherwise `<L'>` is sofic. The minimal
generating sets of letters are `{a,y,z}`, `{b,x,y}`, `{b,y,z}`, `{c,x,y}` and `{c,y,z}`.

*Proof.* The table gives `b = zaz`, `a = zbz`, `c = yby`, `b = ycy`, `z = cxc` and `x = czc`.
- *Generation.* `<a,y,z>` contains `b = zaz`, `c = yby` and `x = czc`. `<b,x,y>` contains `c = yby`,
  `z = cxc` and `a = zbz`. `<b,y,z>` contains `c = yby`, `x = czc` and `a = zbz`. `<c,x,y>` contains
  `b = ycy`, `z = cxc` and `a = zbz`. `<c,y,z>` contains `b = ycy`, `x = czc` and `a = zbz`.
- *Non-generation.* Suppose `L'` fails the criterion.
  - If `y` is not in `L'`, then `L' ⊆ L_h ∪ {x, z}` and `<L'> ≤ P_xz`.
  - If `L'` misses `{x, z}`, then `L' ⊆ L_h ∪ {y}` and `<L'> ≤ P_y`.
  - Otherwise `L'` misses `{b, c}` and does not contain `{a, z}`. If `a` is not in `L'`, then
    `<L'> ≤ V`. If `a` is in `L'`, then `z` is not, so `L' = {a, x, y}`. Since `a` commutes with `x`
    and `y`, `<a,x,y>` is a quotient of `C_2 x D_infinity`, hence amenable.

  `P_y` and `P_xz` are sofic (`radu-bmw-coordinate-subgroups-are-sofic`), `V` is virtually free, and
  subgroups of sofic groups are sofic. □

Item 4 of `radu-bmw-coordinate-subgroups-are-sofic` covers the sets containing `L_h` or `L_v`.
Theorem 2.1 covers all 64 sets.

**Consequence for windows.** If `S_A ∪ S_B ⊆ B_1`, the support group is `<L'>` for the set `L'` of
letters used. A witness must use one of the five generating triples, and its support group is then
all of `Gamma_R`. At radius one there is no intermediate nonsofic letter subgroup to aim at.

# Radu's lattice: anchored linear gadgets over F_2 (w7-vh-anchored, 2026-09-12)

Lane `w7-vh-anchored`. Goal root `strict-automaton-on-lattice-in-product-of-trees`, linear case
`radu-bmw-lattice-group-algebra-not-stably-finite`: matrices `A, B` over `F_p[Gamma_R]` with
`B A = I_n` and `A B != I_n`. Paper work only. This artifact records screens and where candidates
die. It constructs no pair and decides nothing. It does not repeat the Brin--Thompson `2V` host of
`w6-free-neg-d` or the Leavitt pairs of `w6-wf-stage1-a/b`.

Verification: w4-vf-linear-b re-derived Sections 0--3 and 5, PASS given Remark 3.6 (Section 44 of
`research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`, 1a24d8a873). The Section 4 rows that
cite other nodes were not checked.

Results:
- Lemma 1.1: a factor `I_n + N` with `N` nilpotent is a two-sided unit, so it gives no pair.
- Theorem 1.2: over `F_2`, at size one, with supports in the unit ball, `B A = 1` forces `A = B`
  with `A^2 = 1`.
- Theorem 2.1: a set of letters generates `Gamma_R` or a sofic subgroup, by an exact criterion.
- Section 3: the defect vanishes modulo the finite residual `Gamma_0`. With Remark 3.6 the support
  radii satisfy `r + s >= 4`, and the screen is blind at `r + s = 4`. The idempotent law excludes
  `r + s = 4` (`radu-lattice-one-sided-pairs-need-radius-five`, c7fbc72300).
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

**Proposition 1.3 (transposed hinges, linear form).** Let `iota` be the anti-automorphism of
`F_p[Gamma_R]` with `iota(g) = g^(-1)`, extended to matrices by `iota(A)_(ij) = iota(A_(ji))`. Then
`iota(A B) = iota(B) iota(A)`. If `iota(A) = A` and `iota(B) = B`, then `B A = I_n` implies
`A B = iota(B A) = I_n`. At size one every element supported in `B_1` is `iota`-fixed, because the
letters are involutions. So the no-pair part of Theorem 1.2 holds over every commutative coefficient
ring; the classification is what `F_2` adds. This is the linear form of Lemma 5 of the screens
artifact: letter identifications transpose. At size `n >= 2` it needs symmetric matrices, and
general matrices with entries supported in `B_1` are not symmetric.

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

  The four subgroups are proper, by normal forms: `P_y = A ∪ A y` misses `x`, `P_xz = A <x,z>`
  misses `y`, `V` misses `a`, and `<a,x,y> = {1,a} <x,y>` misses `b`. So `<L'> != Gamma_R`. `P_y` and
  `P_xz` are sofic (`radu-bmw-coordinate-subgroups-are-sofic`), `V` is virtually free, and subgroups
  of sofic groups are sofic. □

Item 4 of `radu-bmw-coordinate-subgroups-are-sofic` covers the sets containing `L_h` or `L_v`.
Theorem 2.1 covers all 64 sets.

**Consequence for windows.** If `S_A ∪ S_B ⊆ B_1`, the support group is `<L'>` for the set `L'` of
letters used. A witness must use one of the five generating triples, and its support group is then
all of `Gamma_R`. At radius one there is no intermediate nonsofic letter subgroup to aim at.

## 3. The finite-residual screen

Let `Gamma_0` be the finite residual of `Gamma_R`, the intersection of its finite-index normal
subgroups, and let `pi : Gamma_R -> Q = Gamma_R / Gamma_0`.

**Theorem 3.1.** Let `A, B in M_n(F_p[Gamma_R])` with `B A = I_n`. Then `pi(A) pi(B) = I_n`, so every
entry of the defect `D = I_n - A B` has coefficient sum zero on each coset of `Gamma_0`. If
`A B != I_n`, some coset of `Gamma_0` meets the support of one entry of `D` in at least two points.
So `S_A S_B ∪ {1}` contains `g != h` with `g^(-1) h in Gamma_0`.

*Proof.* `Q` is residually finite: if `g` is not in `Gamma_0`, some finite-index normal subgroup `N`
misses `g`, and `N` contains `Gamma_0`. So `Q` is sofic, hence surjunctive
(`sofic-groups-are-surjunctive`), and `M_n(F_p[Q])` is directly finite by the contrapositive of
`stable-finiteness-failure-refutes-surjunctivity`. Applying `pi` entrywise gives
`pi(B) pi(A) = I_n`, hence `pi(A) pi(B) = I_n` and `pi(D) = 0`. The coefficient of `pi(D)_(ij)` at
`g Gamma_0` is the sum of the coefficients of `D_(ij)` over `g Gamma_0`. A nonzero `D_(ij)` has a
support point, and a zero sum on its coset needs a second one. □

Surjunctivity is not needed (w4-vf-linear-b). Take a finite quotient `phi` of `Q` that is injective on
the finite set `pi(S_A S_B ∪ {1})`. Then `M_n(F_p[phi(Q)])` is finite-dimensional, so
`phi(A) phi(B) = I_n`, and injectivity on the support of `pi(D)` gives `pi(D) = 0`.

This is Corollary 1 of `one-sided-inverse-pairs-transfer-to-table-realizations` with a residually
finite target in place of a finite one. The same argument inside the support group `H`, generated by
`S_A ∪ S_B`, puts `g^(-1) h` in the finite residual of `H`, which lies in `H ∩ Gamma_0`. The new input
is the length of the shortest elements of `Gamma_0`.

**Corollary 3.2 (radius, given Remark 3.6).** Remark 3.6 of arXiv:2509.05054v2 says that
`delta^(+-4) = (xz)^(+-4)` are the shortest elements of the finite residual. The Titz--Witzel lane
read it on p. 10 (`radu-bmw-lattice-embeds-in-titz-witzel-kernel-citation`); this lane did not reread
the page. Suppose `S_A ⊆ u B_r` and `S_B ⊆ B_s u^(-1)` for some `u`. Then `(u^(-1) A, B u)` is again a
pair with the same defect up to conjugation, with supports in `B_r` and `B_s`. The points `g, h` of
Theorem 3.1 lie in `B_(r+s)`, so `8 <= |g^(-1) h| <= 2(r+s)`, and `r + s >= 4`.

**Blind radius.** At `r + s = 4` length excludes nothing. `(zx)^2` and `(xz)^2` lie in `B_4`, and
`((zx)^2)^(-1) (xz)^2 = (xz)^4 = delta^4`, since `(zx)^(-1) = xz`.

**Consequences.**
- Given Remark 3.6, the windows `(B_1, B_1)`, `(B_1, B_2)` and `(B_2, B_1)` carry no pair at any size
  and any `p`. This extends Theorem 1.2 beyond size one, conditionally.
- A witness puts two points of one entry's defect support in one coset of `Gamma_0`. At `p = 2` every
  coset meets every entry's support in an even number of points.
- Theorem 3.1 does not use Remark 3.6. Without it, the only unconditional length information is
  `delta^4 in Gamma_0` (Lemma 3.5 of arXiv:2509.05054v2), and no radius bound follows by hand.
- Later work: `radu-lattice-one-sided-pairs-need-radius-five` (c7fbc72300) squares the defect
  idempotent on these coincidences. Given Remark 3.6 it excludes `r + s = 4`, and it excludes
  `r + s = 5` under its hypothesis (H10).

## 4. Where each candidate dies

| candidate | where it dies | invariant |
|---|---|---|
| `I_n + N` with `N` nilpotent, including the `1 + a` gadgets | always a unit (Lemma 1.1) | two-sided inverse |
| size one, supports in `B_1` | never strict over any commutative ring (Proposition 1.3); over `F_2` only involutions solve `beta alpha = 1` (Theorem 1.2) | transposed letter hinges |
| letter supports containing none of the five triples | sofic support group (Theorem 2.1) | soficity |
| any size, `r + s <= 3` | no two defect points in one coset of `Gamma_0` (Corollary 3.2, given Remark 3.6) | coincidence modulo `Gamma_0` |
| any size, `r + s = 4` | `D^2 = D` against the coincidences (`radu-lattice-one-sided-pairs-need-radius-five`, given Remark 3.6) | idempotent law |
| defects conjugate into finite-subgroup algebras | `radu-lattice-defect-idempotents-avoid-finite-subgroups` | finite subgroups inject into `(Z/2)^3` |
| corner idempotents at odd `p` | characters (Attempts of `radu-bmw-lattice-group-algebra-not-stably-finite`) | abelianization |
| two-by-two track gadgets `(s+s')(m_1+m_2) = 0` | do not die: `m_2 m_1^(-1)` can be an involution (Lemma D of `vh-lattice-table-hosts-2026-09-12.md`) | none |
| transposed hinges among longer products | do not die: `(ac, x) ~ (z, bc)` leaves the nontrivial hinge `zcbacz` (screens artifact, Section 3) | none |

**The expected obstruction is partial.** Transposed reverse hinges kill exactly the gadgets whose
cancellations are letter identifications, at size one, and symmetric pairs at every size. They do not
reach products of length two or more. The one invariant found that reaches every size and every
entry pattern is coincidence modulo `Gamma_0`. Coincidence alone is blind from `r + s = 4` on. With
the idempotent law it excludes `r + s = 4` (`radu-lattice-one-sided-pairs-need-radius-five`).

## 5. The smallest nonlinear anchored gadget

Take the setting of `strict-pairs-transfer-to-table-realizations`: automata `tau`, `sigma` over
`Gamma_R` with memories `M`, `S` containing `1`, `sigma tau = id`, and a Garden of Eden `p` on a
window `Omega`. An identification `(s, m) ~ (s', m')`, meaning `s m = s' m'`, is anchored if exactly
one of `m, m'` is `1`. A table with no anchored identification carries a free `Z` factor
(Proposition 3.1 of `research/artifacts/table-abelianization-and-cell-count-2026-09-12.md`).

**Unit-ball addresses anchor nothing.** Suppose `S, M ⊆ B_1` and `s = s' m'` with `m' != 1`. Then
either `s' = 1` and `s = m'`, or `s' = m'` and `s = 1`, since `s' m'` has length two otherwise. So the
only anchored identifications are `(m, 1) ~ (1, m)` and `(1, 1) ~ (m, m)`, which every group
realizes. A gadget with any other anchored identification, such as `(hv, 1) ~ (h, v)`, has `S` or
`M` outside `B_1`.

**Invariant.** Put `H = <M ∪ S ∪ Omega>`. Then `H / (H ∩ Gamma_0)` embeds in `Gamma_R / Gamma_0`, so it
is residually finite, sofic and surjunctive. By Corollary 2 (quotient folding) of
`strict-pairs-transfer-to-table-realizations`, some `w, w'` in `Omega` with `p(w) != p(w')` have
`w^(-1) w' in Gamma_0 \ {1}`. Given Remark 3.6, `|w^(-1) w'| >= 8`. So every Garden of Eden window of
a strict pair on `Gamma_R` has diameter at least eight, and no window fits in a ball of radius three.

**Smallest survivor shape.** The screen allows a window in `B_4` whose pattern distinguishes `(zx)^2`
from `(xz)^2`. The smallest nonlinear anchored gadget that no known invariant excludes is:
memories and decoder in `B_2` with at least one anchored identification, and an orphan pattern on a
window in `B_4` separating two cells that differ by `delta^4`. Nothing here says such a pair exists.
The idempotent law behind `radu-lattice-one-sided-pairs-need-radius-five` is linear and does not
reach automata.

## 6. What stays open

- A one-sided pair over `F_p[Gamma_R]` at any size. A pair would make `Gamma_R` nonsurjunctive and
  so nonsofic (`radu-bmw-nonsurjunctivity-gives-nonsoficity`), which is open.
- Pairs at size `n >= 2` in the window `(B_1, B_1)` without Remark 3.6.
- Pairs at larger radius. Coincidence alone is blind from `r + s = 4`. The idempotent law of
  `radu-lattice-one-sided-pairs-need-radius-five` excludes `r + s = 4` given Remark 3.6, and
  `r + s = 5` under its hypothesis (H10). Its product-free criterion does not apply at `r + s = 6`.

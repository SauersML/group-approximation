---
rg: 2
id: mod-s2-bielliptic-centralizer-has-rational-h2
kind: claim
title: The centralizer of a bielliptic involution of Mod(S_2) has nonzero rational H^2, detected on two commuting twists about disjoint invariant curves
distinct_from:
  mod-s2-quasirep-windings-vanish-on-fixed-window: that shows every degree-two winding of Mod(S_2) itself vanishes because H_2(Mod(S_2);Q) = 0; this is the torsion sector at a bielliptic involution g, where H_2(Z(g);Q) is nonzero, so the delocalized Bott test is not inert.
  mod-s2-stability-forces-honest-torelli-windings: that pulls back Dadarlat windings of Sp_4(Z) in the trivial sector; this is a class in the sector of a finite-order element.
  weak-matricial-stability-kills-centralizer-even-cohomology: that is the open general vanishing statement; this is the nonvanishing input that makes it bite on Mod(S_2).
artifacts:
  - experiments/mod-s2-bielliptic-sector-2026-09-17/check.py
---

**ESTABLISHED** (route `mod-s2-bielliptic-centralizer-has-rational-h2-proof`).

**Setting.** `M = Mod(S_2)`. Let `psi : M -> Sp_4(Z)` be the action on `H_1(S_2;Z)`.

Let `g` be the deck involution of a double cover `S_2 -> E` of a torus, branched at two points. It is a *bielliptic
involution*: it has order 2 in `M` and exactly two fixed points.

Write `Z_M(g)` for its centralizer. In a symplectic basis `a_1, b_1, a_2, b_2` that `g` permutes as `a_1 <-> a_2`,
`b_1 <-> b_2`, put `J = psi(g)`.

**Claim.**
1. There are disjoint, `g`-invariant, nonseparating simple closed curves `c`, `c'` in `S_2` with
   `[c] = ±(a_1 + a_2)` and `[c'] = ±(b_1 - b_2)`. The Dehn twists `T_c`, `T_c'` commute and lie in `Z_M(g)`.
2. Let `iota : Z^2 -> Z_M(g)` send `e_1 -> T_c` and `e_2 -> T_c'`. Then `iota_*[Z^2]` is nonzero in
   `H_2(Z_M(g);Q)`. Hence `H^2(Z_M(g);Q) != 0`, and some class in it pairs to `1` with this torus.
3. The same holds one level down. `psi_* iota_*[Z^2]` is nonzero in `H_2(Z_{Sp_4(Z)}(J);Q)`, so
   `H^2(Z_{Sp_4(Z)}(J);Q) != 0`.

The class is pulled back along
`Z_M(g) -> Z_{Sp_4(Z)}(J) -> G_Delta = {(X,Y) in SL_2(Z)^2 : X = Y mod 2}`. The second map restricts to the
`(+1)`- and `(-1)`-eigenlattices of `J`. On `G_Delta` the class is the unique `SL_2(F_2)`-invariant pairing
`H_1(Gamma(2)) x H_1(Gamma(2)) -> Q`.

**Why it matters.**
- *It corrects recorded belief.* `mod-s2-is-point-norm-matricially-stable` (Evidence) says that "the known
  cohomological obstruction is absent". Two attempts on that node say every Bott test on commuting twists factors
  through `H_2(M;Q) = 0`, so a refutation "needs a torsion or non-cohomological invariant".
- *This is that torsion invariant.* Take any asymptotic homomorphism `V_n` of `M`. Compress
  `V_n(T_c)` and `V_n(T_c')` to the `(-1)`-eigenspace of `V_n(g)`. Their Bott index `beta_{-1}` is the invariant of
  `weak-matricial-stability-kills-centralizer-even-cohomology` (artifact Lemmas 1.1–1.4). It lives on
  `H_2(Z_M(g);Q)`, which item 2 shows is nonzero, not on `H_2(M;Q)`.
- *Route.* Route `mod-s2-instability-via-bielliptic-delocalized-dadarlat` combines items 1–2 with the open general
  vanishing claim and Bigelow–Budney linearity. It refutes the strong form of `mod-s2-is-point-norm-matricially-stable`.

**Consistency with the recorded kills (not a proof).**
- The total Bott index `beta_{+1} + beta_{-1}` of the uncompressed pair pairs with the image of the torus in
  `H_2(M;Q) = 0`. Granting additivity of Dadarlat's pairing, it vanishes, so `beta_{-1} = -beta_{+1}`.
- For models induced from a normal finite-index `N` with `g` not in `N`, `beta_{+1} = beta_{-1}` (Lemma 4.1 of
  `research/artifacts/laurent-sl4-delocalized-bott-2026-09-16.md`). So both vanish.
- A witness therefore has to be non-induced, exactly as in the `SL_4` lanes. This is the realization problem (P1)–(P3)
  of the general claim. It is not solved here.

**Exact value (heuristic, not established).** Kerckhoff's fixed-point theorem identifies `Fix(g)` in Teichmüller space
with a contractible copy of `Teich(S_(1,2))`. Kani's gluing of `E_1 = S_2/g` and `E_2 = S_2/(iota g)` along
2-torsion suggests the moduli of pairs `(C, g)` is `M_(0,5)/S_3`, with `S_3` permuting three of the five points.
Then `H^2(Z_M(g);Q) = H^2(M_(0,5);Q)^(S_3) = (wedge^2 std_4)^(S_3) = Q`.
- The same count with `S_2 x S_3`, which would also swap the two elliptic quotients, gives `0`.
- Every other finite-order conjugacy class of `M` has a quotient orbifold with at most four cone points. Its sector has
  no rational `H^2`.

If these recalled identifications hold, this is the only positive-degree even rational sector of `M`. It is exactly
one-dimensional.

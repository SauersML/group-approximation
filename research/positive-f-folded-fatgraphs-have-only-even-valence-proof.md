---
rg: 2
id: positive-f-folded-fatgraphs-have-only-even-valence-proof
kind: route
title: Sign-change corners sit at special 2-valent vertices; the certificate LP is exact
target: positive-f-folded-fatgraphs-have-only-even-valence
requires:
  - legal-f-folded-fatgraphs-give-surface-subgroups
artifacts:
  - experiments/legal-f-folded-fatgraphs-2026-09-17/lp5.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/exact_farkas.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/turn_graph_obstruction.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/scan4.py
---

Conventions follow `legal-f-folded-fatgraphs-give-surface-subgroups`.

- `f` is a positive automorphism on the rose, and `X` is an `f`-fatgraph satisfying (2),
  (3), (4). `L(x)` and `F(x)` are the last and first letters of `f(x)` for positive `x`.
- A letter is positive or negative. A *corner* of a boundary circle is a pair
  `(u, v)` of consecutive letters, and it is a *sign-change corner* when `u, v` have
  opposite signs.
- The boundary is `partial^-`, a union of circles `w`, together with `partial^+`, the
  corresponding circles `f(w)^{-1}` read without cancellation. On `partial^+` the
  corners are *junction corners* (between two blocks `f(x)^{-1}`; these are exactly the
  `f`-corners) or *interior corners* (inside a block).

**Step 1: corners at a vertex.** Let `v` be a vertex of valence `k`, with outgoing
directions `d_1, ..., d_k` in cyclic order. The boundary passes through `v` in `k`
corners. The corner between `d_s` and `d_{s+1}` reads `(d_s^{-1}, d_{s+1})`, so it
is a sign-change corner iff `d_s` and `d_{s+1}` have the *same* sign. The number of
sign alternations around a cycle is even. So the number of sign-change corners at `v`
is `≡ k (mod 2)`.

**Step 2: where sign-change corners can be.**

- Blocks `f(x)^{±1}` are single-signed, so interior corners never change sign.
- A sign-change corner of `partial^+` is therefore a junction corner, i.e. an
  `f`-corner.
- By (3) and (4), a vertex carries at most one `f`-corner and at most one
  `partial^-` corner. So it carries at most two sign-change corners.

**Step 3: the pairing.** Let `v` be the vertex of an `f`-corner. By (2) `v` is
2-valent, with directions `d_1, d_2` and corners `(d_1^{-1}, d_2)` and
`(d_2^{-1}, d_1)`. These two corners change sign simultaneously (both iff
`s(d_1) = s(d_2)`), and they are *inverse turns*: corner `(p, q)` is paired with
`(q^{-1}, p^{-1})`. So an `f`-corner that changes sign lies at a 2-valent vertex whose
other corner also changes sign. By (3) that other corner is not an `f`-corner. By
Step 2 it is not interior. Hence it is a `partial^-` corner.

This defines an injection from sign-change junction corners of `partial^+` to
sign-change corners of `partial^-`. Circle by circle the two sets have the same size:
the junction between `f(x_{t+1})^{-1}` and `f(x_t)^{-1}` changes sign iff `x_t, x_{t+1}`
do. So the injection is a bijection. Every sign-change corner of `partial^-` is
therefore at a *special* vertex: 2-valent, carrying one `f`-corner and one `partial^-`
corner.

**Step 4: parity.** A non-special vertex carries no sign-change corner: it has no
sign-changing `partial^-` corner by Step 3, and no sign-changing `f`-corner, since
those sit at special vertices. By Step 1 its valence is even and its directions
alternate in sign. Under (L) the `k/2` positive directions lie in distinct gates, and so
do the `k/2` negative ones. So `k <= 2 min(g_+, g_-)`, where `g_+` and `g_-` count
the gates of positive and negative directions. `chi(X) = sum_v (1 - k_v / 2)`. So
`min(g_+, g_-) <= 1` forces every vertex to be 2-valent and `chi(X) = 0`.

**Step 4b: the turn-graph bound.** Let `v` be a legal vertex of valence `k >= 4`. It carries no
`f`-corner, since `f`-vertices are 2-valent by (2). By (4) it carries at most one `partial^-`
corner. So at least `k - 1 >= 3` cyclically consecutive corners are interior corners of
`partial^+`. An interior corner lies inside a block `f(x)^{±1}`, so its turn is a turn taken
inside some word `f(x)`. Three consecutive corners involve four consecutive directions
`d_1, ..., d_4`, and consecutive pairs are taken turns. By Step 4 they alternate in sign, and by
(L) the two of each sign lie in distinct gates. Reversing the path if necessary, it starts
with a positive direction. `turn_graph_obstruction.py` tests for this path. It collects
turns from truncated iterates `phi^j(x)`, `j <= 8`. That is a subset of the turns of all iterates,
so a path it finds is a real path. In the census it found a path for every automorphism that
Step 4 did not kill. So part 3 kills nothing there, and no kill rests on the truncation.

**Step 5: Df-periodicity of sign-change turns.** Let `w = x_1 ... x_L`. The
junction corner between the blocks of `x_{t+1}` and `x_t` reads
`(F(x_{t+1})^{-1}, L(x_t)^{-1})`, with the convention `F(X) := L(x)^{-1}` and
`L(X) := F(x)^{-1}` on inverse letters. By Step 3 its partner is the corner with turn
`Df(x_t, x_{t+1}) := (L(x_t), F(x_{t+1}))`. When the corner changes sign, the partner is
a sign-change corner `sigma(t)` of `partial^-`. So `sigma` is a permutation of the
finite set of sign-change corners of `partial^-`, and the turn at `sigma(t)` is
`Df(turn at t)`. Iterating along a cycle of `sigma` gives `Df^r(turn) = turn`.

**Step 6: gates are power-invariant.** If `D^j d = D^j d'` then `D^{mj} d = D^{mj} d'`.
Conversely, equality under some power of `D^m` is equality under a power of `D`. So
`f^m` has the gates of `f`, and Step 4 applies to every power with the same
`(g_+, g_-)`.

**Step 7: fully irreducible and atoroidal from the matrix.** Let `M` be the transition
matrix of a positive automorphism `phi` of `F_3`. Assume `M` is primitive and its
characteristic polynomial `chi_M` is irreducible over `Q`.

- *Fully irreducible.* If `phi^k` preserved a proper free factor up to conjugacy, its
  image in `H_1 = Z^3` would be a nonzero proper `M^k`-invariant direct summand, and
  `chi_{M^k}` would have a factor over `Q` of degree 1 or 2. A reducible cubic has a
  rational root `mu^k`, where `mu` is a root of `chi_M`. That root is an algebraic
  integer unit, so `mu^k = ±1`. Then all Galois conjugates satisfy `|mu_i| = 1`, so all
  roots have modulus 1. That contradicts primitivity (Perron--Frobenius root `> 1`).
- *Atoroidal.* By Bestvina--Handel (standard, not re-read), a fully irreducible
  non-atoroidal `phi` of `F_3` is induced by a pseudo-Anosov map of a compact surface
  with one boundary component and `pi_1 = F_3`. That surface is `N_{3,1}`, since an
  orientable one has even rank. Its boundary word is `x^2 y^2 z^2` in some basis, and
  its class `2(x+y+z) ≠ 0` is fixed up to sign by `M`. Then `±1` is a root of `chi_M`,
  contradicting irreducibility.

Brinkmann's theorem (standard) makes `F_3 x|_phi Z` hyperbolic, and it is one-ended.
`scan4.py` checks exactly: positive words of length 2--4, `|det M| = 1`, automorphism
(Stallings folding), `M^9 > 0`, `chi_M` irreducible, and at least 4 gates.

**Step 8: the certificate LP is exact for one word.** Fix a primitive legal cyclic word
`w`. Boundaries `partial^- = N` copies of `w` are considered, each with its own
`partial^+ = f(w)^{-1}`.

- `w` is necessarily cyclically legal (L).
- `(I - M)[w] = 0`, and `I - M` is invertible because the irreducible cubic `chi_M`
  has no root 1. So `[w] = 0`.
- For legal `w` the circle `f(w)^{-1}` has no cancellation: a legal sign-change turn
  `(x, Y)` has `L(x) ≠ L(y)`.

Given such an `X`, project every vertex to its cyclic list of slots
`(d_s -> q_s)` on the base circles `w` and `f(w)^{-1}`. Here `q_s` is the dart paired
with `d_s`, and `d_{s+1} = next(q_s)`. Distinct gates give distinct labels, so a
vertex never contains two lifts of one base dart. The projected polygon satisfies:

- legality;
- at most one `partial^-` dart;
- if it has an `f`-dart, then it has exactly two slots;
- no slot pairs two `partial^-` darts (4);
- at least two slots (a 1-valent vertex would give a backtracking corner, which neither
  circle has);
- at most `2 min(g_+, g_-)` slots (Step 4).

These are exactly the polygons enumerated by `lp5.polygons`. Let `y_P` be the number
of vertices of type `P`, divided by `N`. Then:

- each dart has total weight 1;
- slot `d -> q` and slot `q -> d` have equal weight (every edge of `X` is counted once
  from each end);
- `sum_P y_P (1 - k_P / 2) = chi(X) / N`.

So a certificate with `chi < 0` gives a feasible LP with negative optimum. If
`w = v^j`, projecting modulo `|v|` gives a feasible LP for `v`, so primitive `w`
suffice. Farkas' lemma: the LP `A y = b, y >= 0` is infeasible iff some `z` has
`A^T z <= 0` and `b^T z > 0`. `exact_farkas.py` computes `z` in floating point,
rounds it to integers, and checks both inequalities in exact integer arithmetic. When
some dart lies in no admissible polygon, it uses `z = e_d`.

The converse direction is not needed for any claim here. An LP solution gives rational
vertex counts. Realising it as a fatgraph needs integral slot matchings and a cyclic
cover making the boundary circles read copies of `w`. That realisation is not
implemented.

**Calibration.** On the endomorphism `a -> ab, b -> ba` (Sapir's group), `lp5.py` at
`m = 2` finds `chi = -4` per copy for `w = ABABabab`, and `exact_farkas.py` reports
`lp-feasible` (no certificate), as it must. Squares:
`{a -> abb, b -> ba, c -> c}` gives `chi = -4` at `w = ABCbabcB`. The SAT search
`sat4.py`/`calib_sapir.py` independently finds an integral fatgraph for Sapir `phi^2`,
`w = babaBABA`, with `chi = -4`, and verifies that `X_n` immerses for `n <= 1`
(`calib_sapir_m2_k1.log`). `exact_farkas.py` on the Sapir control: `farkas_sapir_control.log`. `QED`

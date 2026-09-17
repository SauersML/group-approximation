---
rg: 2
id: c4-t4-power-presentations-are-not-infinite-torsion-proof
kind: route
title: Fine--Wilf gives C(4), the Whitehead graph gives T(4), and the Duda--Gui fixed-point theorem makes torsion groups finite
target: c4-t4-power-presentations-are-not-infinite-torsion
requires: []
---

Notation is that of the target claim. Throughout, `u_r` is cyclically reduced
and primitive (not a proper power), roots are pairwise not cyclically
conjugate to each other or to each other's inverses, and `n_r l_r >= 3`
(so that relator cycles are simplicial graphs; relators `a` or `a^2` with
`l_r = 1` are excluded, the first being a Tietze move anyway).

## 0. Classical and graphical formulation

`Theta` is the rose on `X`. `Gamma_r` is the cycle graph with `n_r l_r`
vertices whose edges, read around the cycle, spell `u_r^(n_r)`; `f_r :
Gamma_r -> Theta` sends each edge to the petal of its label. `f_r` is an
immersion because `u_r^(n_r)` is cyclically reduced (as `u_r` is). The group
defined by `f = sqcup f_r : Gamma -> Theta` is `G(P)`.

- *Simplicial*: `Gamma_r` is a cycle of length `n_r l_r >= 3`.
- *Finite components*: `k` finite cycles.
- *Simplified*: an isomorphism `Gamma_r -> Gamma_s` over `Theta` identifies
  the cyclic word `u_r^(n_r)` with `u_s^(n_s)` or `u_s^(-n_s)`. The primitive
  root of a nonempty cyclic word is unique up to cyclic conjugacy
  (Lyndon--Schutzenberger), so `u_r` is cyclically conjugate to `u_s^(±1)`,
  and `r = s` by hypothesis.
- *Label-preserving automorphisms* of `Gamma_r` are the rotations by
  multiples of `l_r` (rotation by `j` preserves labels iff `u_r^(n_r)` equals
  its cyclic shift by `j`, iff `l_r | j` by primitivity of `u_r`); there are
  no label-preserving reflections, since a reflection would make
  `u_r^(n_r)` cyclically conjugate to `u_r^(-n_r)`, impossible for a nonempty
  reduced word (see Lemma 1(ii)).

**Pieces.** A *piece* is a labelled path `p` (a freely reduced word) with two
lifts `p -> Gamma_r`, `p -> Gamma_s` (immersions over `Theta`) that do not
differ by an isomorphism `Gamma_r -> Gamma_s` over `Theta`. By the above this
means: either `r != s`, or `r = s` and the two lifts differ by an orientation
reversal or by a rotation by `j` with `l_r` not dividing `j`. For the
classical case this is exactly the Lyndon--Schupp notion: a common prefix of
two distinct elements of the symmetrized closure `R` of the relators.

## 1. The pieces lemma

**Fine--Wilf theorem (imported; Lyndon--Schupp, *Combinatorics on Words*
Ch. 1).** If a word `w` has periods `p` and `q` and `|w| >= p + q -
gcd(p, q)`, then `w` has period `gcd(p, q)`.

**Primitivity facts.** A cyclic conjugate of a primitive word is primitive; a
primitive word of length `l` differs from each of its cyclic shifts by `j`,
`0 < j < l`; a word of length `l` with period `g | l`, `g < l`, is a proper
power. (All standard.)

**Lemma 1.** Let `p` be a piece with lifts into `Gamma_r` and `Gamma_s`.

- (i) If `r = s` and the lifts have the same orientation, `|p| <= l_r - 1`.
- (ii) If `r = s` and the lifts have opposite orientations, `|p| <= l_r - 1`.
- (iii) If `r != s`, `|p| <= l_r + l_s - gcd(l_r, l_s) - 1`.

*Proof.* A lift of `p` into `Gamma_r` makes `p` a subword of the bi-infinite
periodic word `...u_r u_r u_r...` (or of `...u_r^(-1) u_r^(-1)...` for the
opposite orientation), so `p` has period `l_r`, and its prefix of length
`l_r`, when `|p| >= l_r`, is a cyclic conjugate of `u_r^(±1)`, and determines
the lift up to rotation by a multiple of `l_r`.

(i) If `|p| >= l_r`, the length-`l_r` prefix of `p` is read from two starting
positions `i, i'` of `Gamma_r`, so it equals both the shift of `u_r` by `i`
and by `i'`; primitivity gives `l_r | i - i'`, so the lifts differ by a
label-preserving rotation, and `p` is not a piece.

(ii) If `|p| >= l_r`, the length-`l_r` prefix of `p` is a cyclic conjugate
of `u_r` and of `u_r^(-1)`, so `u_r^(-1)` is a cyclic conjugate of `u_r`:
`u_r = s t` and `u_r^(-1) = t s` for some split. Since `u_r^(-1) = t^(-1)
s^(-1)` and `|t| = |t^(-1)|`, comparing letters gives `t = t^(-1)` and `s =
s^(-1)` as words. A nonempty freely reduced word is never letterwise equal to
its inverse (for odd length the middle letter would be its own inverse, for
even length the two middle letters would cancel). So `s` and `t` are empty,
contradicting `l_r >= 1`.

(iii) If `|p| >= l_r + l_s - gcd`, Fine--Wilf gives `p` period `g = gcd`. The
length-`l_r` prefix of `p`, a cyclic conjugate of `u_r^(±1)`, has period `g |
l_r`; being primitive, `g = l_r`. Likewise `g = l_s`. So `l_r = l_s` and the
length-`l_r` prefix of `p` is a cyclic conjugate of `u_r^(±1)` and of
`u_s^(±1)`, so `u_r` is cyclically conjugate to `u_s` or `u_s^(-1)`,
contradicting the hypothesis. ∎

## 2. (C4) implies C(4)

Graphical C(4): no immersed cycle in `Gamma` is a concatenation of fewer than
4 pieces. The immersed cycles of `Gamma_r` go around the cycle `m >= 1`
times and have length `m n_r l_r >= n_r l_r`. A concatenation of at most 3
pieces, each lifting into `Gamma_r` on one side, has length at most
`3 max(l_r - 1, max_(s != r) (l_r + l_s - gcd(l_r, l_s) - 1))` by Lemma 1,
which is `< n_r l_r` by (C4). ∎

In the classical language: no element of `R` is a product of fewer than
4 pieces.

## 3. Triangle-free Whitehead graph implies T(4)

**Proposition 3.** If `W(P)` has no triangle, every interior vertex of every
disc diagram over `P` (reduced or not) has degree different from 1 and 3.

*Proof.* Work in a disc diagram `D` whose 2-cells are bounded by relator
cycles; subdivide so that each edge carries one letter. Let `v` be an
interior vertex and `e_1, ..., e_d` its incident edges in cyclic order
(an edge with both ends at `v` counts twice). Orient every `e_i` away from
`v` and let `x_i in X^(±1)` be the label read along `e_i` from `v`. Between
`e_i` and `e_(i+1)` lies a corner of a 2-cell `F_i` (indices mod `d`); going
around `bd F_i` through this corner one reads `x_i^(-1) x_(i+1)` (or its
inverse, for the other orientation). This is a cyclic 2-letter subword of
`u_r^(n_r)` or `u_r^(-n_r)` (equivalently a 2-letter subword of
`u_r u_r` or `u_r^(-1) u_r^(-1)`), for the relator of `F_i`.
By definition of `W(P)` (edge `{y, z^(-1)}` for a subword `yz`), the pair
`{x_i^(-1), x_(i+1)^(-1)}` is an edge of `W(P)`. The inverse reading
`x_(i+1)^(-1) x_i` gives the same edge.

Consecutive vertices of the closed walk `x_1^(-1), x_2^(-1), ...,
x_d^(-1)` are distinct: `x_i = x_(i+1)` would make `x_i^(-1) x_i` a subword
of a cyclically reduced relator. So `d = 1` is impossible (the single corner
would read `x_1^(-1) x_1`), and if `d = 3` the three vertices are pairwise
distinct (every pair is consecutive) and span a triangle in `W(P)`. ∎

So interior vertices have degree 2 or at least 4 in every disc diagram, in
particular in every reduced one, which is graphical T(4). Equivalently, in
Lyndon--Schupp's algebraic form: if `r_1, r_2, r_3 in R` and all of `r_1
r_2`, `r_2 r_3`, `r_3 r_1` have cancellation, with last letters `e_i` and
first letters `f_i`, then `e_1 = f_2^(-1)`, `e_2 = f_3^(-1)`, `e_3 =
f_1^(-1)`; the cyclic subword `e_i f_i` of `r_i` gives the edges `{e_2,
e_1}`, `{e_3, e_2}`, `{e_1, e_3}`, and `e_i != e_(i+1)` since `e_(i+1) f_(i+1)`
is reduced; a triangle.

**Positive roots.** If every `u_r` is positive, each subword `yz` has `y, z
in X`, so each edge `{y, z^(-1)}` joins `X` to `X^(-1)`: `W(P)` is bipartite
and triangle-free.

**Equal lengths.** If all `l_r = l`, then `l_r + l_s - gcd - 1 = l - 1`,
and `3(l - 1) < n_r l` holds for every `n_r >= 3` (and for `n_r = 2` exactly
when `l <= 2`).

**Spread lengths.** `gcd >= 1` gives `l_r + l_s - gcd - 1 <= l_r + l_max - 2`,
and if `l_r >= l_max / 2` this is `< 3 l_r`, so `n_r >= 9` gives (C4) for `r`.

## 4. Torsion implies finite

**Duda--Gui, Theorem 1 (imported; K. Duda, H. Gui, *Local-to-global fixed
point properties for graphical C(4)-T(4) and C(6) small cancellation
complexes*, arXiv:2607.11360).** Torsion subgroups of groups defined by
C(4)--T(4) graphical small cancellation presentations are finite. The
standing hypotheses are: the presentation is simplified, `Gamma` is
simplicial, components are finite; classical presentations (rose `Theta`,
cycles `Gamma_i`), including proper powers, are covered.

By Section 0 the hypotheses hold; by Sections 2--3 the presentation is
graphical C(4)--T(4). Apply the theorem to the subgroup `G` itself: if `G` is
torsion, `G` is finite. Hence `G` is finite or has an element of infinite
order. ∎

## 5. Calibration and what is not covered

- Calibration: `<a | a^3>` (finite) and `<a, b | a^3, b^3>` (infinite, not
  torsion) satisfy the hypotheses and agree with the conclusion. Free Burnside
  relator sets `{w^n : |w| <= L}`, `L >= 2`, `|X| >= 2`, violate (T4): the
  roots `a`, `a b^(-1)`, `b a` give the edges `{a, a^(-1)}`, `{a, b}`,
  `{b, a^(-1)}`, a triangle. So the theorem does not collide with Adian or
  Olshanskii groups.
- The obstruction is insensitive to how the presentation was found (towers,
  limits, HNN tricks, computer search): only the root data enter.
- Not covered: (T4) failing (mixed-sign roots with a Whitehead triangle),
  and exponents too small against root lengths. The graphical C(6) theorem
  of Duda--Gui needs "torsion-essentially C(6)-free", which fails for every
  proper-power cell (each cell has a nontrivial rotation stabilizer), so it
  adds nothing here; C(6) alone is not enough for this route.
- Scope: for power presentations whose roots mix signs freely, (T4)
  typically fails once there are many roots, so the obstruction is about
  sparse or sign-structured presentations; it kills positive (monoid-type) power presentations with
  exponent at least 3 and equal root lengths completely.

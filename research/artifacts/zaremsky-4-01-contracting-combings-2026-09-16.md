# Contracting combings for Zaremsky Problem 4.1: the definition, l-infinity lattice groups, and an l1-product obstruction

2026-09-16, swarm lane `swarm-zaremsky-4-01-amenable-automat`, working on the hole
`amenable-automatic-groups-admit-contracting-combings`.

- **Proved:** Theorem 3. Groups acting transitively on `Z^n` by signed-permutation
  integral affine maps, with finite stabilizers, admit contracting combings for every
  constant `C >= 2`. This covers `Z^n` with the l-infinity generators, `Z^n x F`,
  `Z^n ⋊ P` for any finite `P -> B_n`, the Klein bottle group and the scaled
  `4_1`-screw group.
- **Proved:** Theorem 5. If `G` and `H` are infinite, then the word metric of `G x H`
  for the disjoint union of generating sets admits no contracting combing. In
  particular `Z^d` (`d >= 2`) with the standard generators has none, and neither
  does a right-angled Artin group on a join, with its standard generators.
- **Proved:** Proposition 1. The version of the definition recorded in the graph
  before today, with `n <= n'`, is satisfied only by finite groups. The source
  says `n' <= n`.
- **Not proved:** the hole itself, even for all virtually abelian groups. See Section 6.

## 0. Source and conventions

**Source read.** M. C. B. Zaremsky, *Bestvina–Brady discrete Morse theory and
Vietoris–Rips complexes*, arXiv:1812.10976v3, Section 6.1. The text was extracted
from the v3 PDF with pypdf on 2026-09-16. Extracted lines 873–884 (verbatim, up to
extraction spacing):

> a path in G is an eventually constant map p : N0 → G such that d(p(n), p(n + 1)) ≤ 1
> for all n ∈ N0. Let P(G) be the set of all paths p with p(0) = 1, and define
> π : P(G) → G by sending p to p(n) for n large enough that p(n) = p(n + 1) = · · · .
> Now a combing of G is a section s : G → P(G) of π. [...] A combing s is contracting
> if there exists C ≥ 2 such that for all g, h ∈ G and n, n′ ∈ N0, with n′ ≤ n and
> ⌊C/2⌋ ≤ n, if d(s(g)(n), s(h)(n′)) ≤ C then also d(s(g)(n − ⌊C/2⌋), s(h)(n′)) ≤ C.

This is followed by Citation 6.7 (Alonso, *Combings of groups*, MSRI Publ. 23, 1992,
Theorem 1). Alonso's paper itself was not read. Everything below is about the
definition exactly as Zaremsky states it, which is the definition the graph cites.

**Conventions.**
- `G` is finitely generated, `d` is the word metric for a fixed finite generating
  set, and `|g| = d(1, g)`.
- A contracting combing "with constant `C`" satisfies the condition above for that
  `C`. Write `c = ⌊C/2⌋`, so `c >= 1`.
- For a combing `s` and `x ∈ G`, the arrival time is
  `T(x) = min{t : s(x)(u) = x for all u >= t}`. Since `s(x)(0) = 1`, `T(x) >= 1` for
  `x ≠ 1`.
- For `x ≠ 1`, write `p'(x) = s(x)(T(x) − 1)`. By minimality `p'(x) ≠ x`, so
  `d(p'(x), x) = 1`.
- For `v ∈ Z^n` and an integer `r >= 0`, the clamp `κ_r(v)` is the vector with
  coordinates `max(−r, min(r, v_i))`. `‖v‖_∞ = max_i |v_i|`.
- `B_n` is the group of signed permutation matrices. These are exactly the linear
  isometries of `(R^n, ‖·‖_∞)` that preserve `Z^n`, and they fix `{−1,0,1}^n`
  setwise.

## 1. The reversed reading is degenerate

**Proposition 1.** Suppose a combing `s` of `G` satisfies the following condition,
which reverses the order of `n` and `n'`. There is `C >= 2` such that for all `g, h`
and all `n <= n'` with `c <= n`, `d(s(g)(n), s(h)(n')) <= C` implies
`d(s(g)(n − c), s(h)(n')) <= C`. Then `|g| <= C + c − 1` for every `g`, so `G` is
finite.

*Proof.* Fix `g` and choose `N >= max(c, T(g))`, so `s(g)(N) = g`. Set `n_k = N − kc`
and let `K >= 1` be the largest index with `n_{K−1} >= c`.

We show by induction on `k = 1, ..., K` that `d(s(g)(n_k), g) <= C`.
- For `k = 1`, apply the condition with `h = g`, `n = n' = N`. The hypothesis
  `d(g, g) = 0 <= C` holds.
- If `d(s(g)(n_{k−1}), g) <= C` and `n_{k−1} >= c`, apply the condition with `h = g`,
  `n = n_{k−1}` and `n' = N`. Here `n <= n'`, and
  `d(s(g)(n), s(g)(n')) = d(s(g)(n_{k−1}), g) <= C`. It gives
  `d(s(g)(n_k), g) <= C`.

At the end, `m = n_K` satisfies `0 <= m < c`. Since `s(g)(0) = 1` and steps have
length at most `1`, `|s(g)(m)| <= m <= c − 1`. So
`|g| <= |s(g)(m)| + d(s(g)(m), g) <= c − 1 + C`. ∎

So under the reading `n <= n'` that the graph recorded before 2026-09-16:
- the claim `contracting-combings-give-contractible-rips-complexes` would concern only
  finite groups;
- the hole `amenable-automatic-groups-admit-contracting-combings` would be false,
  since `Z` is amenable, automatic and infinite.

The source reads `n' <= n`, and with that reading the theorem is the standard
"push the top vertex back" argument. Both nodes are corrected accordingly.

## 2. The clamp inequality

**Lemma 2.** Let `x, y ∈ Z`, and let `r' <= r` and `c` be integers with
`0 <= c <= min(r, C)`. If `|κ_r(x) − κ_{r'}(y)| <= C`, then
`|κ_{r−c}(x) − κ_{r'}(y)| <= C`.

*Proof.* Put `a = κ_r(x)`, `b = κ_{r'}(y)` and `a' = κ_{r−c}(x)`. Since `r − c <= r`,
clamps nest, so `a' = κ_{r−c}(a)`. Also `|b| <= r' <= r`.
- If `|a| <= r − c`, then `a' = a` and there is nothing to prove.
- Suppose `a > r − c`, so `a' = r − c`.
  - If `b <= r − c`, then `0 <= a' − b < a − b <= C`.
  - If `b > r − c`, then `0 < b − a' = b − r + c <= r' − r + c <= c <= C`.
- The case `a < −(r − c)` is symmetric. ∎

Applied coordinatewise, for vectors `u, v ∈ Z^n` with `r' <= r` and `c <= min(r, C)`:
`‖κ_r(u) − κ_{r'}(v)‖_∞ <= C` implies `‖κ_{r−c}(u) − κ_{r'}(v)‖_∞ <= C`.

## 3. Transitive signed-permutation actions on Z^n

**Theorem 3.** Let a group `G` act on `Z^n` by maps `g(v) = A_g v + t_g` with
`A_g ∈ B_n` and `t_g ∈ Z^n`. Assume the action is transitive and the stabilizer
`G_0` of `0` is finite. Let `S = {g ∈ G ∖ {1} : ‖t_g‖_∞ <= 1}`, and let `d` be the
word metric of `S`. Then:

- (a) `S` is a finite generating set, and `d(g, h) = max(‖t_g − t_h‖_∞, 1)` for
  `g ≠ h`.
- (b) For every `C >= 2`, `G` admits a combing, geodesic for `d`, that is
  contracting with constant `C`.

*Proof of (a).* We have `t_g = g(0)` and `t_{gh} = t_g + A_g t_h`.
- Also `t_g = t_{g'}` if and only if `g^-1 g' ∈ G_0`. So `S` lies in the finitely
  many cosets `g G_0` with `t_g ∈ {−1,0,1}^n`, and `S` is finite. It is symmetric,
  because `t_{g^-1} = −A_g^-1 t_g` has the same norm as `t_g`.
- *Lower bound.* If `k = s_1 ⋯ s_L` with `s_i ∈ S`, then
  `t_k = Σ_i A_{s_1⋯s_{i−1}} t_{s_i}`. Each term has norm at most `1`, so
  `‖t_k‖_∞ <= L`.
- *Upper bound.* Let `k ≠ 1` and `L = ‖t_k‖_∞`.
  - If `L = 0`, then `k ∈ G_0 ∖ {1} ⊆ S`, so `|k| = 1`.
  - If `L >= 1`, set `x_i = κ_i(t_k)` for `0 <= i <= L`. Then `x_0 = 0`, `x_L = t_k`
    and `‖x_i − x_{i−1}‖_∞ <= 1`. By transitivity choose `g_i` with `t_{g_i} = x_i`,
    taking `g_0 = 1` and `g_L = k`. Then `s_i = g_{i−1}^-1 g_i` has
    `t_{s_i} = A_{g_{i−1}}^-1 (x_i − x_{i−1})`, of norm at most `1`. So each
    `s_i ∈ S ∪ {1}`, and `k = s_1 ⋯ s_L`.

  Hence `|k| = max(‖t_k‖_∞, 1)`, and `S` generates `G`.
- *Metric.* For `g ≠ h`, `d(g, h) = |g^-1 h|` and
  `t_{g^-1 h} = A_g^-1 (t_h − t_g)`, whose norm is `‖t_h − t_g‖_∞`. ∎

*Proof of (b).* Choose a map `σ : Z^n → G` with `t_{σ(v)} = v` and `σ(0) = 1`. Define
`s(g)(0) = 1`, and for `m >= 1`:

- `s(g)(m) = g` if `m >= ‖t_g‖_∞`;
- `s(g)(m) = σ(κ_m(t_g))` otherwise.

In all cases `t_{s(g)(m)} = κ_m(t_g)`.

1. *It is a combing.* Consecutive translation parts `κ_m(t_g)` and `κ_{m+1}(t_g)`
   differ by at most `1` in norm, so by (a) consecutive values are at distance at most
   `1`. The path is constant equal to `g` from time `max(‖t_g‖_∞, 1)` on. It is
   geodesic: `|s(g)(m)| = max(min(m, ‖t_g‖_∞), [s(g)(m) ≠ 1])`, which equals `m` for
   `m <= |g|`.
2. *It is contracting.* Let `C >= 2`, and let `n' <= n` with `c <= n`. Suppose
   `d(s(g)(n), s(h)(n')) <= C`. By (a), `‖κ_n(t_g) − κ_{n'}(t_h)‖_∞ <= C`, and
   `c <= min(n, C)`. By Lemma 2, `‖κ_{n−c}(t_g) − κ_{n'}(t_h)‖_∞ <= C`. By (a) again,
   `d(s(g)(n − c), s(h)(n')) <= max(C, 1) = C`. ∎

The combing does not depend on `C`. So one combing is contracting for every
constant at once.

**Examples.**

- **(i) `Z^n` with the l-infinity generators.** Translations only;
  `S = {−1,0,1}^n ∖ {0}` and `d(u, v) = ‖u − v‖_∞`.
- **(ii) `Z^n ⋊_ρ F`.** Here `F` is finite and `ρ : F → B_n` is any homomorphism; the
  element `(v, f)` acts by `w ↦ ρ(f) w + v`. The stabilizer is `F`. This includes
  `Z^n x F` (take `ρ` trivial) and every split crystallographic group with
  signed-permutation point group, in lattice coordinates.
- **(iii) The Klein bottle group.** `K = {(m, k) ∈ Z^2}` with
  `(m, k)(m', k') = (m + (−1)^k m', k + k')`, acting by
  `(x, y) ↦ ((−1)^k x + m, y + k)`. This is `⟨a, b | b a b^-1 = a^-1⟩` with `a = (1,0)`
  and `b = (0,1)`: `b a b^-1 = (−1, 0) = a^-1`. The action is simply transitive and
  `S = {(m, k) ≠ 0 : |m|, |k| <= 1}`. `K` is not split.
- **(iv) Scaled `4_1` screw group.** `{(a, b, k) ∈ Z^3}` acting by `v ↦ R^k v + (a, b, k)`,
  where `R(x, y, z) = (−y, x, z)`. The action is simply transitive and the group is
  torsion-free with holonomy `C_4`.

*Scope.* Every such `G` is virtually `Z^n`: the translation subgroup
`{g : A_g = 1}` has finite index and its orbit of `0` has finite index in `Z^n`. The
theorem does not cover:
- the plane groups containing `p3`, namely `p3`, `p3m1`, `p31m`, `p6` and `p6m` (see the
  referee correction below; the original text also listed "the other trigonal and
  hexagonal groups", which is too broad in dimension 3);
- other finite generating sets of the covered groups.

A properly acting virtually-`Z^2` group transitive on `Z^m` must have `m = 2`, since
they are quasi-isometric. `B_2` has no element of order `3`, so `p3` is not covered
in any coordinates.

*(Referee correction, 2026-09-16.)* The last sentence needs two more steps, and the
original claim that all trigonal and hexagonal groups are excluded was too broad.
- *Why `p3` is not covered.* Suppose a plane group `G ⊇ p3` is covered. Then `G` is virtually
  `Z^2`, so `n = 2`, and `p3` acts on `Z^2` with finite stabilizers. Every rotation of
  order 3 maps to `1` in `B_2`. `p3` is generated by its rotations of order 3: if `r`
  is one, so is `tr` for every translation `t`, since `(tr)^3` is translation by `(1 + r + r^2)t = 0`.
  Then `t = (tr) r^-1` lies in the subgroup they generate. So `p3` acts by translations. Its commutator subgroup, which contains the infinite
  lattice `(1 − r)Λ`, then fixes `0`, contradicting finite stabilizers. This covers
  `p3`, `p3m1`, `p31m`, `p6` and `p6m`.
- *What is covered.* In dimension 3, `Z^3 ⋊ C_3`, with `C_3` cyclically permuting the
  coordinates, is example (ii). That is a rhombohedral trigonal group in its primitive
  basis. A referee script checked the metric formula and the contracting condition on
  a window, with `C = 2, 3, 4` and 0 failures.
- *Open boundary.* Transitivity only forces the translation orbit to have finite index
  in `Z^n`, not to be the whole lattice. So it is not settled here which other
  3-dimensional trigonal and hexagonal groups are covered.

## 4. The arrival rule

**Lemma 4.** Let `s` be a contracting combing with constant `C`. Let `x ≠ 1`, and let
`q` satisfy `d(x, q) <= C` and `d(p'(x), q) > C`. Then `T(q) >= T(x) + c`.

*Proof.* Suppose `T(q) <= T(x) + c − 1 =: n`.
- `n >= c`, since `T(x) >= 1`.
- With `n' = n`, `s(x)(n) = x` and `s(q)(n') = q`, so
  `d(s(x)(n), s(q)(n')) = d(x, q) <= C`.
- But `s(x)(n − c) = s(x)(T(x) − 1) = p'(x)` is at distance `> C` from `q`.

This contradicts the contracting condition. ∎

Informally: stepping back from an endpoint must not lose any `C`-neighbour that has
already arrived. In a tree this is automatic: a neighbour beyond `x` as seen from
`p'(x)` lies in the subtree at `x`, so it is far from the root. In flat directions it
fails, as follows.

## 5. l1-products admit no contracting combing

**Theorem 5.** Let `G` and `H` be infinite groups with finite generating sets `S_G`
and `S_H`. Give `G x H` the generating set `(S_G x {1}) ∪ ({1} x S_H)`, whose word
metric is `d((g,h), (g',h')) = d_G(g, g') + d_H(h, h')`. Then no combing of `G x H`
is contracting, for any constant `C >= 2`.

*Proof.* Suppose `s` is contracting with constant `C`. For `x ≠ 1`, `p'(x)` is
adjacent to `x`, so it differs from `x` in exactly one factor. Call that factor
`α(x) ∈ {G, H}`. Call `q` a *`β`-move of `x` by `C`* if `q` agrees with `x` in the
factor other than `β`, and its `β`-coordinate is at distance exactly `C` from that
of `x`.

- **Claim 1.** If `x ≠ 1`, `β ≠ α(x)` and `q` is a `β`-move of `x` by `C`, then
  `T(q) >= T(x) + c`.

  *Proof.* `d(x, q) = C`. `p'(x)` differs from `x` by `1` in factor `α(x)`, and `q`
  differs from `x` by `C` in the other factor `β`, so `d(p'(x), q) = C + 1 > C`.
  Apply Lemma 4. ∎
- **Claim 2.** If moreover `q ≠ 1`, then `α(q) = β`.

  *Proof.* Otherwise `α(q) = α(x) ≠ β`. Since `x` is a `β`-move of `q` by `C`,
  Claim 1 at `q` gives `T(x) >= T(q) + c >= T(x) + 2c`, which is impossible. ∎

Since `G` and `H` are infinite, every sphere in them is nonempty.
- Choose `g ∈ G` with `|g| > C` and `g' ∈ G` with `d_G(g, g') = C`.
- Choose `h ∈ H` with `|h| > C` and `h' ∈ H` with `d_H(h, h') = C`.

Then `g, g', h, h'` are all nontrivial, so the four points `(g,h)`, `(g',h)`,
`(g',h')`, `(g,h')` are nontrivial. Let `x_0 = (g, h)`. By symmetry of the roles of
`G` and `H`, assume `α(x_0) = G`. Apply Claims 1 and 2 around the square:

| step | point | move | new time bound | new last-step factor |
| --- | --- | --- | --- | --- |
| 1 | `x_1 = (g, h')` | `H`-move of `x_0` | `T(x_1) >= T(x_0) + c` | `α(x_1) = H` |
| 2 | `x_2 = (g', h')` | `G`-move of `x_1` | `T(x_2) >= T(x_1) + c` | `α(x_2) = G` |
| 3 | `x_3 = (g', h)` | `H`-move of `x_2` | `T(x_3) >= T(x_2) + c` | `α(x_3) = H` |
| 4 | `x_0 = (g, h)` | `G`-move of `x_3` | `T(x_0) >= T(x_3) + c` | |

At each step the move is in the factor other than the current last-step factor, as
Claim 1 requires. Chaining the four inequalities gives `T(x_0) >= T(x_0) + 4c`,
which is impossible since `c >= 1`. ∎

**Corollary 5′.**
- (i) For `d >= 2`, `Z^d` with the standard generators `{±e_1, ..., ±e_d}` admits no
  contracting combing. Write it as `Z x Z^{d−1}` with the disjoint union of the
  standard generating sets.
- (ii) If a finite graph `Γ` is a join of two nonempty graphs, the right-angled Artin
  group `A_Γ` with its standard generators admits no contracting combing. This
  includes `F_2 x F_2`.
- (iii) Consequently, whether a group admits a contracting combing depends on the
  generating set. `Z^2` has one for `{−1,0,1}^2 ∖ {0}` (Theorem 3) and none for
  `{±e_1, ±e_2}`.

## 6. Consequences for the hole and what remains

1. **The generating set in the hole must be chosen.**
   `amenable-automatic-groups-admit-contracting-combings` quantifies over some
   finite generating set, and Corollary 5′(iii) shows this is necessary. A strategy
   that keeps the generating set of a given automatic structure and improves its
   combing cannot work in general. `Z^2` is automatic with respect to
   `{±e_1, ±e_2}`, yet it has no contracting combing for that set.
2. **Virtually abelian groups are not a dead end for this route.** The earlier
   Attempts note said no contracting combing was recorded for any virtually abelian
   group. Theorem 3 supplies them for a broad class, including holonomy that is not
   split. The remaining virtually abelian cases include the plane groups containing `p3`, such
   as `p3` and `p6`, which Theorem 3 cannot cover in any coordinates (referee
   correction in Section 3), and possibly some 3-dimensional trigonal and hexagonal
   groups. For those, another generating set and combing would be needed. No construction or obstruction
   is known here for those.
3. **The hole is still open.** An affirmative answer for all amenable automatic groups
   would still need either:
   - a structure theorem, `amenable-automatic-groups-are-virtually-abelian`, which is
     open and would already settle Problem 4.1 through the existing route; or
   - a combing construction from amenability plus automaticity, for which no
     mechanism is known.
4. **Relation to Zaremsky Problem 4.5.** Corollary 5′(ii) shows that Alonso's
   theorem, used with the standard generators, cannot give type R for join RAAGs. It
   does not decide Problem 4.5 either way.

## 7. Computations (evidence, not proof)

Script: `experiments/zaremsky-4-01-contracting-combings-2026-09-16/check_combings.py`.
It runs single-threaded, in about 45 seconds, and exits `0`.

- **Part 1.** Lemma 2, exhaustively for `|x|, |y| <= 16`, `r <= 14` and `2 <= C <= 7`:
  762300 cases, 0 failures.
- **Part 2.** Breadth-first search on balls, for:
  - `Z^2` (l-infinity);
  - `Z^2 x Z/3`;
  - `Z^2 ⋊ B_2`;
  - the Klein bottle group;
  - the scaled `4_1` screw group.

  The search confirms the metric formula of Theorem 3(a) on the ball. The clamp
  combing is a combing and is contracting for `C = 2, 3, 4, 5` on windows
  `‖t‖_∞ <= 3` (`<= 2` in dimension 3), with 0 failures.
- **Part 3.** For geodesic combings of `Z^d` with the standard generators, the
  interior backward vectors `w` that survive the local constraint:
  - none for `d = 3, 4` and any `C` in `2..9`;
  - `(c/2, c/2)` only, for `d = 2` with `c` even.

  This is a weaker precursor of Theorem 5.
- **Part 4.** One candidate geodesic combing of `Z^2` with the standard generators
  fails for `C = 4, 5`, as Theorem 5 predicts.
- **Part 5.** The square construction in the proof of Theorem 5 is run as a
  certificate generator against four combings of `Z^2` with the standard generators:
  shortlex, axis-then-staircase, a lazy emulation of the l-infinity clamp, and a
  slowed shortlex. The certificate is re-verified by direct evaluation. A violation is
  found for every `C` in `2..7` at every test point.

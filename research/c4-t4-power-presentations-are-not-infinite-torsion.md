---
rg: 2
id: c4-t4-power-presentations-are-not-infinite-torsion
kind: claim
title: A proper-power presentation with exponents at least 3 against its root lengths and a triangle-free Whitehead graph of roots never defines an infinite torsion group
distinct_from:
  cprime-one-sixth-presentations-hyperbolic-and-torsion-free: that assumes the metric C'(1/6) condition on the relator words and forbids proper powers; this allows proper powers, needs only exponent inequalities of the size 3 (not 6) on the root lengths plus a triangle-free Whitehead graph, so the metric condition may fail (all positive equal-length power presentations with exponent 3 are covered).
  fp-torsion-group-is-no-limit-of-non-torsion-groups: that kills torsion groups reached as limits; this kills finite power presentations with a combinatorial root condition, whatever route produced them.
  partial-burnside-presentations-are-golod-shafarevich: that is about growth of partial Burnside relator sets; this is a finiteness theorem for torsion groups defined by power presentations satisfying a root-length and Whitehead-graph condition.
---

**ESTABLISHED (proposed; imports classical C(4)--T(4) diagram theory and
Duda--Gui, arXiv:2607.11360, Theorem 1: torsion subgroups of groups given by
C(4)--T(4) graphical small cancellation presentations are finite).** Full
proof: `c4-t4-power-presentations-are-not-infinite-torsion-proof`.

**Setup.** `P = < X | u_1^(n_1), ..., u_k^(n_k) >`, `X` finite, each root
`u_r` a cyclically reduced word that is not a proper power, `l_r = |u_r|`,
`n_r >= 1`, `n_r l_r >= 3`, and no two distinct roots cyclically conjugate to each other or to
each other's inverses. Every finitely presented group has such a presentation
(take `n_r = 1`), so the conditions below carry all the weight.

The *Whitehead graph* `W(P)` is the simple graph on `X^(±1)` with an edge
`{y, z^(-1)}` for every 2-letter subword `yz` of every `u_r u_r` and
`u_r^(-1) u_r^(-1)` (the cyclic 2-letter subwords of the relators).

**Theorem S.** Suppose

```text
(C4)  3 (l_r - 1) < n_r l_r,  and  3 (l_r + l_s - gcd(l_r, l_s) - 1) < n_r l_r  for all s != r,
(T4)  W(P) contains no triangle.
```

Then `G(P)` is finite or contains an element of infinite order.

**Corollaries.**

1. *(Positive roots.)* If every `u_r` is a positive word, `W(P)` is
   bipartite (`X` against `X^(-1)`), so (T4) holds and only (C4) is needed.
2. *(Equal root lengths.)* If all `l_r` are equal, (C4) holds whenever
   `n_r >= 3` for all `r`.
3. *(Positive Burnside-type presentations are dead.)* A finite presentation
   `< X | w^3 : w in W >` (or any exponents `>= 3`), `W` a set of positive,
   primitive, pairwise non-cyclically-conjugate words of one length, defines
   a finite group or a group with an element of infinite order. So no finite
   truncation of a Burnside-type relator set along positive words of fixed
   length can answer Problem 1.11, whatever the exponents and alphabet.
4. *(Spread lengths.)* Since `gcd >= 1`, (C4) holds as soon as
   `n_r l_r > 3 (l_r + l_max - 2)` for every `r`, `l_max = max_s l_s`; for a
   root with `l_r >= l_max / 2`, `n_r >= 9` suffices.

**Where it fails, and what a Problem 1.11 answer in power form must look like.**
A finitely presented infinite torsion group given by a power presentation
with pairwise non-conjugate primitive roots must have (i) a triangle in the
Whitehead graph of its roots, i.e. letters `a, b, c` in `X^(±1)` and three
roots containing cyclic subwords `a b^(-1)`, `b c^(-1)`, `c a^(-1)` (after
inversion), so it genuinely mixes signs; or (ii) some root with
`n_r l_r <= 3 (l_r + l_s - gcd - 1)` against another root, i.e. an exponent
too small for its length (when lengths agree: `n_r = 1`, or `n_r = 2` with
`l_r >= 3`; otherwise typically a short root facing a long one). The standard relator sets `{w^n}` for all words of a
length fail (T4) immediately, which is why the obstruction does not touch
free Burnside groups themselves.

**Why this is not the classical metric theory.** Classical C'(1/6) (with
proper powers) gives hyperbolicity and needs pieces `< n_r l_r / 6`; here
pieces may be a third of the relator, so exponent 3 is allowed where the
metric theory needs exponent 6 or more. The new
input is (a) a Fine--Wilf pieces lemma that turns root data into C(4) with no
cancellation hypothesis on the relators, (b) the Whitehead-graph criterion
for T(4), and (c) the 2026 fixed-point theorem of Duda--Gui, which is what
converts "torsion" into "finite" outside the hyperbolic range.

**Model tests.**
- `<a | a^3>`: (C4) `0 < 3`, `W` = one edge `{a, a^(-1)}`; `G = Z/3`, finite.
- `<a, b | a^3, b^3>`: (C4) `0 < 3`, `W` bipartite; `G = Z/3 * Z/3` has
  `ab` of infinite order.
- Euclidean triangle group `<a, b | a^3, b^3, (ab)^3>`: for `r = a`,
  `s = ab`: `3 (1 + 2 - 1 - 1) = 3`, not `< 3`; (C4) fails, the theorem is
  silent (the group is infinite, not torsion, so nothing is contradicted).
- `A_4 = <a, b | a^3, b^3, (ab)^2>`: (C4) fails for `a^3` against `ab`;
  silent, consistent.

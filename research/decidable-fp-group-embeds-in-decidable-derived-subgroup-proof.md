---
rg: 2
id: decidable-fp-group-embeds-in-decidable-derived-subgroup-proof
kind: route
title: Twist the generators by a central Z so every Heisenberg edge has a decidable membership test
target: decidable-fp-group-embeds-in-decidable-derived-subgroup
requires: []
---

**Setup.** `H = <x_1..x_n | R>` is finite with solvable word problem, and
`H' = H x <t>`, which is finitely presented with solvable word problem. Its
generators are `y_0 = t` and `y_i = x_i t` for `1 <= i <= n`. They generate
`H'`, because `x_i = y_i y_0^{-1}`. The projection `pi : H' -> Z`, `t -> 1`,
is computable on words, and `pi(y_i) = 1`, so each `y_i` has infinite order.

**Membership in edge subgroups.** For a word `w` in `H'`, `w` lies in
`<y_i>` iff `w =_{H'} y_i^{pi(w)}`. A power `y_i^k` has projection `k`, so
`w = y_i^k` forces `k = pi(w)`. The test is one call to the word problem of
`H'`.

Let `B_i = <a_i,b_i | [a_i,[a_i,b_i]], [b_i,[a_i,b_i]]>` be the integral
Heisenberg group, realised as the upper unitriangular integer `3 x 3`
matrices. Then `z_i = [a_i,b_i]` is the elementary matrix `E_13`. It is
central, has infinite order, and lies in `[B_i,B_i]`. The word problem of
`B_i` is matrix multiplication. A word lies in `<z_i>` iff its matrix has zero
`(1,2)` and `(2,3)` entries, in which case the power is the `(1,3)` entry.

**The group.** Let `T_{-1} = H'` and
`T_i = T_{i-1} *_{y_i = z_i} B_i` for `i = 0..n`. Put `T = T_n`. Each step
amalgamates infinite cyclic groups, so it is well defined. Finite
presentation is the union of the vertex presentations plus one relator
`y_i = z_i` per step. By the normal form theorem for amalgamated free products
(Lyndon--Schupp, *Combinatorial Group Theory*, Ch. IV, Section 2; the same
theorem the route `fp-derived-subgroup-amalgam-proof` uses), the factors
embed, so `H' <= T`. Every `y_i` equals `z_i`, which lies in `[B_i,B_i]`, so
it lies in `[T,T]`. The `y_i` generate `H'`, hence `H <= H' <= [T,T]`.

**Word problem, by induction on `i`.** The induction hypothesis `(D_i)` has
two parts: `T_i` has solvable word problem, and membership of a word in
`<y_j>` (`j > i`) is decidable in `T_i`. `(D_{-1})` is the previous
paragraph.

Assume `(D_{i-1})`. A word in `T_i` is a product of syllables, alternately
from `T_{i-1}` and from `B_i`. Test each syllable for membership in the edge
group: `<y_i>` in `T_{i-1}` by `(D_{i-1})`, and `<z_i>` in `B_i` by the matrix
test. Both tests return the exponent. Replace a syllable that lies in the
edge group by the same power on the other side and merge it with its
neighbours. This strictly shortens the syllable count, so it terminates in a
reduced sequence. By the normal form theorem, a reduced sequence of length at
least 2 is nontrivial. So the word is trivial iff it reduces to one syllable
that is trivial in its factor. That is decidable.

For `j > i`, `y_j` lies in `H' <= T_{i-1}`. An element of `T_i` lies in
`T_{i-1}` iff its reduced form is a single `T_{i-1}`-syllable, or a single
`B_i`-syllable in `<z_i>`. In the second case we convert it. Then apply
`(D_{i-1})`. This gives `(D_i)`, and `(D_n)` is the claim. `∎`

The construction is uniform in a finite presentation of `H` together with a
word-problem algorithm for `H`. No choice of generator orders is needed,
unlike the route `fp-derived-subgroup-amalgam-proof`, which has to know
which generators have finite order.

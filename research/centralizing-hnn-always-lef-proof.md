---
rg: 2
id: centralizing-hnn-always-lef-proof
kind: route
title: Truncate the shift graph to one period and evaluate ball words in the periodic right-angled Artin group by a finite cyclic group
target: centralizing-hnn-over-conjugate-basis-is-always-lef
requires: []
---

Fix `r >= 1`; it suffices to embed the ball `B_r` of `H_J` (words of
length `<= r` in `a^{+-1}, b^{+-1}, s^{+-1}`) multiplicatively into a finite
group.

**Normal forms are local.**  As in
[[centralizing-hnn-always-sofic-proof]], `H_J = A(Gamma_J) x| <b>` with
`a_i = b^i a b^-i`, `s_k = b^k s b^-k`, and `Gamma_J` bipartite with edges
`a_i -- s_k` iff `i - k in J`.  A word `w` of length `<= 2r` rewrites as
`u b^t` with `|t| <= 2r` and `u` a word in the generators `a_i, s_k` with
`|i|, |k| <= 2r`.  The parabolic subgroup of `A(Gamma_J)` on the full
subgraph `W` spanned by these vertices is a retract, so `w = 1` in `H_J`
iff `t = 0` and `u = 1` in `A(W)`, which depends only on the edges of `W`,
i.e. on `J n [-4r, 4r]`.

**Periodic model.**  Put `J_r = J n [-4r, 4r]`, choose `M > 8r + 1`, and let
`Gamma'` be the bipartite graph on `Z/M u Z/M` with `a_i -- s_k` iff
`(i - k) mod M in J_r mod M`.  For `|i|, |k| <= 2r` the difference
`i - k` lies in `[-4r, 4r]`, and since `M > 8r + 1` it is congruent to an
element of `J_r` iff it is one, so the window of `Gamma'` on
`{|i|, |k| <= 2r}` is isomorphic to `W` (the vertex map is injective on
the window).  The shift `i |-> i + 1` is an automorphism of `Gamma'`, so
`H' = A(Gamma') x| Z/M` is defined; it is residually finite because
`A(Gamma')` is a finitely generated right-angled Artin group (linear over
`Z`) and `Z/M` is finite.

**Local embedding.**  Send `a |-> a_0`, `b |-> ` the generator of `Z/M`,
`s |-> s_0`, and evaluate words.  For words `w, w'` of length `<= r`
representing the same element of `H_J`, `w^{-1} w'` has length `<= 2r` and
is trivial in `H_J`, hence (locality plus the window isomorphism) its
rewritten form `u b^t` has `t = 0` and `u = 1` in `A(W) = A(window of
Gamma')`, hence in `H'`.  So evaluation is well defined on `B_r`; the same
argument backwards shows it is injective on `B_r`; and for `g, h, gh in
B_r` the concatenated word represents `gh` with length `<= 2r`, so
evaluation is multiplicative.  The image of `B_r` is a finite subset of the
residually finite group `H'`, which a finite quotient of `H'` separates,
giving the required finite model.

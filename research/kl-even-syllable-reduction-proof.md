---
rg: 2
id: kl-even-syllable-reduction-proof
kind: route
title: Amalgamate the one-relator quotient in z with a cyclic group along z = t^d, then substitute a shifted variable
target: kl-even-syllable-words-reduce-to-shorter-equations
requires:
  - kl-length-at-most-five-equations-are-solvable
---

**Lemma.** Put `H = (G * <z>)/<<v>>`, and let `k` be the order of `z` in `H`,
possibly infinite. Let `C = <t>` be cyclic of order `dk` (infinite cyclic if
`k` is infinite), and form the amalgamated product

```text
P = H *_(z = t^d) C.
```

Both factors inject into `P`, because `<z> <= H` and `<t^d> <= C` are both
cyclic of order `k`. In `P`, `w = v(t^d) = v(z) = 1`. So the homomorphism
`G * <t> -> P` that is the identity on `G` and sends `t` to `t` kills `w`, and
factors through `(G * <t>)/<<w>>`. The composite `G -> H -> P` is injective by
hypothesis, so `G -> (G * <t>)/<<w>>` is injective. The degree hypothesis is
not used in this step, only in the hypothesis on `v`.

**Shift normalization.** For `c in G`, the automorphism of `G * <t>` fixing `G`
with `t -> s c^(-1)` rewrites `w` as

```text
s (c^(-1) a_1) s (c^(-1) a_2) s (c^(-1) a_3) s (c^(-1) y c) s^(-1) (n c) s^(-1) x.
```

It maps `<<w>>` onto the normal closure of the rewritten word, so injectivity
is unchanged.

**Corollary.** Take `c = n^(-1)`. The N-label becomes `1`, and the P-labels
become `n a_i`.
- (E1): all three P-labels become `1`, and
  `w = s^4 y' s^(-2) x' = v(s^2)` with `v(z) = z^2 y' z^(-1) x'`.
- (E2): the P-labels become `1, g, 1` with `g = n a_2`, and
  `w = s^2 g s^2 y' s^(-2) x' = v(s^2)` with `v(z) = z g z y' z^(-1) x'`.

Here `y' = n y n^(-1)` and `x' = x`. In both cases `v` has variable length
three and `deg_z(v) = 1`. By `kl-length-at-most-five-equations-are-solvable`,
`G -> (G * <z>)/<<v>>` is injective. The lemma with `d = 2` gives the
corollary.

**Scope check.** The rewritten words may fail to be cyclically reduced when a
coefficient is `1`; the length-three theorem needs only nonsingularity, and
cyclic reduction only lowers the length, which stays covered.

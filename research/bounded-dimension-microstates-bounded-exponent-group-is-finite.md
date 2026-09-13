---
rg: 2
id: bounded-dimension-microstates-bounded-exponent-group-is-finite
kind: claim
title: A finitely generated group of finite exponent with bounded-dimension separated microstates is finite
distinct_from:
  bounded-dimension-microstates-force-lef: that concludes only LEF for an arbitrary countable group; this uses finite exponent and Schur's theorem to conclude finiteness, which LEF alone does not give.
  hyperlinear-fg-bounded-exponent-groups-are-finite: that is the open finiteness statement for all hyperlinear bounded-exponent groups; this is its bounded-dimension case, which forces every counterexample to have microstate dimension tending to infinity.
---

**ESTABLISHED.** Let `G` be a finitely generated group of finite exponent `N`.
Suppose there are `c > 0` and `D < infinity` such that for every finite
`F <= G` and every `eps > 0` there is a map `rho : F -> U(d)` with `d <= D`,

```text
||rho(x) rho(y) - rho(xy)||_2 < eps   whenever x, y, xy in F,     (BE1)
||rho(x) - rho(y)||_2 >= c            whenever x != y in F,       (BE2)
```

the norm being the normalized Hilbert--Schmidt norm on `M_d`. These are
conditions `(BDM1)`--`(BDM3)` of `bounded-dimension-microstates-force-lef`.
Then `G` embeds in `U(d)` for some `d <= D`, and `G` is finite.

## Consequence for the open finiteness claim

Every counterexample to `hyperlinear-fg-bounded-exponent-groups-are-finite`
is an infinite hyperlinear group of finite exponent. By this claim its
microstate dimensions are unbounded: for some finite window `F` and
separation constant `c`, the least dimension carrying `(BE1)`--`(BE2)` tends
to infinity as `eps -> 0`. Regular-character microstates satisfy `(BE2)`
with `c = 1` for small `eps`, as recorded in the LEF node.

This corrects a gap in Attempt 2 of the finiteness claim. It said
bounded-dimension approximations force LEF and therefore that a counterexample
needs growing dimension; LEF does not force finiteness, so that inference was
incomplete. The present argument goes through an exact linear representation
and Schur's theorem instead.

## Trust surface

- **Schur's theorem** (1911): a finitely generated periodic subgroup of
  `GL_n(C)` is finite. Cited, not reproved. Text pinned from the
  "Burnside problem" survey page (Wikipedia, fetched 2026-09-13): "Any finitely
  generated periodic group that was a subgroup of the group of invertible
  n × n complex matrices was finite." The same statement is used in
  `research/sp21-lattice-positive-characteristic-images-finite-proof.md` (S)
  and `research/operator-norm-restricted-burnside.md`.
- Everything else is elementary: norm equivalence in fixed dimension and
  compactness of `U(d)`.

No novelty is claimed; this is a standard compactness argument.

DERIVATION
bounded-dimension-bounded-exponent-finiteness-proof

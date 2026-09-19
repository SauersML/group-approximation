---
rg: 2
id: affine-memorizers-are-cross-direction-orthogonal
kind: claim
title: Odd-order pair memorizers in distinct directions have disjoint Fourier support, so all N-1 directions are independently addressable
invalidates:
  - glue-lemma-via-parseval-budget-across-directions
distinct_from:
  linear-pairing-memorizer-restricts-to-a-dictator: that is the single-direction construction and its exact restriction identity; this is the mod-4 orbit argument comparing two directions and the superposition it licenses.
  memorizer-superposition-has-large-sup-norm: that bounds the sup norm of superpositions from below and is proved by evaluating at linear points; this is an L^2 and Fourier-support statement and says nothing about sup norms.
artifacts:
  - research/artifacts/unique-games-affine-orientation-2026-08-24.md
---

**ESTABLISHED.**  Keep the notation of
`linear-pairing-memorizer-restricts-to-a-dictator`, with `r` odd.

**Disjoint supports.**  For distinct `b, c != 0` the Fourier supports of
`B_{b,r}` and `B_{c,r}` are disjoint.  A shared Fourier set, with the forced
coordinate `0` removed, would be a `2r`-element set `S` that is
simultaneously a union of `b`-pairs and of `c`-pairs, so `S + b = S` and
`S + c = S`.  Since `b, c` are distinct and nonzero over `F_2` they span a
four-element subgroup, `S` is a union of its orbits, and `4 | |S| = 2r`.
But `r` is odd, so `2r = 2 mod 4`.

**The same argument controls restriction, not just orthogonality.**  For
`c != b`, no monomial of `B_{c,r}` restricts on `D_b` to the singleton
quotient character at `C_b`.  Such a monomial `{0} union S` would have to
meet `C_b` oddly and every other `b`-coset evenly, forcing `S + b = S`
again, with `S` a union of `c`-pairs and `|S| = 2r`.  Same contradiction.

**Consequence.**  For an arbitrary sign pattern `s in {-1,1}^(Omega\{0})`
put `P_s = sum_{b != 0} s_b B_{b,r}`.  Then

```text
||P_s||_2^2 = (N-1)/M = Theta_r(N^(1-r)),
```

while for every `b` the Fourier coefficient of the singleton quotient
coordinate `C_b` in `P_s|_{D_b}` is **exactly** `s_b`.

So all `N - 1` linear pairing directions can be memorized independently and
simultaneously, with ambient `L^2` mass tending to zero for `r >= 3`.  No
Parseval or `L^2` budget spread over the direction set can therefore bound
the number of heavy directions, which is what
`glue-lemma-via-parseval-budget-across-directions` assumed.

This is the reason replacing random matchings by the presently hard `F_lin`
matchings is not a routine invariance-principle exercise.

What it does **not** do: `P_s` is not a bounded function, so this is not a
counterexample to `affine-orientation-glue-lemma`.  How far that gap can be
closed is settled negatively in `memorizer-superposition-has-large-sup-norm`.

The proof is `affine-memorizer-orthogonality-proof`.

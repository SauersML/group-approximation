---
rg: 2
id: houghton-far-transposition-commutation-is-superpolynomial
kind: claim
title: "In some H_n, commuting the top transposition past a transposition pushed k steps down ray 1 needs superpolynomial area"
distinct_from:
  houghton-transposition-commutation-area-is-polynomial: that asserts a polynomial bound for all centralizing words, which would refute this; this is the opposite assertion for one explicit family.
  houghton-carmichael-sections-have-unbounded-edge-area: that shows unbounded areas for Carmichael relators (u_i u_j)^2 over arbitrary conjugators; this asks for superpolynomial growth, as a function of k, for the explicit word [α, α^(g_1^(-k))].
---

For some `n >= 3`, with Lee's presentation (generators `g_i = λ_(1,i+1)`,
`α = ((1,1),(1,2))`, `x^h = h^(-1) x h`), the null-homotopic words

```text
w_k = [α, α^(g_1^(-k))]        (length 4k + 4)
```

satisfy: for every `d`, `Area(w_k) <= k^d` fails for infinitely many `k`. The
second factor `α^(g_1^(-k))` is the transposition `((1,k+1),(1,k+2))`, reached by
pushing ray `1` outward from ray `2`.

## Attempts

- 2026-09-13 (z1-24-houghton): no lower-bound mechanism found. Distortion is
  absent: finitary permutations are at most `P log P` distorted
  (Burillo–Cleary–Martino–Röver, arXiv:1403.0026, Theorem 4.1), and there is no
  `BS(1,m)` with `|m| >= 2`. Linear 1-cochain (weight) arguments cannot beat
  `O(k)` for a boundary of length `4k+4` unless the weights grow with position.
  Corridor arguments need a presentation in which some generator occurs in
  relators only in cancelling pairs. That would be an ascending HNN structure
  over `ker φ_1`, and whether it exists depends on `Σ^1(H_3)`. What is known on
  the other side: every transport, route-conversion and Morse-descent upper-bound
  scheme tried reduces to this family recursively, with branching factor `>= 2`
  (Tower-of-Hanoi recursion). See the Attempts on
  `houghton-transposition-commutation-area-is-polynomial`.
- 2026-09-17 (swarm-0917-w4-pull-z-5, reframing): ruled out for `n >= 6`. There
  `Area(w_k) ≼ k^2 log k`
  (`houghton-far-commutation-has-quadratic-log-area-for-six-rays`,
  `research/artifacts/zp-houghton-pours-2026-09-17.md` §3), and even
  `δ_(H_n) ≼ x^8 log x` (`houghton-groups-with-six-or-more-rays-have-polynomial-dehn`).
  The Hanoi recursion breaks once a pour `λ_ac^m λ_cb^m` may be rerouted through
  rays outside the relation: with two auxiliary rays, route changes split in half
  with only a quadratic overhead. So a superpolynomial family can only exist for
  `n ∈ {3,4,5}`. For those `n`, a lower bound would have to use the shortage of
  auxiliary rays. Any 2-cochain or corridor argument must fail when two more rays
  are added.
- 2026-09-18 (swarm-0917-w12-w12-z-break, reframing): `n = 5` is excluded by
  `houghton-five-rays-polynomial-dehn-via-path-words`. For `n = 3` the family is
  bounded by one explicit pour rewrite
  (`houghton-h3-far-commutation-bounded-by-two-ray-pour-rewrite`):
  `Area(w_k) <= 4A_3(k-2) + 2k^3 + 14k`, where `A_3(m)` is the `H_3`-area of
  `λ_ac^m λ_cb^m = λ_ab^m ρ_b(m)`. The same `A_3` bounds `H_4` through Remark 3.1 of
  `research/artifacts/zp-houghton-four-rays-via-h3-2026-09-18.md`. So a proof of this
  claim for `n = 3` must show that `A_3` is superpolynomial. The same holds for
  `n = 4`, since `A_3 ≼ m^D` gives `δ_(H_4) ≼ x^(6+D)`. The Hanoi recursion `R(k) <= 2R(k-1) + O(k)` is
  replaced by the non-recursive bound `R(j) <= 2A_3(j) + O(j^3)`.
  The converse, `A_3 ≼ poly(F_3)`, is not proved. It dies at renormalizing two-ray
  words after each `λ_ac`-conjugation in the `u_j` telescoping: that step needs a
  polynomial count of `S_∞` Coxeter moves, which is not bounded here. See the
  artifact `research/artifacts/zp-houghton-h3-far-commutation-via-pour-rewrite-2026-09-18.md`.

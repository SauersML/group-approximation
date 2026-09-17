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

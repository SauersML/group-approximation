---
rg: 2
id: houghton-transposition-commutation-area-is-polynomial
kind: claim
title: "In H_n (n >= 3), words centralizing the basic transposition commute with it with polynomial area"
distinct_from:
  houghton-dehn-polynomially-equivalent-to-commutation-area: that is the established reduction theorem relating the Dehn function to this area; this is the open assertion that the area is polynomial.
  houghton-groups-have-polynomial-dehn-function: that is the polynomial Dehn function statement; by the reduction theorem the two are equivalent, and this one isolates the single relation family that must be controlled.
---

For every `n >= 3` there is `k` such that for every word `z` of length `<= ℓ`
in Lee's generators with `z α z^(-1) = α` in `H_n`, `Area([z, α]) <= C ℓ^k`.
Here `α = ((1,1),(1,2))`.

## Attempts

- 2026-09-13 (z1-24-houghton), transport. Let `μ` be a shift that fixes
  `(1,1),(1,2)`. Then `[μ, α]` has bounded area, so `[α, D^(μ^m)]` costs `O(m)`
  for a deep transposition `D` written with the `μ`-routed word. But
  `μ = λ_(e,1)·ν`, with `ν` a 3-cycle on the top three points of ray `1`, so
  converting `λ`-routed words into `μ`-routed words needs far commutations of
  `ν^(λ^i)` with the deep transposition, at distances up to the original one. The
  naive recursion `F(k) <= Ck + 2 Σ_(d<k) F(d) + 2P(k)` is exponential, matching
  Lee's `e^x`.
- Route conversions behave like the Tower of Hanoi. Lee's relator
  `α^(ḡ_i) = α^(ḡ_j)` converts one push step between source rays. At depth `j`,
  the one-step conversion from source `b` to source `c` is `[λ_(b,c), D]` for the
  deep transposition `D`, and it costs `O(j)` only when `D` is routed from a third
  ray. The recursive scheme gives `C(k) <= 2 C(k-1) + O(k)`, which is exponential.
  With more rays a Frame–Stewart-type scheme is subexponential but still
  superpolynomial. Parking the tokens of `α` on another ray changes nothing: the
  parking pours are part of the conjugator, and after free reduction the relation
  is the original far commutation with the rays renamed.
- Pour identity. `λ_(e,1) λ_(1,f) = λ_(e,f)` holds exactly. Its iterate
  `λ_(e,1)^m λ_(1,f)^m = λ_(e,f)^m · K'_1 ⋯ K'_m` is derived with `O(m^2)`
  relator applications, where `K'_j` is a product of transpositions on ray `f`
  (moving `λ_(e,f)` past `λ_(e,1)` uses `[λ_(e,1), λ_(e,f)] = ((1,1),(f,1))`). The
  `K'_j` are written as conjugates of `((1,1),(f,1))` whose conjugators touch ray
  `1`. Converting them to words commuting letter by letter with `α` is again a far
  commutation at scale `m`.
- Morse descent. Use Lee's CAT(0) cube complex (vertices = injective eventual
  translations, height = deficiency, descending links = chessboard complexes
  `M_(n x r)`, ascending links = simplices) and the deterministic descent `d(f)`
  that inserts the `≺`-smallest held token at the top of ray `1`. Generic squares
  descend in parallel through a 3-cube, at cost `O(1)` per level, and a square
  meets at most two non-generic events. So `δ(L) <= L^2 (L + Patch(L))`. But the
  patch relations are commutations of skipping shifts `μ^((k))` (a shift that
  skips the top `k` points of ray `1`) with top-local moves, which is the same
  far-commutation family.
- Every route tried reduces to the far-commutation family
  `houghton-far-transposition-commutation-is-superpolynomial` (or its negation).
  Deciding that family is the sharpest target.

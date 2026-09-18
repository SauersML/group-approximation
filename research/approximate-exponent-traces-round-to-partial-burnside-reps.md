---
rg: 2
id: approximate-exponent-traces-round-to-partial-burnside-reps
kind: claim
title: Limit traces of approximate exponent-N unitary models are limits of traces of exact representations of every partial Burnside group
distinct_from:
  hyperlinear-fg-bounded-exponent-groups-are-finite: that is the finiteness statement; this is only its analytic half, an exact rounding statement with no finiteness conclusion, which by itself does not imply finiteness.
  bounded-degree-partial-burnside-reps-factor-through-burnside: that concerns exact representations of bounded degree; this asks for exact representations in unbounded degree that reproduce a given limit trace.
  hs-burnside-iff-lrb-and-partial-law-trace-rounding: that is the established decomposition in which this statement is the analytic prerequisite; this is the open prerequisite itself.
---

**OPEN.** For all `m, N >= 2` and `R >= 1`, `S(m,N,R)` of
`hs-burnside-iff-lrb-and-partial-law-trace-rounding` holds: every limit trace
`tau` of an approximate exponent-N model in `U(d_k)^m` is a pointwise limit of
normalized traces `tr rho_j(w)` of finite-dimensional unitary representations
`rho_j` of the partial Burnside group `Π_R(m,N)`.

**Status in the decomposition.**
- It is necessary for `hyperlinear-fg-bounded-exponent-groups-are-finite`
  (clause (b) of the decomposition).
- Together with `LRB(R_0, C)` at some radius `R_0 <= R`, it is sufficient
  (clause (c)).
- A failure of `LRB` does not refute it. The LEF witnesses give exactly
  roundable traces, as noted in the consequences of the decomposition.

## Attempts

1. **Radius one is elementary (swarm-0917, d-nhg-p4).** `Π_1(m,N)` is the free
   product of `m` copies of `Z/N`. Round each generator spectrally: send each
   eigenvalue `λ = e^{iθ}` of `u_i` to the nearest `N`-th root of unity
   `ζ = e^{iφ}` with the same eigenvector, giving `v_i` with `v_i^N = I`. For
   `|θ - φ| <= π/N`, `|λ^N - 1| = 2|sin(N(θ - φ)/2)| >= (2N/π)|θ - φ| >= (2N/π)|λ - ζ|`,
   so `||u_i - v_i||_2 <= (π/2N) ||u_i^N - I||_2 -> 0`. By bi-invariance, every
   fixed word satisfies `||w(u) - w(v)||_2 -> 0`, so the traces have the same
   limit. So `S(m,N,1)` holds, with `rho_j` close to the model in `||.||_2`.
2. **Where the difficulty starts.** By
   `partial-burnside-presentations-are-golod-shafarevich`, an `LRB` radius
   exceeds `(q - 5)/4` for every prime power `q` dividing `N`. So the useful
   instances of `S` must be exact on all words of at least that length, with `N`
   odd and `N >= n_1(F_m)` for the flagship route. Generator-by-generator
   spectral rounding keeps the law on longer words only approximately:
   `||(v_1 v_2)^N - I||_2 -> 0`, but in general `(v_1 v_2)^N != I`. Exactness
   on products needs a joint rounding that no longer stays operator-close; see
   Attempt 3.
3. **Calibration: the stability route is at least as strong as the root.**
   Strict Hilbert--Schmidt stability of the finitely presented group `Π_R(m,N)`
   would give `S(m,N,R)` with operator-level closeness. By clause (d) of the
   decomposition, at a radius `R >= R_0` where `LRB(R_0, C)` holds and with
   `B(m,N)` infinite, strict or flexible stability of `Π_R(m,N)` makes
   `Π_R(m,N)` a finitely presented non-hyperlinear group. So any proof of `S` at
   an `LRB` radius must be trace-level, not operator-level, or it resolves
   `non-hyperlinear-group` directly. Rounding that changes the operators, such
   as passing to direct sums or tensor amplifications that reproduce only the
   trace, is not excluded by this obstruction.
4. **What remains open.** No trace-level rounding scheme at radius `R >= 2` is
   known. The natural candidate is "replace the model by a genuine
   representation of a finite group satisfying the law on the ball". That is
   circular at an `LRB` radius: by clause (c) its images are bounded, so it
   already asserts trace rigidity.

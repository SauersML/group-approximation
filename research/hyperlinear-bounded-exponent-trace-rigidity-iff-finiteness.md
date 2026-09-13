---
rg: 2
id: hyperlinear-bounded-exponent-trace-rigidity-iff-finiteness
kind: claim
title: Limit traces of approximate exponent-N unitary models all come from finite groups iff hyperlinear groups of exponent N are finite
distinct_from:
  hyperlinear-fg-bounded-exponent-groups-are-finite: that is the open finiteness statement itself; this is the established equivalence identifying it with a statement about limit traces of approximate exponent-N models.
  bounded-dimension-microstates-force-lef: that caps the dimension and concludes LEF; here dimensions are unbounded and the conclusion concerns limit traces.
  matrix-restricted-burnside-gap: that is the operator-norm, dimension-free power-law inequality of the corona program; this is the normalized Hilbert--Schmidt analogue at the level of limit traces, and it uses no restricted Burnside input.
---

**ESTABLISHED.** Fix integers `m, N >= 1`. Call a sequence of unitary tuples
`u^(k) = (u_1^(k), ..., u_m^(k)) in U(d_k)^m` an **approximate exponent-N
model** if

```text
|| w(u^(k))^N - I ||_2 -> 0      for every word w in F_m,
```

and the normalized traces `tr w(u^(k))` converge for every `w`, with limit
`tau(w)`. Here `tr` and `||.||_2` are normalized by `d_k`. The following are
equivalent.

1. Every `m`-generated hyperlinear group of exponent dividing `N` is finite.
2. For every approximate exponent-N model, the limit trace `tau` factors
   through a finite quotient of `F_m`: there are a finite group `Q`, a
   homomorphism `p: F_m -> Q` and a function `s` on `Q` with `tau = s o p`.

**Consequences.**

- Approach A5 of `research/artifacts/ideas-2026-09-13/nh/nh-small-cancellation.md`
  (Hilbert--Schmidt stability of exponent laws, toward non-hyperlinearity of
  free Burnside groups) uses exactly the trace-level conclusion 2. So that
  route is statement 1 and nothing weaker. Its second kill test, "build
  approximate models whose limit trace is not a finite-group character", is
  the same problem as building an infinite `m`-generated hyperlinear group
  of exponent dividing `N`.
- If statement 1 holds for some `(m,N)` with `B(m,N)` infinite, then
  `B(m,N)` is non-hyperlinear.

Neither direction uses a restricted Burnside theorem, a Schur theorem,
stability or property `(T)`.

DERIVATION
hyperlinear-bounded-exponent-trace-rigidity-iff-finiteness-proof

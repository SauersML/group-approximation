---
rg: 2
id: self-dual-sector-frustrated-flux-shift-proof
kind: route
title: Self-duality commutes with the sheet involution, sheet differences form a cocycle with holonomy given by the extension, and a detecting character supplies an invariant base point
target: clifford-cover-self-dual-sectors-are-frustrated-flux-shifts
requires: []
artifacts:
  - research/artifacts/clifford-copying-rule-lift-2026-09-12.md
  - research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md
---

Complete direct proof, artifact Section 2.
- **Sector.** `tau(Jx) = J tau(x)` with `J(x)(e) = x(eps e) + 1`, by self-duality; injectivity then gives
  `image cap Fix(J) = tau(Fix(J))`.
- **Gauge coordinates.** `Theta_x(w, m) = x(e) + x(e m)` is independent of the lift, satisfies the cocycle identity and
  `Theta(w, eps) = 1`; `x(e) = Theta(1, e)` inverts it up to the flip. On generators, holonomy along a word `r` with
  `rbar = 1` is `Theta(w, r) = omega(r)`.
- **Induced automaton.** `mu(a) = a_0 + mu(a + a_0 1)` gives `tau(x)(e) = x(e) + mu((Theta_x(w, m_i))_i)`.
- **Characters.** `theta(eps) = 1` gives an element of the sector with invariant gauge field; writing `x = theta + y`
  conjugates `tau` to a `W`-automaton over the full shift, bijective when injective over a surjunctive group. The
  memory-group version works coset by coset; surjunctivity passes to subgroups (standard induction).
- **Clifford flux.** `[c_x, c_y] = eps^(b_S(x,y))`, `c_o^2 = eps^q`, and `omega` is additive on products of conjugates
  of relators since `eps` is central. Characters kill commutators.

**Verification (w3-vf-nonlinear, 2026-09-12): PASS.** Re-derived independently.
- `J` commutes with `tau`.
- `Theta` does not depend on the lift, and its inverse `x(e) = Theta(1,e)` lies in `Tw`.
- Holonomy is `omega(r)` because `r = eps^(omega(r))`.
- `mu(a) = a_0 + mu(a + a_0 1)`.
- Flat differences are coboundaries.
- A character gives `tau(theta + y) = theta +` a `W`-automaton. The cosets of `<M>` are `eps`-stable.
- Plaquette flux is `b_S`, and `eps` is a commutator.

Scope note: the Payoff design filter needs `<M>/<eps>` surjunctive
(`research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md`, Section 22).

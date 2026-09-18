---
rg: 2
id: hot-surjunctivity-tools-hold-on-irs-schreier-networks
kind: claim
title: Mass transport, Bernoulli preservation, random-order transport and the Rokhlin deficit all hold for shape-dependent designs on IRS Schreier networks
distinct_from:
  injective-ca-random-order-transport-identity: that is the transport identity over a group; this proves the same identity for shape-dependent designs on the Schreier graphs of any invariant random subgroup of a free group, via mass transport for IRS.
  bijective-ca-preserve-uniform-bernoulli-measure: that is invariance over a group; this is the per-graph version for arbitrary vertex tables, used as one of four audited tools.
  strict-automaton-lowers-bernoulli-rokhlin-entropy: that lowers absolute Rokhlin entropy over a group, paying for markers by amplification; this lowers Rokhlin entropy relative to the base of an IRS realization, where markers are free and no amplification is needed.
artifacts:
  - research/artifacts/design-subgroup-tests-2026-09-17.md
---

**ESTABLISHED** by `hot-surjunctivity-tools-hold-on-irs-schreier-networks-proof`.

**Setting.**
- `mu` is an IRS of `F_r`.
- `D = (tau, sigma)` is a design of shape-dependent automata with `eps_D(mu) = 0`, with radius
  `rho = R_tau + R_sigma`.
- `q = |A|`, and `b_k` is the size of the radius-`k` ball of the `2r`-regular tree.

**Theorem.**
1. *Mass transport.* For isomorphism-invariant Borel `f >= 0` on doubly rooted Schreier graphs,
   `E_mu sum_v f(X_H, o, v) = E_mu sum_u f(X_H, u, o)`.
2. *Bernoulli preservation.* On every countable bounded-degree graph, a finite-radius pair with arbitrary vertex
   tables and `sigma tau = tau sigma = id` preserves the uniform product measure.
3. *Transport identity.* With `x` uniform, `y = tau x` and i.i.d. labels `U` defining a random order,
   `E_mu sum_u I( x(u) ; y(o) | y(B_{R_sigma}(u) cap past(o)), U, X_H ) = log q`. Domination of this sum by
   `E H(y(o) | X_H)` is equivalent to `E H(y(o) | X_H) >= log q`.
4. *Rokhlin deficit.* If `D` is strict for `mu`, the Bernoulli extension of the realization of `mu` (Lemma 1.1 of
   the artifact) has
   `h^Rok(Bernoulli extension | base) <= log q - (delta_D(mu) / b_(2 rho)) q^(-b_rho) < log q`.

**Consequence** (answers bus need 9f00a635).
- These tools hold verbatim on IRS Schreier networks.
- So an argument for `gottschalk-surjunctivity-conjecture` built from them alone, with no input that fails on
  IRS, also proves `free-group-irs-carry-no-strict-design`.
- A single witness for `some-free-group-irs-carries-a-strict-design`, which must be non-co-sofic, defeats every
  such argument.
- The IRS form of the Rokhlin target is relative maximality of Bernoulli extensions over every p.m.p. base. By
  item 4 it implies P1.

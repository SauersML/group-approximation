---
rg: 2
id: galois-unique-game-value-is-transversal-expansion
kind: claim
title: A unique game whose lift is a Cayley graph has value = best transversal non-expansion, is perfect iff the walk acts freely, and has SDP = K-orthogonal positive-definite functions
distinct_from:
  perfect-commuting-unique-game-is-classically-satisfiable: that is operator rigidity at value one for arbitrary unique games; this computes the value, the perfect case and the basic SDP for the symmetric regular-cover (Galois) games only.
  sd-rich-and-unique-games-sos-gaps-interconvert: that converts gap instances between UG and admissible 2-to-1 games; this is an exact group-theoretic description of one class of symmetric UG instances.
artifacts:
  - research/artifacts/ugc-galois-games-2026-09-12.md
---

**ESTABLISHED.** Let `G` be a finite group, `K <= G` of order `k`, and `mu` a
symmetric probability measure on `G`. The **Galois game** `Gal(G,K,mu)` has
vertices `G/K` (left cosets), alphabet `K`, edges `(v, s v)` with `v` uniform
and `s ~ mu`, and translation constraints `f(s v) = tau(s v)^-1 s tau(v) f(v)`
for a fixed section `tau`. Its label-extended graph is the left Cayley graph
of `(G,mu)`, with fibres the cosets of `K`. Khot--Vishnoi's integrality-gap
instance is `Gal(F_2^N, Hadamard code, epsilon-noise)`.

1. **Value.** `val = max_T Pr_(t in T, s~mu)[s t in T]`, over left transversals
   `T` of `K`.
2. **Perfect completeness.** `val = 1` iff `<supp mu>` acts freely on `G/K`,
   that is, `<supp mu> cap g K g^-1 = {e}` for every `g`. In the connected case
   this says `<supp mu>` is a complement of `K`.
3. **Symmetric SDP.** If `mu` is conjugation-invariant, the basic SDP value is
   `max sum_g mu(g) phi(g)` over real positive-definite `phi` with
   `phi(e) = 1` and `phi = 0` on `K \ {e}`.

So a symmetric gap construction of quotient type has two ingredients. The
SDP side needs a vector with orthonormal `K`-translates that is almost invariant
under `mu`. The integral side needs every transversal of `K` to expand. That is
small-set expansion of the total space at density `1/k`, restricted to
transversals.

This does not bear on the truth of `unique-games-conjecture`. It is the
language in which `elementary-abelian-galois-games-round-with-linear-loss` is
stated.

DERIVATION galois-unique-game-value-is-transversal-expansion-proof

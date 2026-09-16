---
rg: 2
id: profinite-diagonal-cantor-type-is-transfer-limit
kind: claim
title: The type semigroup of a profinite diagonal extension is the transfer limit over the chain, and it is almost unperforated once the closures of the chain stabilize
distinct_from:
  induced-cantor-action-type-semigroup-matches-subgroup: that is one finite-index induction; this assembles a whole chain of inductions into a free action, identifies the connecting maps as transfers, and gives the stabilization firewall.
  product-with-divisible-cantor-action-kills-finite-type: that multiplies by a second group acting on another space; this extends by the same group acting on its own profinite completion.
---

**Setting.**  Let `Gamma` be a countably infinite group acting on a Cantor
space `X`.  Let `Gamma = N_0 ⊇ N_1 ⊇ ...` be normal subgroups of finite index
with trivial intersection, `K = lim Gamma/N_j`, and let `Gamma` act on
`Y = X x K` by `gamma (x, k) = (gamma x, gamma k)`.  Write `[s]` for the
clopen coset of `K` over `s in Gamma/N_j`.

**Theorem.**

1. `Y` is a Cantor space and the action is free.
2. The action on `Y` is minimal iff every `N_j` acts minimally on `X`.
3. `Y` has an invariant Borel probability measure iff `X` has one.
4. `S(Y, Gamma)` is the direct limit of `S(X, N_j)` along the transfers
   `rho_j [A] = sum_(t in N_j/N_(j+1)) [t^(-1) A]`, with `[A]` at stage `j`
   going to `[A x [N_j]]`.  At stage `j` the class `[1_Y]` is
   `[Gamma : N_j] [1_X]`.
5. For a commutative monoid `M`, the `Gamma`-invariant finitely additive maps
   `nu : Clopen(Y) -> M` (additive on disjoint unions, `nu(∅) = 0`) correspond
   bijectively to chains of `N_j`-invariant finitely additive
   `mu_j : Clopen(X) -> M` with
   `mu_j = sum_(t in N_j/N_(j+1)) t_* mu_(j+1)`, via
   `nu(A x [g N_j]) = mu_j(g^(-1) A)`.  Here `(t_* mu)(A) = mu(t^(-1) A)`.
6. **Firewall.**  Give `Homeo(X)` its compact-open topology.  If the closures
   of the `N_j` in `Homeo(X)` are eventually constant, `S(Y, Gamma)` is almost
   unperforated.  So a non-almost-unperforated extension needs the closure of
   `Gamma` to have infinitely many strictly shrinking open normal subgroups of
   finite index.

**Relation to earlier attempts.**
* Freeness, the direct limit over `S(X, N_j)` and the class
  `[Gamma : N_j][1_X]` of `1_Y` were already recorded as an unreviewed idea
  ("Freeing by profinite extensions") on
  `free-minimal-cantor-action-with-finite-clopen-type`.  New here: the
  transfer formula for the connecting maps, item 5 and item 6.
* The "Profinite diagonal products" attempt on
  `rainone-free-minimal-f2-action-not-almost-unperforated` assumes every
  `N_j` is `mu`-exhaustive inside `Aut(B, mu)` (Wehrung, Definition 4.7.12, as
  recorded on `wehrung-countable-refinement-monoids-group-measurable`).  Then
  `S(X, N_j) ≅ M` via `mu`, every `t` preserves `mu`, and the transfer of
  item 4 is multiplication by the index.  Item 6 is a separate firewall that
  needs no refinement-monoid structure: it applies to any action whose chain
  has eventually constant closures.

Status: proved in `profinite-diagonal-transfer-limit-proof`; refereed
2026-09-16 (swarm referee), no gaps found.

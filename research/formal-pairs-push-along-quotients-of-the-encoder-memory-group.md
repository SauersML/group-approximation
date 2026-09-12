---
rg: 2
id: formal-pairs-push-along-quotients-of-the-encoder-memory-group
kind: claim
title: A formal pair whose encoder memory lies in a subgroup pushes forward to every quotient of that subgroup
distinct_from:
  formalizable-pairs-restrict-to-finite-quotients: that substitutes coset variables for a finite-index normal subgroup of the whole host; this first collapses the formal identity onto any subgroup containing the encoder representative's memory, then pushes along any surjection of that subgroup, so it also reaches infinite-index subgroups and infinite quotients.
  formalizable-binary-pairs-over-biorderable-groups-are-affine: that classifies formal one-track pairs over a bi-orderable host; this transports formal pairs from any host to bi-orderable quotients of the encoder memory group, where that classification then applies.
artifacts:
  - research/artifacts/stable-formalizability-on-simple-hosts-2026-09-12.md
---

Let `k = F_q`, and let `tau` on `(k^n)^G` have local rule `mu` on memory `M`. Suppose representatives
`tau~` (memory `M~ ⊇ M`) and `sigma~` form a formal left-inverse pair. Suppose `M~ ⊂ H <= G`, and
`rho : H -> Q` is surjective. Then the `Q`-automaton `tau_rho(y)(q) = mu((y(q rho(m)))_(m in M))` has
a formal left inverse, with encoder representative obtained by substituting `X_(m,i) -> X_(rho(m),i)`
into `tau~`. `tau_rho` depends only on `mu`, `H` and `rho`. The same holds for stable formalizations,
carrying the ancilla tracks along.

**Consequences.**
- **Normal subgroups.** With `H = G` it covers every normal subgroup `K`, not only finite-index ones.
- **Formalizability passes up to overgroups,** with the same polynomials, so refutations pass only down,
  through this theorem.
- **Bi-orderable obstruction.** By `formalizable-binary-pairs-over-biorderable-groups-are-affine`, a
  formalizing encoder representative of a non-affine one-track `tau` has memory generating a subgroup
  `H` on which every surjection onto a bi-orderable group pushes `tau` to an affine automaton.
- **Induced marker involution.** For the marker involution along an infinite-order `g`, every
  bi-orderable quotient of `H` must kill `g`. In particular `g` has finite order in `H^ab`, and the
  encoder memory must leave every subgroup that maps onto `Z` nontrivially on `g`, such as `<g> x F`.
- **Scope.** When the encoder memory generates a finitely generated simple host, no bi-orderable
  quotient exists (`finitely-generated-simple-groups-are-not-biorderable`), so this obstruction is void
  there.

Proof: artifact Section 1, route `formal-pairs-push-along-encoder-memory-quotients-proof`.

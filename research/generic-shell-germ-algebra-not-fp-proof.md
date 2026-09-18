---
rg: 2
id: generic-shell-germ-algebra-not-fp-proof
kind: route
title: Retract the odd-distance graph product with bounded distances onto a free product of two far vertex groups
target: generic-shell-germ-algebras-are-not-finitely-presented
requires:
  - generic-shells-have-infinitely-generated-singular-ideals
  - shell-germ-algebra-fp-forces-fp-germ-group
---

**Proof.** Items 2 and 3 follow from item 1: item 2 by part 2 of
`generic-shells-have-infinitely-generated-singular-ideals` (`Q_nu ≅ Q_gen` for generic `nu`),
and item 3 by `shell-germ-algebra-fp-forces-fp-germ-group`.

**Item 1.** Let `X = S ∪ {τ}` and let `R` be the defining relators of `Q_gen`:
- the relators of `P` on `S`;
- the commutators `[a, τ^D b τ^(-D)]` for `a, b ∈ P` and `D` odd.

Suppose `Q_gen` were finitely presented. Since `X` is finite, some finite `R_0 ⊆ R` already
presents it. This is standard:
- by Tietze moves, the kernel `N` of `F(X) -> Q_gen` is the normal closure of finitely many
  elements `n_1, ..., n_k`;
- each `n_j` is a finite product of conjugates of elements of `R`;
- let `R_0` be the finitely many elements used. Then `N = <<R_0>>`.

Let `L` be the largest `|D|` among the commutators in `R_0`.

Put `G_L = <X | relators of P, [a, τ^D b τ^(-D)] for odd |D| <= L>`. It is a quotient of
`<X | R_0>`. So, if `R_0` presented `Q_gen`, every relation of `Q_gen` would hold in `G_L`. We
show that `[a, τ^D b τ^(-D)] ≠ 1` in `G_L` for `a, b ∈ P ∖ {1}` and odd `D > L`.

- **Graph product model.** Let `Γ_L` be the graph product of copies `P^(k)`, `k ∈ Z`, over the
  graph with an edge `{i, j}` exactly when `|i - j|` is odd and at most `L`. The index shift is
  an automorphism of this graph, so `τ` acts on `Γ_L` by `P^(k) -> P^(k+1)`. Let
  `H_L = Γ_L ⋊ <τ>`.
- **A map.** `P -> P^(0)` and `τ -> τ` define `G_L -> H_L`. The relators of `P` hold in
  `P^(0)`. The commutator `[a, τ^D b τ^(-D)]` maps to `[a^(0), b^(D)]`, which is trivial because
  `{0, D}` is an edge for odd `|D| <= L`.
- **A retraction.** For odd `D > L`, the vertices `0` and `D` are not adjacent. Killing every
  `P^(k)` with `k ∉ {0, D}` defines `Γ_L -> P^(0) * P^(D)`. Every defining commutation of
  `Γ_L` involves an adjacent pair, hence at least one killed factor, so the map is well
  defined.
- **Nontriviality.** The image of `[a, τ^D b τ^(-D)]` is `[a^(0), b^(D)]` in the free product
  `P^(0) * P^(D)`. This is nontrivial for `a, b ≠ 1`.

`P` is infinite, so such `a, b` exist. So `[a, τ^D b τ^(-D)]` is trivial in `Q_gen` but not in
`G_L`, a contradiction. `∎`

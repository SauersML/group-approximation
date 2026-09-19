---
rg: 2
id: free-compatible-wreath-actions-are-bernoulli-absorptions
kind: claim
title: A full shift absorbs a nontrivial subshift exactly when the compact group H^G acts on it freely, compatibly with the shift, and not transitively; the absorbed subshift is then a strongly irreducible Cantor SFT carrying a product-splitting measure
distinct_from:
  monomial-quantum-automata-are-topological-bernoulli-absorptions: that characterizes absorptions by a non-injective decoder sigma together with a commuting translation lift (T_e) satisfying sigma T_e = sigma + delta_e; this drops the decoder and commutativity altogether, showing that any free, shift-compatible, non-transitive continuous action of H^G (H any group of order |A|) already produces the decoder and the trivialization, and it adds the extension criterion and the shape of Y.
  absorptions-give-post-surjective-strict-pairs: that derives decoder properties and fixed-point rigidity Fix_N(Y) = {y_0}; this derives measure splitting, perfectness, uniqueness of the finite orbit, the SFT and strong irreducibility of Y, and recasts the strict automaton of an absorption as an orbit map.
  no-group-carries-a-topological-bernoulli-absorption: that is the conjecture that no absorption exists; this proves only equivalences and necessary structure, and shows that conjecture is the statement that every free compatible H^G-action on a full shift is transitive.
  strict-automata-yield-topological-bernoulli-absorptions: that is the open transfer from strict automata to absorptions; this reduces it to extending, freely, the action that a strict automaton transports onto its image.
---

**ESTABLISHED** by [[free-compatible-wreath-actions-are-bernoulli-absorptions-proof]]. Elementary topological
dynamics; the novelty is the reformulation.

**Setting.** `G` is an infinite group, `A` a finite alphabet with `|A| = n >= 2`, and `H` any group of order `n`.
The shift is `(lambda_g u)_h = u_{g^-1 h}` on `A^G`, and `G` acts on the compact group `H^G` by the same formula,
`(g.k)_h = k_{g^-1 h}`. A *compatible action* is a continuous action `(k, u) -> k * u` of the compact group `H^G` on
`A^G` with `lambda_g (k * u) = (g.k) * (lambda_g u)`. Equivalently, it is a continuous action of the unrestricted
wreath product `H^G ⋊ G` extending the shift. A *topological Bernoulli absorption* is as in the monomial theorem: a
subshift `Y` with `|Y| >= 2` and a shift-equivariant homeomorphism `Psi : A^G -> A^G x Y`. Fix a bijection
`beta : A -> H`, and let `H^G` act on `A^G` by *translation*, `(k . u)_g = beta^-1(k_g beta(u_g))`.

**Theorem A (wreath form).** The following are equivalent.

1. `A^G` admits a topological Bernoulli absorption.
2. For some group `H` of order `n`, some compatible action of `H^G` on `A^G` is free and not transitive.
3. For every group `H` of order `n`, some compatible action of `H^G` on `A^G` is free and not transitive.
4. Some injective, non-surjective cellular automaton `tau : A^G -> A^G` is an *orbit map*: `tau(u) = k_u * c`,
   where `k_u = beta(u)`, for a constant configuration `c` and a free compatible action `*`.

Moreover:

- **(a) The decoder is automatic.** Every free compatible action has a cellular automaton `sigma : A^G -> H^G` with
  `sigma(k * u) = k sigma(u)` (coordinatewise product). Then `Psi(u) = (sigma(u), sigma(u)^-1 * u)` is a
  shift-equivariant homeomorphism `A^G -> H^G x Y` with `Y = sigma^-1(1)`, and `Y` meets each orbit exactly once.
- **(b) Orbit maps are injective automata.** For every constant `c`, `k -> k * c` is an injective cellular automaton
  `H^G -> A^G`. The action is transitive iff this map is onto. So on a group that is surjunctive at size `n`, every
  free compatible action is transitive. This is `Gottschalk => no absorption` in one line.

**Theorem B (extension criterion).** `A^G` admits an absorption iff some injective non-surjective `tau` on `A^G`
has this property: the action `k * tau(u) = tau(k . u)` that `tau` transports onto its image `X = tau(A^G)`
extends to a free compatible action of `H^G` on all of `A^G`. The image `X` is then a single orbit.

**Theorem C (shape of the absorbed factor).** Let `Psi = (sigma, zeta)` be any absorption over the infinite group
`G`, let `mu` be the uniform Bernoulli measure, and let `nu = zeta_* mu`.

- **(i) Measure splitting.** `Psi_* mu = mu x nu`. `nu` has full support on `Y` and no atoms.
- **(ii) Perfect, one finite orbit.** `Y` has no isolated point, so it is a Cantor set. Its unique shift-fixed
  point `y_0` is its only point with a finite `G`-orbit.
- **(iii) SFT and strong irreducibility.** `Y` is conjugate to the subshift of finite type `sigma^-1(c)`, for any
  constant `c`. It is also a shift-equivariant retract of `A^G`, via `zeta` and `y -> Psi^-1(c, y)`. Being a
  factor of a full shift, it is strongly irreducible.

**Consequences for the hub `strict-automata-yield-topological-bernoulli-absorptions`.**

- **The recorded death point is not an obstruction.** The w6 attempt died at "an equivariant, continuous
  trivialization of the fibre bundle `sigma`" of the decoder of the given strict pair. By (a), trivialization is
  automatic once a free compatible action exists. The absorption's decoder is manufactured from the action, and it
  need not be the decoder of the strict pair one starts from. Commutation relations `T_e T_g = T_g T_e` are also
  not needed, since `H` may be nonabelian.
- **What the hub really asks.** By Theorem B, the hub is equivalent to the following. For every non-surjunctive
  group, at some alphabet size, some strict automaton's transported image action extends to a free compatible
  action of `H^G` on the whole full shift. The content is freeness off the image.
- **Class kill.** Every construction whose absorbed factor `Y` is finite, countable, or has an isolated point dies
  at (ii). So does every construction whose `Y` has a second finite orbit, for example one that absorbs a periodic
  orbit or a finite `G`-set. Every construction with a non-strongly-irreducible `Y` dies at (iii), for example one
  whose `Y` is a union of two disjoint nonempty closed invariant pieces. Every construction whose `nu` is atomic,
  or not product-splitting, dies at (i).

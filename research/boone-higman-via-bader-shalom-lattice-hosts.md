---
rg: 2
id: boone-higman-via-bader-shalom-lattice-hosts
kind: route
title: Put the decidable simple envelope in a Bader-Shalom lattice, read off just-infiniteness, and extract a finitely presented simple factor from the finite residual
target: boone-higman-conjecture
requires: [boone-higman-thompson-simple-envelope, decidable-simple-groups-embed-in-bader-shalom-lattices, simple-in-bader-shalom-lattice-forces-compact-presentation, product-lattice-fp-iff-factors-compactly-presented, bader-shalom-normal-subgroup-theorem, just-infinite-over-simple-subgroup-gives-fp-simple-host]
---

**Three unstated assumptions shared by the existing Boone–Higman routes, and their
denials.**

- **A1. Finite presentation must be engineered.** Existing routes get it from a
  finiteness criterion on the host (Brown's criterion, fibre products, the
  1-2-3 theorem), or by finitely normally generating a kernel.
  - *Denial:* finite presentation is inherited for free by finite-index subgroups
    and retracts. So get the simple group as a direct factor of a finite-index
    subgroup of a host that is finitely presented for geometric reasons, and let
    the host have finite quotients.
- **A2. Simplicity is proved element by element inside a group with no finite
  quotients.** Existing routes use commutator tricks, Epstein/Higman-type
  arguments, or independence properties.
  - *Denial:* use a global normal-subgroup dichotomy (just-infiniteness) and let
    the input do the rest. An infinite simple subgroup kills residual finiteness,
    and `just-infinite-over-simple-subgroup-gives-fp-simple-host` turns
    "just-infinite plus one simple subgroup" into "virtually `T^k` with `S ↪ T`".
- **A3. The host is a discrete transformation group assembled from the input's
  combinatorics** (Thompson-like groups, germ groups, groups acting on trees).
  - *Denial:* the host is a uniform lattice in a product of two locally compact
    groups. Just-infiniteness comes from ergodic theory (the Bader–Shalom
    amenability and property (T) halves), not from combinatorics.

By `boone-higman-iff-fp-just-infinite-hosts`, the three denials together lose no
strength: Boone–Higman is equivalent to finding finitely presented just-infinite
hosts.

**The route.** Let `G` be finitely generated with solvable word problem.

1. By `boone-higman-thompson-simple-envelope` (with the infinite, decidable
   refinement recorded there), `G ≤ S` with `S` an infinite finitely generated
   simple group with solvable word problem.
2. **P1** (`decidable-simple-groups-embed-in-bader-shalom-lattices`, OPEN):
   `S ≤ Γ`, where `Γ < G_1 × G_2` is a cocompact lattice with dense projections.
   Each `G_i` is non-discrete, compactly generated and just-non-compact, with no
   nontrivial abelian normal subgroup.
3. By `bader-shalom-normal-subgroup-theorem`, `Γ` is just-infinite.
4. **P2** (`simple-in-bader-shalom-lattice-forces-compact-presentation`, OPEN):
   both `G_i` are compactly presented.
5. By `product-lattice-fp-iff-factors-compactly-presented`, `Γ` is finitely
   presented.
6. By `just-infinite-over-simple-subgroup-gives-fp-simple-host`, `S` embeds in a
   finitely presented infinite simple group `T`. Hence `G ≤ T`.

**Independence of the open prerequisites.**

- P1 is an existence and universality statement. It says nothing about presentations.
- P2 is a rigidity statement about any such lattice once it exists.
- P1 can fail: no non-linear, non-Haagerup, non-CAT(0) factor pair has a lattice
  with a simple subgroup.
- P2 can fail: such a lattice exists with a non-compactly-presented factor.

If P2 fails, the route is repaired by strengthening P1 to compactly presented
factors, and then steps 4–5 read "P1c, then `product-lattice-...`".

**Where whole classes of instantiations die** (details in
`decidable-simple-groups-embed-in-bader-shalom-lattices`, Attempt 1):

- **linear factors**, on either side, by residual finiteness via the injective
  projection;
- **two Haagerup factors**, by the simple Kazhdan probe
  `fg-groups-have-simple-kazhdan-hosts-of-same-wp-degree` being forced into a
  compact subset of the product;
- **products of properly cocompact CAT(0) factors**, by
  `complexity-bounded-host-classes-are-not-universal`, conditional on the unpinned
  BORS Dehn-function bound.

Every non-linear uniform example this lane found in Caprace's survey acts on a
product of trees or buildings, and so lies in the last two classes. Caprace
(arXiv:1709.05949, p. 36) knows no example with more than two non-linear factors.
The route is therefore a precise request for a new kind of lattice, not a
repackaging of Burger–Mozes.

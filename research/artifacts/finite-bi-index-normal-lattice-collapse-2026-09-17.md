# Finite bi-index collapses the normal lattice (swarm-0917, w4)

Lane: `ck-envelope-simple-core-has-finite-bi-index`, role inverter, family
reframing. Agent `swarm-0917-w4-bh-ck-bi-index`.

## The biography that became a theorem

The task was to write the biography of a counterexample-free envelope:
fp `Gamma`, `Gamma = <<s>>`, `s in S` simple, and `r = |S\Gamma/S| < infinity`.
Its forced properties:

1. Every proper normal `N` meets each double coset in at most one
   `S`-conjugacy class (`n' = a n b` in `N` forces `ab in N ∩ S = 1`).
2. So `N` is a union of at most `r` core classes, and is normally generated
   by at most `r-1` elements.
3. `Gamma` has Max-n, every proper quotient is fp, keeps (T), keeps the
   normal generator, and keeps bi-index `<= r`.
4. `Gamma/M` is an fp simple Kazhdan group containing the input.

Nodes: `bi-index-core-makes-normals-core-class-unions`
(lemma), `ck-finite-bi-index-hole-is-kazhdan-boone-higman` (consequences),
`kazhdan-boone-higman-conjecture` (the true strength of the hole).

## Belief changed

The graph recorded, in the hole's `distinct_from` and in
`simple-core-bi-index-counts-coset-action-pair-orbits`, that finite bi-index
and a finitely normally generated maximal kernel are independent
conditions. They are not: finite bi-index implies finite normal generation
of every proper normal subgroup of the same envelope. The Attempt 1
remark on `ck-envelope-has-a-finitely-normally-generated-maximal-kernel`
("A Max-n condition on the normal lattice would rescue it") is exactly
what finite bi-index supplies.

The twisted Brin--Thompson step of
`boone-higman-via-finite-bi-index-envelope` is idle. The envelope's maximal
quotient is already the finitely presented simple host.

## Classes killed (the step where each dies is clause 2 of the lemma)

- Envelopes with an infinite central subgroup. Example: a marked
  Steinberg cover whose covering kernel is central and infinite. Any central
  covering kernel must have at most `r` elements.
- Envelopes mapping onto `EL_n(U)`, `n >= 2`, for a ring `U` whose proper
  two-sided ideals contain an infinite strictly ascending chain.
- fp envelopes with a proper quotient that is not finitely presented, for
  instance `kazhdan-hyperbolic-continuum-non-fng-maximal-kernels`.

## Open side question (spark, not pursued)

Does the universal sandwich ring `U = Z[G~]<p,q>/(p(1-g)q - 1)` have an
infinite strictly ascending chain of proper two-sided ideals? With
`x = p(1-g)` one has `xq = 1`. If `e = 1 - qx != 0`, then the `q^i e x^j` are
matrix units, and the ideals inside `UeU` follow the ideals of the corner
`eUe`. A non-Noetherian corner would kill every envelope mapping onto
`EL_n(U)` for this `U`, the canonical CK ring, whatever the marking.

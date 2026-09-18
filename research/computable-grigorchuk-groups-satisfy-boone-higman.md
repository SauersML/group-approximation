---
rg: 2
id: computable-grigorchuk-groups-satisfy-boone-higman
kind: claim
title: Every Grigorchuk group G_omega with computable omega embeds in a finitely presented simple group
distinct_from:
  fp-self-similar-groups-embed-in-fp-simple-groups: that covers finitely presented self-similar groups, and through contracting self-similar groups (BBMZ) the first Grigorchuk group; this asks for G_omega with an arbitrary computable, possibly non-periodic, omega, which is not self-similar with finitely many states.
  decidable-minimal-subshift-full-groups-satisfy-boone-higman: that is the Juschenko-Monod class; this is the intermediate-growth family that embeds in it.
---

**OPEN.** For every computable `ω ∈ {0,1,2}^N`, the group `G_ω` embeds in a finitely presented
simple group. (`G_ω` has solvable word problem exactly when `ω` is computable, Grigorchuk 1984.)

## Known cases

- The first Grigorchuk group, `ω = (012)^∞`, lies in Röver's finitely presented simple group
  `V(G)`. More generally contracting self-similar groups satisfy Boone–Higman (BBMZ,
  arXiv:2309.06224). For eventually periodic `ω`, `G_ω` is expected to be covered this way, as a
  subgroup of a finite wreath product over the self-similar `G_(v^∞)`, but that is **not checked** here.

## Routes and reductions

- `computable-grigorchuk-bh-via-minimal-subshift-full-groups`: Matte Bon, arXiv:1408.0762 (abstract
  read; body not read) embeds every `G_ω` in `[[T]]'` for a minimal subshift `X_ω` built from
  Schreier graphs. So `G_ω` satisfies Boone–Higman as soon as `X_ω` is Brin–Thompson realizable
  (`decidable-minimal-subshifts-are-brin-thompson-factors`). That `X_ω` has decidable
  language when `ω` is computable is plausible from the construction but not checked.
- The self-similar route (`computable-tree-groups-embed-in-fp-self-similar-groups`, OPEN) also
  applies: `G_ω` has a computable faithful action on the binary tree.

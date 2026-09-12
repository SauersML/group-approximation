---
rg: 2
id: thompson-v-marker-involution-is-stably-formalizable
kind: claim
title: The Thompson V marker involution, after identity ancilla tracks, has a formalizable left inverse
distinct_from:
  thompson-v-marker-involution-is-formalizable: that asks for formalization on the original one-track alphabet over V; this allows identity ancilla tracks, the stable version, which already gives the Kaplansky payoff.
  dihedral-marker-involution-is-stably-formalizable: that is the same object over the infinite dihedral subgroup; a D-equivariant stable formalization there induces one here with the same polynomials.
artifacts:
  - research/artifacts/dihedral-marker-composition-reduction-2026-09-12.md
---

**OPEN.** With `g, s in V` the infinite-order dihedral pair of
`thompson-v-marker-involution-is-formalizable`, let `tau_g` be the marker involution along `g` on
`{0,1}^V`. Then for some `m >= 0`, `tau_g x id_m` on `(F_2^(1+m))^V` has a left-inverse automaton
forming a formalizable pair with `V`-equivariant finite-memory representatives.

`V <= L_(F_2)(1,2)^x`, so a stable formalization here induces one over the binary Leavitt unit group.

## Attempts

- **Inducing from the dihedral core.** A `D`-equivariant stable formalization over `<g, s>` induces
  one over `V` with the same polynomials, because the composite at cell `1` reads only cells of
  `<g, s>` (`thompson-v-marker-stable-formalizability-from-dihedral`,
  `formal-pairs-push-along-quotients-of-the-encoder-memory-group`). So this claim follows from
  `dihedral-marker-involution-is-stably-formalizable`, hence from the integer-marker instance of
  `injective-binary-automata-are-stably-formalizable`.
- **Why stable, not plain.** The Kaplansky payoff on simple hosts needs only stable formalizability
  (`stable-formalization-reduces-surjunctivity-to-kaplansky`), and the composition route reaches the
  stable version but not the plain one, since it spends ancilla tracks.
- **Consequence for the program.** The `V`-marker is not an independent test object for stable
  formalizability: it is downstream of the integer-marker warm-up. Through this route the marker can
  fail on `V` only if the integer-marker instance fails.
- **Where it stops.** The integer-marker instance is open; no obstruction is known.

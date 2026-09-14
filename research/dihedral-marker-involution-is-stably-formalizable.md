---
rg: 2
id: dihedral-marker-involution-is-stably-formalizable
kind: claim
title: The infinite dihedral marker involution, after identity ancilla tracks, has a formalizable left inverse
distinct_from:
  dihedral-marker-involution-is-formalizable: that asks for formalization on the original one-track alphabet over the infinite dihedral group; this allows identity ancilla tracks, the stable version, which already suffices for the Kaplansky payoff on simple hosts.
  injective-binary-automata-are-stably-formalizable: that is the universal stable statement over every group; this is its instance at the dihedral marker, derived here from the integer-marker instance of that same claim.
artifacts:
  - research/artifacts/dihedral-marker-composition-reduction-2026-09-12.md
---

**OPEN.** Let `D = <g, s | s^2, sgs = g^(-1)>` and let `tau` be the marker involution on `{0,1}^D`
that flips cell `h` when `(x(hg^(-3)), ..., x(hg^3)) = (0,0,1,1,0,0)`. Then for some `m >= 0` the
automaton `tau x id_m` on `(F_2^(1+m))^D` has a left-inverse automaton forming a formalizable pair
with `D`-equivariant finite-memory representatives.

**Why it suffices.** Stable formalizability gives the Kaplansky payoff exactly as plain
formalizability does (`stable-formalization-reduces-surjunctivity-to-kaplansky`). So for the
simple-host program the stable version of the marker test object is as good as the plain one, and it
is the version the reduction below reaches.

## Attempts

- **Reduction to the integer marker.** In coset coordinates `a(k) = x(g^k)`, `b(k) = x(g^k s)`, with
  `s` acting by `a(k) <-> b(-k)`, the marker is `tau_Z x tau_Z`, one integer marker on each coset.
  Factoring `tau = (tau_Z x id) o (id x tau_Z)` and composing formal pairs gives
  `dihedral-marker-stable-formalizability-from-integer-marker`: if the integer marker is stably
  formalizable with an ancilla set disjoint from the other coset, then `tau x id` is stably
  formalizable over `D`. See the artifact.
- **Reflection symmetry is free.** Realize `id x tau_Z` with an ancilla set `A1` touching only the
  `b`-coset, and `tau_Z x id` with the reflected ancilla set `A2 = s A1` touching only the `a`-coset.
  As polynomial maps the two factors act on disjoint variables, so they commute and the composite
  encoder `E` satisfies `s E s = E` (with `s` permuting `A1 <-> A2`). So `E` is `D`-equivariant, not
  merely `<g>`-equivariant, which is what the induction to `V` needs.
- **Where it stops.** The hypothesis is exactly the integer-marker instance of
  `injective-binary-automata-are-stably-formalizable`, which is open. No unconditional construction and
  no obstruction is known. Regrouping along `<g^4>` formalizes `tau` over `D` but only
  `<g^4>`-equivariantly, so it does not induce to `V`; the composition route is `D`-equivariant and
  does.

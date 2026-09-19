---
rg: 2
id: decidable-minimal-subshifts-are-brin-thompson-factors
kind: claim
title: Every infinite minimal subshift with decidable language is a factor of some element of some nV acting on a clopen invariant set
distinct_from:
  smart-trace-full-group-embeds-in-brin-thompson-2v: that realizes one subshift, the SMART trace, this way; this asks for every minimal subshift with decidable language.
  fg-full-group-subgroups-factor-onto-subshift-full-groups: that codes an action DOWN to a subshift factor; this asks for a Brin-Thompson dynamical system ABOVE a given subshift.
---

**OPEN.** Call an infinite minimal subshift `(X,T)` *Brin–Thompson realizable* if there are `n`,
`g ∈ nV`, a clopen `U ⊆ C^n` with `g(U) = U`, and a continuous surjection `π : U -> X` with
`π ∘ g = T ∘ π`. The claim: every infinite minimal subshift with decidable language is realizable.

## Why it matters

If `X` is realizable then `[[T]] ≤ nV`, by `aperiodic-full-groups-lift-along-factor-maps` and
`brin-thompson-groups-contain-full-groups-of-their-elements`. Since `nV` is finitely presented and
simple (Brin; Hennig–Matucci for all `n`), this claim gives
`decidable-minimal-subshift-full-groups-satisfy-boone-higman`.

## Established here (lane proofs, elementary; not reviewed)

1. **The hypothesis is necessary.** If `X` is realizable then its language is decidable. The partition
   `P_a = π^-1[a]_0` of `U` is a finite union of dyadic boxes, and `a_0 ... a_(m-1) ∈ L(X)` iff
   `∩_(i<m) g^-i(P_(a_i)) ≠ ∅`. Images of box unions under a box map, their intersections, and
   emptiness are all computable.
2. **Closure properties.** The realizable subshifts are closed under
   - infinite factors: compose the factor maps;
   - products with the diagonal shift: `g_1 × g_2 ∈ (n_1+n_2)V` on `U_1 × U_2`;
   - induced systems on clopen sets `W ⊆ X`: the first return of `g` to `π^-1(W)` has the same return
     times as `T` to `W`, so it is a piecewise power of `g` with bounded exponent, which lies in `nV`
     by the gluing node, and it factors onto `(W, T_W)`.
3. **One instance.** The SMART trace subshift is realizable, with `n = 2`
   (`smart-trace-full-group-embeds-in-brin-thompson-2v`).

## Where the difficulty is

A realization must be aperiodic on all of `U` (points over an aperiodic `X` cannot be periodic), and
`U` is clopen, so every configuration in a whole cylinder must be forced to produce `X`. For
Turing-machine elements of `2V` this is the problem of building a minimal aperiodic reversible
machine whose trace factors onto a prescribed subshift. Such machines are rare (SMART is the known
small one), which is why the claim is left open.

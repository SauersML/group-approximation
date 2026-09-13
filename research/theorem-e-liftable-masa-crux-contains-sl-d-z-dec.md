---
rg: 2
id: theorem-e-liftable-masa-crux-contains-sl-d-z-dec
kind: claim
title: Every relative commutant of a model of SL_d(Z) is the actor commutant of a vertex-rounded Theorem E model, so the liftable-masa crux contains the HS Kun partition problem for SL_d(Z)
distinct_from:
  liftable-masa-in-every-model-iff-uniform-hs-kun-partitions: that equates liftable masas in every model of one Kazhdan group with a dimension-uniform partition inequality; this embeds the models of SL_d(Z) into vertex-rounded trace-preserving models of the Theorem E actor with the same commutant, so the crux implies that inequality for SL_d(Z).
  theorem-e-vertex-types-equidistribute-on-finite-sl-d-orbits: that locates the remaining content of the crux in fibre holonomies of congruence stabilizers, as a reading; this proves the reverse containment, that every model of SL_d(Z) occurs as a fibre holonomy with a single type.
---

**ESTABLISHED.** Let `Gamma = EL_r(F_q[x_1..x_d]) < G = EL_r(L) x| SL_d(Z)`, `L = F_q[x^(+-1)]`, be the
Theorem E pair, with `r >= 3`, `d >= 3` odd and `gcd(r, q - 1) = 1`. Let `quo : G -> SL_d(Z)` be the
quotient map.

1. **Arithmetic tensor model.** For primes `l` not dividing `q`, let `X_l` be the maximal ideals of
   `B_l = L/(x_1^l - 1, ..., x_d^l - 1)`, with residue fields `F_P`. Put
   `tau_l = (x)_(P in X_l) l^2_0(P^(r-1)(F_P))`, the tensor product of the nontrivial parts of the projective
   permutation modules. It is a genuine unitary representation of `G`: `EL_r(L)` acts through
   `EL_r(B_l) = prod_P SL_r(F_P)`, and `SL_d(Z)` permutes the factors through `x^v -> x^(Mv)`. Along
   `l -> infinity`:
   - `tau_l(Gamma)` is irreducible for every `l`;
   - `tr tau_l(g) / dim tau_l -> 0` for every `g != 1` in `G`.
2. **Transfer.** Let `h : SL_d(Z) -> U(prod_U M_(k_n))` be any homomorphism, with no trace condition.
   Choose primes `l_n -> infinity` and put `sigma_n = tau_(l_n) (x) (h_n o quo)` on `C^(N_n) (x) C^(k_n)`.
   Then `sigma : G -> U(prod_U M_(N_n k_n))` is trace-preserving, satisfies (H1) with no padding (its
   vertex restriction is genuine), and

   ```text
   sigma(G)' cap prod_U M_(N_n k_n)   =   1 (x) ( h(SL_d(Z))' cap prod_U M_(k_n) ) .
   ```

   By `liftable-abelian-subalgebras-are-amplification-invariant`, `sigma(G)' cap M` has a liftable masa
   iff `h(SL_d(Z))' cap prod_U M_(k_n)` does.
3. **Consequence.** If `actor-commutant-has-liftable-masa-in-every-model` holds at this pair, then every
   model of `SL_d(Z)` has a liftable masa in its relative commutant. By
   `liftable-masa-in-every-model-iff-uniform-hs-kun-partitions`, `SL_d(Z)` then satisfies the
   dimension-uniform HS Kun partition inequality `DEC_kappa`. Conversely, one model of `SL_d(Z)` whose
   relative commutant has no liftable masa refutes the crux at this pair.

## Reading

- **The crux is a statement about `SL_d(Z)`.** With
  `theorem-e-vertex-types-equidistribute-on-finite-sl-d-orbits`, the remaining content of (LM) at the
  Theorem E pair sits in fibre holonomies of congruence stabilizers. Item 2 shows every model of
  `SL_d(Z)` itself occurs as such a holonomy, on a single fixed type. So the crux at this pair is at
  least `DEC_kappa(SL_d(Z))`. That it is no stronger than the fibre problem for finite-index subgroups
  is the reading in that claim's artifact, not an established implication.
- **Where a counterexample must come from.** Genuine coordinates for `h` always lift
  (`at-op62-holds-for-representation-lifts`). A counterexample needs a model of `SL_d(Z)` that is not
  flexibly roundable to genuine representations. Flexible normalized-HS stability of `SL_d(Z)` is open,
  so the counterexample side of the crux contains that open question.
- **Why the vertex does not help.** The tensor model rounds the vertex exactly and normalizes by
  `vertex-rounding-alone-normalizes-each-theorem-e-model`. The actor commutant it produces is whatever
  `h` makes it. Vertex arithmetic constrains only the type level.
- **Scope.** `d` odd excludes `-I`, which could fix every factor. `gcd(r, q-1) = 1` excludes the central
  scalars of `EL_r(F_q)`, on which every `tau_l` is trivial. Other parameters are not treated.

Derivation: `theorem-e-liftable-masa-crux-contains-sl-d-z-dec-proof`.

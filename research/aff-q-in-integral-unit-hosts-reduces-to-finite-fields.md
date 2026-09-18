---
rg: 2
id: aff-q-in-integral-unit-hosts-reduces-to-finite-fields
kind: claim
title: A copy of Aff(Q) in a finitely generated integral-form unit group already lives over a finite field, so the Leavitt route in characteristic zero adds nothing
distinct_from:
  integral-unit-hosts-for-gl-n-q-reduce-to-finite-fields: that transfers SL_n(Q) and PSL_n(Q) to a finite field using perfectness and simplicity; this transfers Aff(Q), which is neither perfect nor simple, using single-element detection of injectivity.
  cone-sl2-and-v-put-central-scalars-in-derived-subgroup: that scalar wall needs an infinite central subfield; this finite-field wall applies over Z too, where the centre is Z, and also to the subgroup <V, t> of U(L_Z(1,2)).
  rationals-do-not-embed-in-binary-leavitt-unit-group: that is the open F_2 statement for (Q,+); this shows that the characteristic-zero Leavitt route to Aff(Q) needs exactly the negation of that statement, over F_2 or some other F_p.
  aff-q-embeds-in-fp-simple-group: that is the stepping-stone target; this closes one route to it unless a finite-field Leavitt unit group contains Aff(Q).
---

**ESTABLISHED** through `aff-q-in-integral-unit-hosts-reduces-to-finite-fields-proof`
(lane proof, not independently reviewed; elementary, no novelty claimed).

**Setting.** `A` is a unital ring whose additive group is free abelian (an integral
form, for example `L_Z(1,d)`), `K` is any field, `m >= 1`, and `A_K = A ⊗_Z K`.
`Aff(Q) = Q ⋊ Q^x`, with translation subgroup `N ≅ (Q,+)` and `t_1` the
translation by `1`.

**Statement.**
1. **Reduction.** Let `S <= GL_m(A_K)` be finitely generated and `H <= S` a copy
   of `Aff(Q)`. Then for some finite field `F`, one of the reduction maps
   `rho: S -> GL_m(A ⊗ F)` of `integral-unit-hosts-for-gl-n-q-reduce-to-finite-fields`
   (part 1) is injective on `H`.
2. **Leavitt case.** If a finitely generated subgroup of `L_K(1,2)^x`, for any
   field `K`, contains `Aff(Q)`, then `Aff(Q)` embeds in `L_(F_p)(1,2)^x` for some
   prime `p`. So `(Q,+)` embeds in `L_(F_p)(1,2)^x`, and the image of `t_1` has
   infinite centralizer rank over `F_p` (`unit-roots-divide-centralizer-rank`).
   For `p = 2` this would refute the open
   `rationals-do-not-embed-in-binary-leavitt-unit-group`; for odd `p`, its `F_p`
   analogue.
3. **Power conjugacy of `t` happens for only finitely many primes.** Let
   `char K = 0`, let `S <= L_K(1,2)^x` be finitely generated with
   `t = 1 + x_01 y_00 in S`, and let `D` be its coordinate ring as in part 1. If
   `d in S` and `d t d^(-1) = t^p` for a prime `p`, then `p` is a unit of `D`. Only
   finitely many primes are. Hence:
   - no finitely generated subgroup of `L_K(1,2)^x` contains elements `d_p`, for
     infinitely many primes `p`, with `d_p t d_p^(-1) = t^p`, whether finite-type
     or dynamical;
   - in particular none contains a copy of `Aff(Q)` whose translation subgroup
     contains `t`, such as one extending the root tower
     `phi: Q -> <V, t>` of `integral-leavitt-unit-group-contains-q`.

   This is sharp for finitely many primes: over `Z[1/p]`, the finite-type unit
   `d = u(Gamma_1, diag(1,p))` satisfies `d t d^(-1) = t^p`.
4. **The host `<V, t>` is not simple modulo congruences.** Its commutator subgroup
   `<V, t>'` contains `t`, and for every prime `p` the congruence kernel
   `ker(rho_p) ∩ <V, t>'` contains `t^p != 1` but not `t`. So `<V, t>'` is not
   simple, and `<V, t>` embeds in `∏_p L_(F_p)(1,2)^x`.

## Consequences for `gl-n-q-embeds-in-fp-simple-group`

- **Characteristic 0 escapes the scalar wall but not the finite-field wall.**
  Integer coefficients, where the centre is `Z`, avoid
  `leavitt-scalar-commutators-block-fp-central-quotients`. But by part 1 every
  copy of `Aff(Q)`, and by `integral-unit-hosts-for-gl-n-q-reduce-to-finite-fields`
  every copy of `SL_n(Q)` or `PSL_n(Q)`, in a finitely generated Leavitt unit host
  over any field already lives in `L_(F_p)(1,2)^x` for some prime `p`. Since
  `Aff(Q) <= B_2(Q) <= GL_2(Q)`, this covers `SL_2(Q)`, `GL_2(Q)` and every
  `GL_n(Q)`.
- **One statement closes the Leavitt route for all these groups.** Suppose `(Q,+)`
  embeds in `L_(F_p)(1,2)^x` for no prime `p`, as would follow from the finite-rank
  statement of `leavitt-unit-centralizers-have-finite-rank` for every `F_p`. Then no
  finitely generated subgroup of any `L_K(1,2)^x` contains `Aff(Q)`, `SL_n(Q)` or
  `GL_n(Q)` (`n >= 2`).
- **Where the characteristic-0 `(Q,+)` can still help.** Only for groups whose
  injectivity is not detected by one element being nontrivial, such as
  `(Q,+)` and `U_n(Q)` (`gl-n-q-embeddings-detected-by-nontrivial-homomorphisms`,
  parts 1 and 2). They contain no dilations. Every stepping stone that contains
  dilations for all primes (`Aff(Q)`, `B_n(Q)`, `SL_n(Q)`, `GL_n(Q)`) reduces to a
  finite field. So `U_3(Q)` (`u3-q-embeds-in-fp-simple-group`) is the one rational
  stepping stone left open for characteristic-0 Leavitt hosts such as `<V, t>`.

## Attempts

- **Dynamical conjugators on the transvection tower** (proposed by the
  coordinator, 2026-09-17). The idea was to use `V`-cone dynamics to find `d_p` with
  `d_p a d_p^(-1) = a^p` on the root tower. This dies by part 3, even before
  finite presentation is considered. An earlier obstruction already excluded
  `d t d^(-1) = t^p` for every unit `d` of `L_Z(1,2)` (cokernel of `x - 1` on
  `LC(C,Z)`; see `integral-leavitt-unit-group-contains-q`). Part 3 extends this to
  every characteristic-0 coefficient field. There, power conjugacy of `t` is
  possible, but only for the finitely many primes that are inverted in the
  coefficients.

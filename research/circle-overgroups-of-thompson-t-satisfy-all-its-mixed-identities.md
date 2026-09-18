---
rg: 2
id: circle-overgroups-of-thompson-t-satisfy-all-its-mixed-identities
kind: claim
title: Every group of orientation-preserving circle homeomorphisms containing Thompson's T in its standard action satisfies every mixed identity of T
distinct_from:
  homeo-circle-three-arc-commutator-word-is-mixed-identity: that exhibits one explicit mixed identity shared by all circle groups containing three suitably supported constants; this proves every mixed identity of T, in every number of variables, holds in every circle overgroup of T.
  thompson-t-mixed-identity-problem-is-decidable: that decides membership in J_k(T); this shows J_k(T) is unchanged by passing to any circle overgroup, so no circle overgroup can separate a finite basis from J_k(T).
  fp-simple-group-with-non-finitely-based-mixed-identities: that is the open claim asking for overgroups that satisfy a finite set of identities but not all; this rules out every circle overgroup of T as such a witness.
  bffhz-q32-forces-finitely-based-mixed-identities: that proves finite presentation of the BFFHZ action image forces a finite basis over all overgroups; this restricts which overgroups can test that basis at T.
---

**ESTABLISHED** by `circle-overgroups-of-thompson-t-mixed-identities-proof`.
Not independently reviewed; no novelty claimed. The density of `T` in
`Homeo+(S^1)` is folklore, but it is proved in full here.

Notation is as in `bffhz-q32-forces-finitely-based-mixed-identities`: for
`S <= M` put `J_k(M; S) = { w in S * F_k : w(g) = 1 for all g in M^k }`, with
the constants in `S` evaluated by the inclusion.

## Statement

**(A) Density.** Thompson's `T`, in its standard action on `S^1 = R/Z`, is
dense in `Homeo+(S^1)` for the uniform metric `d(f, g) = sup_p |f(p) - g(p)|`.

**(B) Closure principle.** Let `H` be a Hausdorff topological group and
`S <= M <= H` with `M` contained in the closure of `S`. Then
`J_k(M; S) = J_k(S)` for every `k >= 1`.

**(C) Circle overgroups.** If `T <= M <= Homeo+(S^1)`, with `T` in its standard
action (or any conjugate of it by a homeomorphism of `S^1`), then
`J_k(M; T) = J_k(T)` for every `k >= 1`.

**(D) Ultrapowers.** For any group `S`, index set `I` and ultrafilter `U` on
`I`, every `M` with `S <= M <= S^I / U`, where `S` sits diagonally, has
`J_k(M; S) = J_k(S)` for every `k`.

**(E) Closure under products.** If each `M_i ⊇ S` has `J_k(M_i; S) = J_k(S)`,
then so does every `M` with `S <= M <= ∏ M_i`, where `S` sits diagonally.

**(F) Blow-ups along irrational orbits.** Let `Q ⊂ S^1` be a union of `T`-orbits
of irrational points. Form the circle `C` by inserting an open interval `I_q` at
each `q in Q`, with summable lengths. Let `π : C -> S^1` collapse each closed
gap to its point. Let `M_Q` be the group of homeomorphisms `f` of `C` such that
`π f = t π` for some `t in T` and `f` maps each gap `I_q` onto `I_(tq)`. So the
maps between gaps are arbitrary. `T` embeds in `M_Q` through the maps that are
affine on every gap. Then `J_k(M_Q; T) = J_k(T)` for every `k`. Part (B) does
not give this directly, because the closure of `T` in `Homeo+(C)` consists of
maps that are affine on the gaps.

## Consequence for the finite basis question

`fp-simple-group-with-non-finitely-based-mixed-identities` needs, for each finite
`W`, an overgroup `M_W ⊇ T` that satisfies `W` but not all of `J_1(T)`.

- By (C), no `M_W` acts faithfully on the circle by orientation-preserving
  homeomorphisms extending the standard action of `T`.
- This kills Attempt 3 there. Its candidate overgroups, with breakpoints in
  `Z[1/(2q)]` and slopes in `<2, q>`, lie in `Homeo+(S^1)`. The step that dies
  is "the three-arc mechanism needs an arc arrangement that must fail somewhere
  in such an overgroup". No identity of `T` fails in any such group.
- The same holds for smooth, piecewise-projective and all other circle
  overgroups, and for their subgroups of products and of ultrapowers of `T`, by
  (D) and (E).

**Named invariant.** Say `M ⊇ S` is *S-dense* if some Hausdorff group topology
on a group containing `M` has `M` inside the closure of `S`. By (B), an S-dense
overgroup satisfies all of `J_*(S)`. So every witness `M_W` must be non-T-dense.

## What survives

- Overgroups whose `T`-subaction on the circle is not conjugate to the standard
  one. (F) kills the Denjoy blow-ups along irrational orbits, even though `T` is
  not dense there.
  - *The invariant (F) uses.* At an irrational point every element of the
    stabilizer in `T` is the identity near that point. So the gaps can be
    mirrored by small arcs in `S^1`.
  - *What survives on the circle.* Blow-ups along orbits of rational points,
    dyadic or not. At such points the stabilizers have nontrivial germs, for
    example slope `4` at `1/3`. The gap action of the stabilizer then need not
    mirror anything in `S^1`. Among blow-ups this is the family left untested.
    Circle actions of `T` not obtained by blowing up orbits are not examined.
- Overgroups not acting on the circle at all, such as amalgams, HNN extensions
  and the canonical witnesses `(T * <x>) / N_W` of part (B) of
  `bffhz-q32-forces-finitely-based-mixed-identities`.

## Reframing

By (A) and (B), `J_k(T) = J_k(Homeo+(S^1); T)`. The mixed identities of `T` are
exactly the mixed identities of the Polish group `Homeo+(S^1)` whose constants
happen to lie in `T`. The finite basis question at `T` is therefore a question
about `Homeo+(S^1)` with constants from `T`.

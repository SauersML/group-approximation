---
rg: 2
id: fp-simple-group-with-non-finitely-based-mixed-identities
kind: claim
title: Some infinite finitely presented simple group has one-variable mixed identities that are not finitely based over its overgroups
distinct_from:
  fp-simple-group-with-nonrecursive-mixed-identities: that asks for an undecidable set of mixed identities; this asks only for the failure of a finite basis over overgroups, which that would imply by part (C) of `bffhz-q32-forces-finitely-based-mixed-identities`, and which can hold for a recursive set such as that of Thompson's T.
  bffhz-q32-forces-finitely-based-mixed-identities: that proves a finite basis is necessary for BFFHZ Question 3.2 at one group; this asks for a group where the necessary condition fails.
  fp-simple-groups-embed-in-fp-simple-mif-groups: that asks whether mixed identities can be removed in a finitely presented simple overgroup; a witness here does not refute that, but blocks the one explicit route to it through Question 3.2.
  q34-counterexample-necessary-conditions: that lists properties a counterexample to Question 3.4 must have; a witness here is only a counterexample to Question 3.2, which is a stronger statement.
---

**OPEN.** Definitions are as in `bffhz-q32-forces-finitely-based-mixed-identities`.

## Statement

Some infinite finitely presented simple group `S` has the following property. For
every `m` and every finite `W ⊆ J_m(S)`, some group `M ⊇ S` satisfies `W` but has
a one-variable mixed identity `u in J_1(S)` with `u(g) != 1` for some `g in M`.

By part (B) of that claim, this says: for no finite `W` is `J_1(S)` the normal
closure in `S * <x>` of the substitution instances of `W`.

## Why it matters

- **Refutes Question 3.2 at every rank.** By the contrapositive of
  `bffhz-q32-forces-finitely-based-mixed-identities`, a witness `S` has
  `Aut_S(S * F_n)` modulo its action kernel not finitely presented for every
  `n >= 2`. That answers BFFHZ Question 3.2 (`bffhz-q32-for-fp-simple-groups`)
  negatively.
- **Blocks the route to Question 3.4.** `q34-from-bffhz-q32-for-fp-simple-groups`
  gives nothing for `S`. What remains is an embedding of `S` into some other
  actor, whose kernel must behave differently.
- **Weaker than the undecidability target.** A witness to
  `fp-simple-group-with-nonrecursive-mixed-identities` with `k = 1` is also a
  witness here, by part (C). The converse need not hold: this claim can be tested
  on groups with decidable mixed identities.

## Attempts

1. **MIF groups: die.** `J_1(S)` is trivial and `W = ∅` is a basis.
2. **Where a witness can live (2026-09-17, lane `c-mif`).**
   - *Non-MIF is required.* A witness must have a nontrivial mixed identity.
   - *Type (A) actions do not exclude it.* Unlike for Question 3.4, a type (A)
     action of `S` is not an obstruction: the finite basis concerns the Theorem C
     actor of `S`, not membership of `S` in the permutational class. So the
     Leavitt unit groups of Attempts 5--7 of
     `fp-simple-groups-embed-in-fp-simple-mif-groups` stay candidates whenever they
     are not MIF.
   - *First test case.* Thompson's `T`, with its explicit three-arc commutator
     identity (`homeo-circle-three-arc-commutator-word-is-mixed-identity`).
3. **Thompson's `T`: untested, one heuristic.**
   - *Decidability.* `J_k(T)` is recursive
     (`thompson-t-mixed-identity-problem-is-decidable`, through feasibility over
     `Z[1/2]`), so part (C) gives no obstruction.
   - *Candidate overgroups.* Circle groups that contain `T` but carry more
     piecewise-linear data, for example breakpoints in `Z[1/(2q)]` and slopes in
     `<2, q>` for an odd prime `q`. A fixed finite `W` constrains, heuristically,
     only boundedly many breakpoints and slopes along each trajectory, while the
     three-arc mechanism needs an arc arrangement that must fail somewhere in such
     an overgroup.
   - *What is missing.* No computation or proof shows that some identity of `T`
     fails in such a group while a given `W` holds. The heuristic is recorded as a
     search direction only.
4. **Not a Question 3.4 counterexample.** A witness still might embed in a
   finitely presented simple MIF group by a different actor. Part (A) of
   `bffhz-q32-forces-finitely-based-mixed-identities` rules out only the Theorem C
   actor of `S` itself.
5. **Circle overgroups of `T`: die (2026-09-18, belief breaker, family
   `host-geometry`).** By `circle-overgroups-of-thompson-t-satisfy-all-its-mixed-identities`,
   every `M` with `T <= M <= Homeo+(S^1)`, in the standard action, has
   `J_k(M; T) = J_k(T)` for all `k`.
   - *Why.* `T` is uniformly dense in `Homeo+(S^1)`, by Lemma L2 (T) on a fine
     dyadic grid, and word maps are continuous.
   - *What dies.* Every candidate of Attempt 3, with breakpoints in `Z[1/(2q)]`
     and slopes in `<2, q>`. The dying step is "the three-arc mechanism needs an
     arc arrangement that must fail somewhere in such an overgroup": no identity
     of `T` fails in any circle overgroup.
   - *Also dead.* Ultrapowers of `T`, products of dead overgroups, and Denjoy
     blow-ups along irrational `T`-orbits with arbitrary gap maps. Density does
     not reach the last case. It dies because stabilizers of irrational points
     have trivial germs, so gaps can be mirrored by small arcs.
   - *Named invariant.* A witness `M_W` must be non-T-dense: no Hausdorff group
     topology on a group containing `M_W` puts `M_W` in the closure of `T`.
   - *What survives.* Among circle overgroups that collapse onto the standard
     action along gaps, only blow-ups along rational orbits survive. There the
     stabilizer germs are nontrivial. Circle actions of `T` of other kinds are
     not examined. Off the circle, amalgams, HNN extensions and the canonical
     quotients `(T * <x>) / N_W` survive.
   - *Reframing.* `J_1(T) = J_1(Homeo+(S^1); T)`, so at `T` the question is one
     about mixed identities of the Polish group `Homeo+(S^1)` with constants
     from `T`.

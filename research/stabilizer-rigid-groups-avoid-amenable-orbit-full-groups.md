---
rg: 2
id: stabilizer-rigid-groups-avoid-amenable-orbit-full-groups
kind: claim
title: Non-amenable groups with trivial or regular characters, such as Thompson's V, act trivially by amenable-orbit piecewise translations
distinct_from:
  amenable-full-group-forces-invariant-measure: That shows an amenable group realizing moving bisections forces an invariant measure, which removes compressible hosts from the amenable question; this shows a character-rigid non-amenable group, V in particular, has no nontrivial realization inside any measure-preserving amenable orbit full group, which removes every group containing V from the sofic certificate.
  thompson-v-character-simplex: That imports the Dudko--Medynets classification of characters of V; this consumes it to exclude V from measure-preserving amenable orbit full groups.
  thompson-v-sofic-iff-not-permutation-stable: That uses the same character simplex to equate nonsoficity of V with permutation stability; this uses it to show that no p.m.p. amenable orbit relation can host V nontrivially.
---

**ESTABLISHED.**

**Setting** (as in `amenable-orbit-full-group-subgroups-are-sofic`). `Lambda`
is countable amenable and acts essentially freely, preserving `mu`, on a
standard probability space `X`; `W(Lambda ~ X)` is the group of Borel bijections
`g` with `g(x) = c_g(x) x` for a Borel `c_g` of finite range.

**Theorem.** Let `Gamma` be a countable infinite simple non-amenable group whose
normalized characters (positive-definite class functions `phi` with
`phi(1) = 1`) are exactly the functions

```text
phi_s = s 1 + (1 - s) delta_1,     0 <= s <= 1.                    (CR)
```

Then every homomorphism `rho : Gamma -> W(Lambda ~ X)` acts trivially almost
everywhere: `mu(Fix rho(g)) = 1` for all `g`.

**Instance: Thompson's V.** `V` satisfies (CR) by `thompson-v-character-simplex`,
is infinite and simple by `thompson-v-finitely-presented-infinite-simple`, and is
not amenable (proved in the route). Consequently:
- no group containing `V` has a homomorphism into any `W(Lambda ~ X)` with
  `mu(Fix rho(g)) < 1` for all `g != 1`;
- in particular no simple group containing `V` acts nontrivially, and no
  topological full group `[[Lambda ~ X]]` of an amenable `Lambda` with an
  essentially free invariant measure of full support contains `V`.

So the sofic certificate of `amenable-orbit-full-group-subgroups-are-sofic` is
closed for every finitely presented simple group containing `V`: the Thompson-like
families, the SFT full groups and the Leavitt unit groups listed in
`fp-infinite-simple-amenable-group`.

**The mechanism, in one line.** A nontrivial realization gives the character
`g -> mu(Fix g)`; (CR) makes the action essentially free off the global fixed
points; a free measure-preserving action inside an amenable orbit relation makes
the group amenable.

**Scope.** The proof uses (CR) only to make the action essentially free off its
fixed-point set. Any non-amenable group with that property is excluded the same
way. This includes groups whose only ergodic invariant random subgroups are
trivial, by ergodic decomposition of the stabilizer map; that variant is not
separately recorded here.

Proof: `stabilizer-rigid-groups-avoid-orbit-full-groups-proof`.

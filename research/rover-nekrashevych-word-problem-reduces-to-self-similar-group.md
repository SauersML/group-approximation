---
rg: 2
id: rover-nekrashevych-word-problem-reduces-to-self-similar-group
kind: claim
title: The word problem of a Rover--Nekrashevych group reduces to that of its self-similar group with exponential rescaling
distinct_from:
  fp-self-similar-groups-embed-in-fp-simple-groups: that imports the embedding of a finitely presented self-similar group into the finitely presented simple commutator subgroup of its Rover--Nekrashevych group; this bounds the word-problem complexity of that host from above by the complexity of the self-similar group, so the host is never harder than its input up to exponential rescaling.
  rational-homeomorphism-subgroups-have-exponential-wp: that gives one uniform exponential bound for groups of rational homeomorphisms, including finite-state self-similar groups; this bound is relative, for an arbitrary finitely generated self-similar group with decidable word problem and possibly infinitely many states, and it carries the group's own complexity into the host.
  simple-envelope-forces-solvable-word-problem: that deduces decidability of a subgroup from a finitely presented simple envelope, with no time bound; this is a quantitative upper bound for one specific envelope construction in terms of the input group.
---

**ESTABLISHED.** Let `d >= 2`, `X = {0,...,d-1}`, and let `G <= Aut(T_d)`
be a finitely generated self-similar group with decidable word problem. Let
`V_d(G)` be its Rover--Nekrashevych group: the homeomorphisms `f` of `X^omega`
for which there are complete prefix codes `{u_1..u_k}`, `{v_1..v_k}` and
`g_1..g_k in G` with `f(u_i zeta) = v_i g_i(zeta)` for all `zeta`.

If the word problem of `G` is decidable in time `T` (non-decreasing), then for
every finite generating set of `V_d(G)` there is a constant `c` such that its
word problem is decidable in time

```text
2^(c*l) * ( T(2^(c*l)) + 2^(c*l) ).                                  (RN1)
```

Every finitely generated subgroup of `V_d(G)` inherits a bound of the same
form, with a different constant, by the length-linear substitution of
`complexity-bounded-host-classes-are-not-universal-proof`. In particular this
applies to the finitely presented simple commutator subgroup
`[V_d(G),V_d(G)]` of `fp-self-similar-groups-embed-in-fp-simple-groups`.

## Payoff

This construction produces hard finitely presented simple groups exactly when
it is fed hard finitely presented self-similar groups.
- **One direction.** If some recursive `g` bounds every finitely presented
  self-similar group, in the sense of
  `F(g) = { L : L decidable in time C*g(C*n)+C*n+C }`, then `(RN1)` bounds
  every Rover--Nekrashevych host by the recursive function
  `2^n * (g(2^n) + 2^n)`, after absorbing constants. The wall
  `complexity-bounded-host-classes-are-not-universal` then makes this family of
  hosts non-universal.
- **Other direction.** A self-similar group embeds in its finitely presented
  simple host, so hardness passes up by the same substitution. That is the
  route `arbitrarily-complex-fp-simple-via-hard-self-similar-groups`.

So the self-similar branch of `fp-simple-groups-with-arbitrarily-complex-word-problem`
is equivalent to `fp-self-similar-groups-with-arbitrarily-hard-word-problem`.
The host adds no complexity of its own: everything must already be in `G`.

## Scope

- Only decidability and self-similarity of `G` are used. There is no finite
  presentation, contraction or finite-state hypothesis.
- The exponential in `(RN1)` comes from section-word growth along refinements
  of depth `O(l)`. For contracting `G` it can be improved, but that is not
  needed here.
- Nothing in this claim is new mathematics. It is the tree-pair normal form
  plus section recursion, recorded as a quantitative screen.

DERIVATION
rover-nekrashevych-wp-reduction-proof

---
rg: 2
id: common-higher-rank-context-projections-are-syndrome-cylinders
kind: claim
title: Shared higher-rank abelian context projections are exactly shared-syndrome cylinders
distinct_from:
  literal-common-ghost-atom-classicalizes-contexts: that treats rank-one assignment atoms and forces equality of the full context groups; this classifies every higher-rank common projection and exhibits the proper-subgroup cylinder escape.
  common-meet-local-sectors-pay-one-deficit: that shows why a common projection is analytically valuable; this determines the predicate geometry available from literal finite-subgroup sharing.
---

**ESTABLISHED CLASSIFICATION.**  Let `H_1,H_2` be finite elementary
abelian subgroups of a group `Gamma`, and put `L=H_1 intersection H_2`.
Then

```text
C[H_1] intersection C[H_2]=C[L]       inside C[Gamma].       (SHC1)
```

Consequently every projection `f` which is literally common to the two
context algebras belongs to `C[L]`.  Write its Fourier support in `L` as
`S subseteq dual(L)`.  Viewed inside context `H_i`, the spectral support of
`f` is exactly

```text
{chi in dual(H_i): chi restricted to L lies in S}.             (SHC2)
```

Thus it is a union of complete fibers of the restriction map
`dual(H_i)->dual(L)`: the rejected assignments form a cylinder determined
only by the shared parity syndrome on `L`.

This gives the exact higher-rank alternative left by
`literal-common-ghost-atom-classicalizes-contexts`.  Proper private context
extensions can remain noncommuting, but a literal shared rejection
projection cannot distinguish assignments within one shared-syndrome fiber.
In particular a singleton one-ghost atom can be shared only when
`L=H_i` for both contexts, recovering full context identification and
classicalization.

Therefore a higher-rank common rejection packet can satisfy the actual-meet
bookkeeping `(CHD3)` only for a cylinder-type local rejection event (or a
union of such syndromes).  To use it for a one-ghost/nonaffine predicate one
must add a genuinely nonliteral Morita/Hecke overlap or extra constraints
which isolate one point inside the fiber; literal subgroup amalgamation
alone does not do so.


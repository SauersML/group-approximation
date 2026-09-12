---
rg: 2
id: jacobson-165-seed-fails-full-root-intersection
kind: claim
title: The specified 165-dimensional Jacobson seed matches the smaller overlap but fails the full root intersection
distinct_from:
  jacobson-double-rank-one-root-orbit-cannot-extend: that excludes every two-dimensional rank-one root fiber; this excludes one specified three-dimensional-fiber seed and its head-trivial spectators by a stabilizer character on the full intersection.
  jacobson-first-root-packet-admits-coherent-relative-correction: that constructs compatible exact root packets from sufficiently accurate mixed models; this rules out a particular proposed pair of finite representation profiles after examining their actual intersection.
artifacts:
  - research/artifacts/jacobson-165-seed-full-intersection-obstruction-2026-09-08.md
---

Use `P=N semidirect F`, `J`, and
`I=N_0 semidirect (P_Q x K_P)` from the coherent first-root
correction, where `N_0` consists of the four matrix coordinates
with row and column indices in `{1,3}`. Write `rho_0` for the
seven-point representation of `G=GL_3(F_2)`, `sigma_3` for either
three-dimensional irreducible, and `chi_6` for its six-dimensional
irreducible. Let `S` be the standard three-dimensional representation
of a target stabilizer `S_4`, `t_2` its two-dimensional irreducible,
and `s` its sign character. Put

```text
V=Ind_(S_4)^G(S)=chi_6+chi_7+chi_8.
```

Consider the `P` representation whose nontrivial `N` part is the
rank-one character orbit with trivial head stabilizer action and
target fiber either `S` or `t_2+s`, and whose `N`-trivial part is
`chi_6,Q tensor sigma_3,P`. Its restriction to `F` is

```text
(rho_0)_Q tensor V_P
  direct-sum chi_6,Q tensor sigma_3,P,
```

of dimension 165. Both target fibers induce the same `V`; these
are two distinct `P` profiles with that carrier. Exact `J`
representations of dimension 165 match this whole restriction on
the smaller overlap `L'=P_Q x K_P`. Nevertheless neither `P`
profile admits an exact `J` representation agreeing on all of `I`.
The exclusion also holds after adding arbitrary head-trivial,
`N`-trivial spectators.

More precisely, for the nonzero `N_0` character indexed by the
head plane vector `e_1` and tail plane covector `e_1^*`, the
stabilizing element `z=x_31,P` has trace zero or four on its
12-dimensional `P` spectral subspace. Every possible `J` fiber
compatible with the nontrivial head types gives trace six, two, or
minus two there. Thus an isomorphism on `I` is impossible.

The artifact also proves the general head-parabolic multiplicities
`4m_+ +6m_2` and `4m_- +6m_2` for the two three-dimensional
head types of any `J` representation. This rejects the tentative
156-dimensional seed with the same 147-dimensional carrier and
`sigma_3,Q tensor sigma_3,P` complement, whose two multiplicities
are 21 and three.

This is a seed-specific representation obstruction. It does not
exclude every dimension-165 profile, all three-dimensional root
fibers, or the unbounded matrix dimensions in the mixed-gap problem.

DERIVATION
jacobson-165-seed-stabilizer-trace-proof

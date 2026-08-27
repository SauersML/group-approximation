---
rg: 2
id: carmichael-edge-hodge-operator-has-root-m-norm
kind: claim
title: The Carmichael edge incidence operator of an R5 packet has square-root norm
artifacts:
  - research/artifacts/thompson-subquadratic-carmichael-energy-2026-08-24.md
distinct_from:
  r5-subquadratic-carmichael-energy: that is the weakest aggregate hypothesis the collapse theorem consumes, an `o(M^2)` statement with a model-dependent implied constant; this is the strictly stronger linear bound `E_M <= C M def_R(U)^2` with a presentation constant, obtained from an operator norm.
  collective-centralizer-cycles-are-free-gauge-identities: that identifies the free gauge kernel as an information-free telescoping identity; this asks for the complementary positive estimate on the non-gauge component, and must additionally kill the common mode that cycle identities cannot see.
  a5-carmichael-triangle-covers-involution-kernels: that is a fixed three-channel spectral gap inside one `A_5`; this is an `M`-dependent operator norm bound on the whole edge field of an unbounded packet, and would consume that gap rather than restate it.
  self-similar-square-function-checksum-compiler: that compiles a multiscale checksum from self-similar cylinder returns; this is a single-scale incidence estimate on the Carmichael edges of one common-pivot star.
---

Fix the Bleak--Quick presentation `V=<X|R>`, the mark `b=(01 10 11)`, and a
model `U in U(d)^X`.  Give `M_d` the normalized Hilbert--Schmidt inner
product and let

```text
H_M = direct sum over pairs i<j of M_d
```

carry the edge field `e=(e_(ij))` with `e_(ij)=(X_iX_j)^2-I` of a
common-pivot packet `X_i=U(g_i)^*U(b)U(g_i)`.  Prove the following.

There are a constant `C`, depending only on the presentation, and an integer
`K`, independent of `M`, such that for arbitrarily large `M` the packet may be
chosen with a decomposition

```text
e = T_M f + D^* q,                                            (SF1)
```

where `f=(f_1,...,f_K)` is a tuple of translated defining-relator residuals
`f_k = V_k (r_k(U)-I) V_k'` with `r_k in R`, where `D^*` is the coboundary of
the vertex-gauge space of the packet, where the two summands are orthogonal in
`H_M`, and where

```text
||T_M||_(2->2) = O(sqrt M).                                   (SF2)
```

Consequently

```text
E_M = ||e||^2 <= C M sum_(r in R) ||r(U)-I||_2^2
              <= C |R| M def_R(U)^2.                          (SF3)
```

`(SF3)` gives `r5-subquadratic-carmichael-energy` immediately, since
`M = o(M^2)`.

## What the bound actually demands

The edge field has `M(M-1)/2` slots and the source `f` has a fixed number `K`
of them, so `(SF3)` says the root-mean-square edge defect is

```text
(2E_M/(M(M-1)))^(1/2) = O(def_R(U)/sqrt M).
```

A proof must therefore show that almost every Carmichael edge is *far* better
than the generic telescoping estimate `||q(U)-I||_2 <= Area * def_R(U)`, which
gives only `O(def_R(U))` per edge and hence `O(M^2 def_R(U)^2)` in total.  The
entire content is cancellation across the packet.  This is a strictly stronger
statement than what the collapse theorem needs, and it is proposed only
because it is the shape a Hodge argument would produce.

## Attempts

- **The scalar common mode refutes the bound.**
  In `scalar-phase-refutes-r5-subquadratic-energy`, all conjugates of the
  marked matrix equal `zI`, so the edge field is the nonzero constant field
  `(z^4-1)I`.  Its squared norm is `Theta(M^2)`, while `(SF3)` is only
  `O(M def_R(U)^2)`.  Thus the previously uncontrolled common mode is not
  merely a technical gap: it is an exact counterexample to `(SF1)--(SF3)`.

- **The gauge half is already understood, and it is empty.**
  `collective-centralizer-cycles-are-free-gauge-identities` proves the exact
  free identity `r_(ij)^(h_j^(-1)) = Q_j Q_i^(-1)` and hence that every
  directed cycle of endpoint corrections freely reduces to the empty word.
  In the language of `(SF1)` that is the statement that the cycle-space
  component of the correction field is a pure coboundary, so it carries no
  matrix information.  This is why `(SF1)` splits off `D^* q` rather than
  trying to estimate it: the target is the complement.
- **The common mode is the open piece.**  A cycle identity is blind to a
  constant shift of the vertex gauges, so the splitting `(SF1)` is not
  canonical until the common mode is fixed.  The candidate tool is the
  positive local relation of
  `a5-carmichael-triangle-covers-involution-kernels`: its inequality `(A5K1)`
  says that the three involutions of one Carmichael triangle cannot be
  simultaneously blind, so a triangle-indexed sum of squares is bounded below.
  Applying it to combined edge errors — rather than to separately filled
  centralizer commutators, which
  `orthogonal-centralizer-channels-retain-area-properness` shows gains nothing
  — is untried.
- **No area is charged, so the area firewalls do not fire.**
  `finite-mark-centralizer-commutator-area-is-proper` bounds filling areas
  from below and `thompson-v-r5-uniform-common-pivot-centralizers` is refuted
  by it; neither touches `(SF2)`, which is an operator norm on an already
  linearized field.  The proposal survives those obstructions by construction,
  which is also why it carries no evidence from them.
- **Linearization is not free.**  `(SF1)` is written as an exact splitting,
  but the natural derivation is first-order in the residuals, and
  `normalized-hs-tangent-quotient-is-nonabelian` records that first-order
  linearization of near-identity errors in normalized HS is exactly where
  sparse Pauli blocks break the analogous asymptotic-cohomology argument.  A
  serious attempt must either produce an exact `(SF1)` with a controlled
  remainder or explain why the sparse-block counterexample does not apply to
  the Carmichael edge field.
- **Cheap falsification test.**  Form the linearized occurrence boundary of
  the packet, as in the fast test of
  `thompson-v-r5-coherent-alternating-packet`, and track the operator norm of
  the induced edge map as `M` grows.  Growth faster than `sqrt M` refutes
  `(SF2)` for that construction of the packet.  This has not been run.

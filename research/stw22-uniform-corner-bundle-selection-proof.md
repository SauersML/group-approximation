---
rg: 2
id: stw22-uniform-corner-bundle-selection-proof
kind: route
title: Stabilize the L2 field and use uniform corner contractions to select weighted copies in all degrees
target: stw22-uniform-corner-bundles-have-uniform-traces
requires:
  - stw22-full-fundamental-group-weighted-copy-all-sphere-fillings
  - stw22-dim2-factor-bundles-have-uniform-traces
  - stw22-tracefree-fibre-gap-ideals-force-trace-continuity
artifacts:
  - research/artifacts/stw22-uniform-corner-bundle-selection-audit-2026-08-30.md
---

Write `N_x=M_x` and use the ambient fibre trace throughout.

## 1. The corner datum gives uniform Stiefel spheres

Fix `0<=k<=d-1`, a projection-weight frame `v_0` in one `N_x`, and its
final projection `q_0`.  For a variable frame `v`, the conjugator value is

```text
G_x(v_0,v)={u in U(N_x):uv_0=v}
 =u_v(q_0+U((1-q_0)N_x(1-q_0))).                      (UC1)
```

The universal polar correction proves, independently of `x,q_0`, that
these values are closed and lower semicontinuous and that

```text
dist(1,G_x(v_0,v))<13||v-v_0||_2.                    (UC2)
```

The hypothesis makes all values in `(UC1)` uniformly equi-`LC^(k-1)`.
They are globally `(k-1)`-connected because every separable-predual `II_1`
factor corner unitary group is contractible by Jekel; the zero corner is a
singleton.  Gutev's controlled Michael theorem over `S^k` therefore lifts
every sufficiently small Stiefel sphere to a small sphere in `U(N_x)`, with
one input modulus independent of `x` and of the source projection.  The
degree-`k` part of the uniform corner hypothesis, applied with `r=1`, fills
that unitary lift in a small ball.  Multiplication by `v_0` gives a small
Stiefel filling together with a unitary lift on `B^(k+1)`.

For global connectivity, the uncontrolled Michael theorem lifts an
arbitrary Stiefel `S^k`; Jekel contractibility of `U(N_x)` fills the lift.
Thus the Stiefel spaces across all fibres and all source projections are
globally `k`-connected and uniformly equi-`LC^k`.  When `k=0`, use the
direct principal-logarithm path argument.  Multicopy frames reduce
isometrically to one Stiefel space inside `N_x`, so no matrix amplification
or replication-number dependence appears.

## 2. Uniform weighted spheres

For a positive contraction `a in N_x`, cut at a small scalar `eta`.  The
high polar multicopy frame amplifies weighted displacement by at most
`eta^(-1/2)` and is filled by Step 1 with a unitary lift.  Extend the low
part in the moving complement by the dimension-free unitary-lifted
spectral-band recursion.  Each bounded band is a Stiefel `S^k` in one
fixed complement corner; the preceding global lifting and Jekel filling
extend it and explicitly trivialize the next complement.  Strict total
support slack leaves a nonzero complement at every finite stage.

Only the orthogonal weighted band sums are passed to a limit.  Their tails
converge uniformly in `2`-norm, their operator norms are uniformly bounded,
and products converge in `L^1`; hence the limits lie in `N_x` and preserve
the exact source, range orthogonality and boundary.  The low displacement
is at most `2sqrt(eta)`.  It follows that, for every `k<=d-1`, the strictly
slack weighted-copy fibres over all `x`, weights and copy numbers are
globally `k`-connected and have one equi-`LC^k` modulus.  Take the minimum
of the finitely many degree-wise moduli when invoking degree `d-1`
selection.

## 3. Stabilized selection and gap traces

Kasparov stabilization embeds the countably generated intrinsic Hilbert
`C(K)`-module as a complemented submodule of `C(K,ell^2)`.  For a fixed
positive contraction `a in M`, copy number `m`, and uniform strict support
slack, regard the exact copy sets `F_x(a_x)` as subsets of the one complete
space `(ell^2)^m`.  The uniform finite-factor correction lemma makes this
multifunction lower semicontinuous with nonempty closed values.  Step 2,
the usual fibre-centred-to-ambient-centred conversion, and equivalence of
the maximum and Hilbert-sum metrics for fixed `m` give precisely the
global connectivity and equi-`LC^(d-1)` hypotheses of Michael's theorem.
It selects an exact continuous weighted tuple.  The operator-ball recovery
identity puts its components back in `M`.

Given a positive fibre-gap element, a spectral cut and central cutoff make
it globally slack with support trace below `1/(2m)`.  The selected `m`
orthogonal copies bound every bounded positive gap trace by its norm divided
by `m`.  Letting `m` tend to infinity and then removing the spectral cut
kills every gap trace.  The exact gap criterion proves the claim.

## 4. Fixed full-fundamental-group and locally trivial corollaries

If all `N_x` are isomorphic to one full-fundamental-group factor `N`, the
corner transport and small-corner diameter argument of
`stw22-transport-a-pointed-contraction-through-all-corners` supplies the
uniform corner condition in every finite degree.  The isomorphisms
`N_x->N` are used only to prove an intrinsic metric estimate inside one
fibre; they need not vary continuously in `x`.  Thus isotriviality plus
countable generation suffices, even without local triviality.

For a locally trivial bundle with fibre `N`, its `L^2` Hilbert bundle is
locally trivial with separable fibre.  Choose a finite trivializing cover
and a subordinate partition of unity.  Multiplying a countable constant
orthonormal family in each chart by the square roots of the partition
functions, and extending by zero, gives a countable generating family for
the section Hilbert module.  Transition automorphisms preserve the trace,
the `2`-metric, weighted-copy equations and orthogonality.  No global gauge
or compatibility of the independently transported contractions is needed:
Michael selection, rather than chartwise gluing of those contractions,
constructs the global weighted copies.

---
rg: 2
id: kt-regular-congruence-mask-removes-trace-faithfulness-from-the-commutant-wall
kind: claim
title: A KT regular congruence mask makes every multiplicity leak trace-faithful
artifacts:
  - research/kt-tensor-mask-isometry-and-positive-density-multiplicity-proof.md
distinct_from:
  canonical-kt-steinberg-deleted-line-embeddings-have-scalar-relative-commutants: that constructs the exact regular-character carrier and proves its own negligible-boundary commutants are scalar; this tensors that carrier with an arbitrary multiplicity microstate and proves the carrier cannot constrain the multiplicity wall.
  kt-two-compressor-irrep-flow-has-profinite-stationary-points: that shows scalar irrep weights have common profinite stationary points; this retains the full multiplicity algebra and proves all two-compressor defects survive isometrically.
  strict-compressor-mixed-return-collapses-shared-pauli-sign: that identifies the mixed-return condition needed from a trace-faithful actor microstate; this proves trace-faithfulness itself gives no leverage toward that condition.
  generic-perturbations-destroy-exact-commutant-gap: that constructs low spectral bands after perturbing exact coordinates; this is an exact tensor reduction for arbitrary multiplicity microstates.
---

**ESTABLISHED REDUCTION; IT DOES NOT CONSTRUCT THE REQUIRED LEAK.**

Let

```text
alpha_n:G->U(D_n)
```

be the exact regular-character congruence representations of
`canonical-kt-steinberg-deleted-line-embeddings-have-scalar-relative-commutants`.
Thus `tr(alpha_n(g))->0` for every `g!=1`.  Let

```text
v_n:G->U(k_n)
```

be arbitrary maps which are pointwise asymptotically multiplicative; no trace
condition is imposed.  Define

```text
u_n(g)=alpha_n(g) tensor v_n(g).                         (KTM1)
```

Then:

1. **All actor defects are preserved exactly.**  For every `g,h in G`,

   ```text
   ||u_n(g)u_n(h)-u_n(gh)||_2
    =||v_n(g)v_n(h)-v_n(gh)||_2.                         (KTM2)
   ```

   The same identity holds for every relator word, including the full joint
   relations of the two positive compressors `A,B` generating
   `SL_3(Z)`.

2. **The carrier forces the regular trace.**

   ```text
   tr(u_n(g))=tr(alpha_n(g)) tr(v_n(g))->0,  g!=1.       (KTM3)
   ```

   Hence `u=[u_n]` is a trace-faithful hyperlinear representation of `G`
   for every ultraproduct representation `v=[v_n]`, even if `v` is highly
   nonfaithful.

3. **Multiplicity commutators are preserved exactly.**  The map

   ```text
   j:[x_n] |-> [I_(D_n) tensor x_n]                      (KTM4)
   ```

   is a trace-preserving isometric `*`-embedding and, for every `g in G`,

   ```text
   ||[j(x),u(g)]||_2=||[x,v(g)]||_2.                     (KTM5)
   ```

   In particular, any `Lambda`-central but not `Gamma`-central
   multiplicity operator becomes a trace-faithful KT commutant leak with
   exactly the same norm.  The same is true for a failure of
   `G`-normalization of the `Gamma`-commutant or for the single named
   mixed-return condition.

Consequently the universal KT commutant statement has an exact
trace-removal equivalence:

```text
(CCR for every trace-faithful matrix-ultraproduct representation of G)
iff
(CCR for every matrix-ultraproduct representation of G).               (KTM6)
```

The forward implication is (KTM1)--(KTM5); the reverse implication is
tautological.  The analogous equivalence holds for normalization of
`u(Gamma)'` by `u(G)`.

This is a positive-density multiplicity result.  If a contraction `x_n` has
`Lambda`-commutator defect tending to zero and some fixed
`Gamma`-commutator bounded below by `delta>0`, then `j(x_n)` has the same
defects in dimension `D_n k_n`.  After arbitrary extra padding
`q_n=o(D_n k_n)`, extend it by zero.  The lower commutator is multiplied
only by

```text
sqrt(D_n k_n/(D_n k_n+q_n))=1-o(1),                     (KTM7)
```

so the displayed leak itself is not diluted by negligible padding.

There is an exact physical-mass versus adjoint-rank split.  In
`L^2(M_(D_n k_n))` the multiplicity sector is

```text
C I_(D_n) tensor L^2(M_(k_n)).
```

It contains every unit vector `I tensor x_n` above, but its dimension ratio
inside the full adjoint Hilbert space is

```text
k_n^2/(D_n^2 k_n^2)=D_n^(-2)->0.                        (KTM8)
```

Thus the leak has full physical `2`-mass while occupying a vanishing-density
adjoint sector.  Global low-band rank or normalized superoperator-trace
estimates cannot see it; a pointed bounded-vector estimate is indispensable.

**Meaning.**  Repeating the irreducible Steinberg carrier with a trivial
multiplicity action gives a large matrix commutant which the actor fixes.
Allowing a multiplicity cocycle does not make the carrier rigidify it:
the carrier cancels from every two-compressor coherence equation, while its
regular character masks every multiplicity trace.  Thus canonical actor
moments, congruence provenance, and trace-faithfulness cannot kill a
positive-density fiber cocycle.

What remains is exactly the bare source-specific problem: construct a
matrix-ultraproduct representation `v` of the KT actor with a compressor
commutant leak, or prove none exists.  Formula (KTM6) sharpens the target but
does not decide it.  The global nonhyperlinear-group route remains **OPEN**.

DERIVATION
kt-tensor-mask-isometry-and-positive-density-multiplicity-proof

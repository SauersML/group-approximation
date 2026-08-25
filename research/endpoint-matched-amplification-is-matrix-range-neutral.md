---
rg: 2
id: endpoint-matched-amplification-is-matrix-range-neutral
kind: claim
title: Matched finite-representation amplification preserves every lattice matrix-range gap despite full endpoint transport
invalidates:
  - sl3-central-dual-via-canonical-full-endpoint-amplification
artifacts:
  - research/endpoint-matched-amplification-proof.md
distinct_from:
  letter-central-matrix-range-separation-is-morita-neutral: that splits the commutant of one finite-spectrum stable letter into multiplicity blocks; this tensors the lattice coordinates and their dual coefficients by the same arbitrary finite-dimensional lattice representation and proves an exact matrix-range support identity.
  two-conjugate-letter-overlap-data-is-morita-neutral: that puts the two conjugate letters and their common overlap actor on a spectator tensor factor; this permits an actor representation of the entire S-arithmetic base, including every transported endpoint generator outside the overlap.
  residual-finite-tensor-camouflages-iwahori-transfer-failures: that regularizes endpoint characters while preserving a pre-existing Iwahori transfer failure; this proves the complete-matrix-order identity needed to preserve a ucp matrix-range separator.
---

**ESTABLISHED MATCHED-AMPLIFICATION FIREWALL.**  Let `Lambda` be any
discrete group, let `S` be a finite generating tuple, and put

```text
A=C^*(Lambda),                    u_s in A  (s in S).
```

For a finite-dimensional unitary representation
`v:Lambda->U(r)` and tuples `X=(X_s)`, `B=(B_s)` in `M_m`, define

```text
X~_s=v(s) tensor X_s,             B~_s=v(s) tensor B_s.          (FER1)
```

Then the matrix-range support function and separation gap are unchanged:

```text
h_(rm)(B~)=h_m(B),
Delta_(rm)(B~;X~)=Delta_m(B;X).                                (FER2)
```

The identity is exact, uses normalized traces, and preserves the summed
normalized Hilbert--Schmidt norm and coordinate operator-norm bounds of the
separator.  The upper bound in `(FER2)` is not an informal tensor-factor
argument: tensor a candidate ucp map with the contragredient representation
and compress by the normalized maximally entangled vector.  This produces
one ucp map whose generator values are precisely the twisted partial traces
appearing in the support functional.  The reverse inequality comes from
the group comultiplication.

Now take

```text
Lambda=SL_3(Z),       Gamma=SL_3(Z[1/p]).
```

If `v` extends to a finite-dimensional representation of `Gamma`, then the
amplified base assignment carries the **entire** S-arithmetic endpoint actor:

```text
v(h lambda h^(-1))=v(h)v(lambda)v(h)^*                         (FER3)
```

for every named lattice generator, including those outside
`Lambda cap h^(-1)Lambda h`.  Tensoring an approximate HNN assignment by
`v` on the base coordinates and by the identity on the stable letter leaves
every presentation defect unchanged, while `(FER2)` preserves its central
dual gap.

Residual finiteness of `Gamma` sharpens the scope.  On any prescribed finite
window of nonidentity **base-group** words, choose a finite quotient which
retains the window and take its left regular representation.  Matched
amplification then makes the whole base window exactly canonical and installs
all full-endpoint transport identities, without changing the matrix-range
gap.  Hence neither a finite endpoint actor, canonical base moments, nor
their tensor combination can prove
`sl3-hnn-central-dual-gap-vanishes`.

This does not refute the central-dual claim.  The amplification does not
regularize reduced words whose image in `Gamma` is trivial but whose Britton
word in the centralizer HNN extension is nontrivial: finite-quotient
co-density makes the stable letter centralize the whole finite base image.
Thus the exact surviving datum is now sharper than “full endpoint
transport.”  A positive proof must couple the separator to the **mixed
stable-letter/base canonical moments** (equivalently, the quasiregular
stable-letter orbit) in a way which cannot be separated into a finite base
actor and a multiplicity factor.

DERIVATION
endpoint-matched-amplification-proof

---
rg: 2
id: toeplitz-parity-negative-corner-has-trivial-scalar-kernel
kind: claim
title: The Toeplitz parity negative corner has trivial old scalar kernel
artifacts:
  - research/toeplitz-parity-scalar-kernel-proof.md
distinct_from:
  character-diracization-limit: that identifies the quotient selected by tensor powers for an arbitrary character; this proves that the concrete Toeplitz parity relations make that quotient equal to the whole old group.
  property-t-free-spectator-erases-old-commutant-overlap: that gives arbitrary spectator traces; this excludes every nontrivial scalar-kernel spectator on the actual negative parity corner.
---

**ESTABLISHED PROPERTY-`(T)`-FREE TRACE AUTHENTICATION.**

Use the notation of `toeplitz-parity-compressor-candidate`:

```text
Lambda=Gamma x C_2,       Gamma=EL_4(T),
b=(1,1) in Lambda,        alpha(b)=c,
```

where `c` is the nontrivial finitary head swap in
`L=GL_fin(N x {1,2,3,4},F_2)`.

Let `pi:H_T->U(M)` be a homomorphism into a tracial matrix ultraproduct,
restricted to a nonzero corner on which

```text
pi(J)=-1.
```

Let

```text
tau(g)=tr(pi(g)),                  g in Lambda,
K_tau={g in Lambda:|tau(g)|=1}.
```

Then

```text
K_tau={1}.                                               (TPS1)
```

DERIVATION
toeplitz-parity-scalar-kernel-proof

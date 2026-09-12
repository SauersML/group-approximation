---
rg: 2
id: canonical-packet-traces-do-not-place-old-commutant-density
kind: claim
title: Canonical old-group and packet traces still allow complete commutant-density dilution
distinct_from:
  packet-kazhdan-commutant-placement-decouples: that gives one tensor-product exact representation; this gives a canonical-trace microstate sequence and computes both the local Schur Reynolds density and the vanishing old low spectrum.
  finite-normalizer-covariance-density-no-go: that permits nontrivial finite automorphism covariance and uses semidirect regular quotients; this isolates what scalar canonical trace and all packet-internal Schur identities can prove before any genuine coefficient covariance is added.
  canonical-marked-corner-kazhdan-density-vanishes: that proves old low-density vanishing in canonical microstates of a marked ambient group; this supplies an explicit canonical product model where positive packet mass coexists with that vanishing.
---

**ESTABLISHED.**  Let `Lambda` be an infinite residually finite property-`(T)`
group with finite quotients `Q_n` whose kernels have trivial intersection,
and let `B` be any fixed finite Schur packet.  On

```text
H_n=ell^2(Q_n) tensor ell^2(B)                         (CPT1)
```

represent `Lambda x B` by the tensor product of the two left-regular
representations.  These exact representations converge to the canonical
trace of `Lambda x B`: a nonidentity packet word has zero `B`-regular trace,
and every fixed nonidentity old-group word survives in `Q_n` for all large
`n` and then has zero `Q_n`-regular trace.

Every nonzero packet projection `z in C[B]` nevertheless has its fixed
canonical Hilbert mass

```text
tr_Hn(z)=tr_B(z)>0.                                    (CPT2)
```

For fixed subgroups `A<B` of the packet, the adjoint Reynolds difference
has constant normalized density

```text
rank(R_A-R_B)/dim(H_n)^2
 =rank(R_A^B-R_B^B)/|B|^2>0.                           (CPT3)
```

In contrast,

```text
dim End_Lambda(H_n)/dim(H_n)^2=1/|Q_n| ->0.            (CPT4)
```

For an adjoint Laplacian cutoff below the Kazhdan gap, its low-spectral
space is exactly this commutant, so `(CPT4)` is also the old low-commutator
density.

Consequently canonical scalar moments of the old group, canonical scalar
moments of the full packet, fixed positive forbidden carrier mass, and all
packet-internal Schur Reynolds identities do **not** imply `(PCD1)`.  The
missing cell in `parity-compressor-old-commutant-has-positive-density` must
visibly fail on `(CPT1)` by coupling the packet coefficient to a genuinely
nontrivial Toeplitz old-group word.  Canonical trace by itself is not that
coupling.

This does not refute the open claim, which explicitly asks for such an
additional coefficient-covariance cell.  It rules out a direct proof from
canonical trace and Schur identities alone.

The same dilution applies to the actual Toeplitz old group without assuming
residual finiteness, conditionally on the microstates whose exclusion is the
goal.  If `phi_n` is any canonical microstate sequence of an infinite
property-`(T)` group `Lambda`, replace it by

```text
phi_n tensor lambda_B.                                  (CPT5)
```

This is canonical for `Lambda x B`, has the same fixed packet masses and
Reynolds densities, and its old adjoint Laplacian is the Laplacian for
`phi_n` tensored with the identity on `End(ell^2(B))`.  Normalization cancels
that fixed multiplicity.  Canonical commutant-density vanishing therefore
makes its old low-spectral density tend to zero.  Thus even under
hypothetical canonical Toeplitz microstates, the local packet data stay
completely decoupled until an added coefficient relation rules out `(CPT5)`.

---
rg: 2
id: uniformly-discrete-block-monomial-images-are-sofic
kind: claim
title: Uniformly HS-discrete finite-label block-monomial tracial images are sofic
invalidates:
  - leavitt-hyperlinear-nonsofic-via-fold-mf-trace
distinct_from:
  signed-monomial-tracial-images-are-sofic: that treats scalar labels in the fixed group `{+1,-1}`; this permits varying finite block groups and varying block dimensions under exactly the uniform normalized-character gap needed by the proof.
  block-monomial-coordinate-collapse: that permits arbitrary unitary blocks but uses a faithfully represented coarse lamp algebra to recover the Kun--Thom coordinate action; this has no lamp algebra and instead uses uniform metric discreteness of the finite block labels to recover the whole GNS group image.
---

**ESTABLISHED BLOCK-MONOMIAL SOFICITY FENCE.** For each `n`, let `L_n` be
a finite group with a faithful unitary representation

```text
pi_n:L_n -> U(r_n)
```

and let `B_n=L_n wr Sym(I_n)` act block-monomially on
`directSum_(i in I_n) C^(r_n)`.  Assume the block labels are uniformly
HS-discrete:

```text
delta := inf_n inf_(ell!=1)
         (1-Re tr_(r_n)(pi_n(ell))) > 0.                (UDB1)
```

If a countable group `G` has asymptotic homomorphisms

```text
rho_n:G -> B_n
```

in normalized Hilbert--Schmidt norm and `N` is their tracial identity
kernel, then

```text
G/N is sofic.                                           (UDB2)
```

The finite permutation model is the natural action of `B_n` on

```text
I_n times L_n,
(ell_i,sigma)(i,x)=(sigma(i),ell_i x).                  (UDB3)
```

If `h_n(A,B)` is the normalized Hamming distance of the actions `(UDB3)`,
then

```text
min(1,delta) h_n(A,B)
 <= (1/2)||A-B||_2^2
 <= 2 h_n(A,B).                                         (UDB4)
```

Consequently HS multiplicative defects vanish exactly when the associated
Hamming defects vanish, and the two ultraproduct maps have the same identity
kernel.  This proves `(UDB2)`.

The uniform gap is load-bearing.  Without it, a positive density of
nonidentity block labels can approach the identity in their normalized
unitary characters and become invisible in HS while remaining fully visible
in the regular finite action.  The exact necessary escape is isolated in
`nonsofic-block-monomial-images-force-soft-kernel-labels`.

This is a theorem about the GNS **group image** of the block-monomial
coordinates.  It does not rule out extracting a different quotient
representation from an almost-reducing adjoint compression: soficity is not
closed under quotients.  In particular it fences the fold-word
sofic-radical route, not the full IR compression problem.

DERIVATION
block-label-regular-action-metric-comparison-proof

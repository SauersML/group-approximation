---
rg: 2
id: two-whitehead-face-has-haar-mf-character
kind: claim
title: Both complementary partial-inverse Whiteheads retain the full Haar row MF character
artifacts:
  - research/two-whitehead-haar-proof.md
distinct_from:
  first-partial-inverse-whitehead-face-has-haar-mf-character: that treats one `s_0,t_0` Whitehead and a `C_2` actor; this adds the complementary `s_1,t_1` occurrence and computes their joint actor as `S_3`.
  binary-branch-flip-weyl-has-s3-c2-model: that constructs a finite occurrence-label model for a branch-flip packet; this keeps the literal full infinite row module and realizes Haar on it by finite invariant row spaces.
  full-depth-one-leavitt-menu-has-finite-clifford-model: that handles a broader finite occurrence menu through a Clifford model; this gives the exact elementary-matrix semidirect-product normal form for the two shortest partial-inverse Whiteheads.
  binary-leavitt-haar-row-profile-is-not-mf-character-restriction: that asks for an MF character of the whole Steinberg group; this proves that the two complementary partial-inverse faces still do not obstruct such an extension.
---

Let `R=L_(F_2)(1,2)`, let `n>=4`, and let

```text
N=<x_(1j)(a):2<=j<=n, a in R> ~= (R,+)^(n-1).
```

On coordinates `2,3` put

```text
omega_i=x_23(s_i) x_32(t_i) x_23(s_i),       i=0,1.
```

Their elementary images have active blocks

```text
W_0=[[q,s_0],[t_0,0]],        W_1=[[p,s_1],[t_1,0]],
p=s_0t_0,                     q=s_1t_1.
```

Both are involutions, and

```text
C=W_1W_0=[[s_1t_0,s_0],[t_1,0]]             satisfies C^3=1.  (CWH1)
```

The order of `C` is exactly three, so `<W_0,W_1>~=S_3`.  This finite actor
normalizes the elementary image of `N`, and

```text
<bar(N),bar(omega_0),bar(omega_1)>
   ~= (R,+)^(n-1) semidirect S_3.                         (CWH2)
```

The group in `(CWH2)` is locally finite.  Its regular character pulls back
to an MF character of `<N,omega_0,omega_1>` whose restriction to the full
row is Haar.  It retains `z=x_13(q)` with trace zero and operator-norm
distance two from the identity.

Thus adding both partial inverses, both reverse idempotents, the crossed-zero
relations, and their first complementary opposite-root interaction still
does not exclude the Haar row profile.  Their interaction creates only the
finite `S_3` prefix actor.  A successful obstruction must leave this
locally finite row-by-actor face.  No extension of the constructed character
to the whole Steinberg group is asserted.

DERIVATION
two-whitehead-haar-proof

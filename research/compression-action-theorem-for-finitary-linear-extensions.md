---
rg: 2
id: compression-action-theorem-for-finitary-linear-extensions
kind: claim
title: A compressed Kazhdan subgroup with a moved forward point puts the whole finitary linear kernel in the MF radical, with no points adjoined
distinct_from:
  finitary-linear-extension-kazhdan-defect-kills-kernel: that needs two extra points adjoined to X and fixed by V, states only Rad_MF(G) = K under an MF hypothesis on V, and makes no defect or soficity claim; this runs inside the original action, using a finite permutation of the compressor's backward orbit to supply the two fixed points, and proves both inverse-image identities. The earlier claim is the special case of this one at Y = X u {a,b}, so no second route into it is wired here.
  normal-kazhdan-defect-non-mf: that is the analytic criterion consumed here, about a normal Kazhdan subgroup of the very group being killed; this is an action theorem whose finite central witness is normal only in an auxiliary subgroup H, with the conclusion reached by ambient normal closure.
  affine-perfect-lamp-wreath-has-locally-finite-mf-radical: that is one explicit ordinary wreath product with an A_5 lamp, proved through the commuting-conjugate centralizer criterion; this is an action theorem over an arbitrary base action whose kernel is a finitary linear group over F_2, and it consumes only the finite-central Kazhdan criterion.
artifacts:
  - research/artifacts/compression-finitary-linear-action-theorem-2026-09-08.md
---

**ESTABLISHED.** Let a countable `V` act on a countably infinite `X`, and put

```text
K = GL_fin(F_2^(X)),      G = K x| V,      pi : G -> V,
```

with `V` acting by permutation of the displayed basis. Suppose

```text
L <= V has property (T),   uLu^-1 <= L,   x in X^L,   ux not in X^L.  (1)
```

Then every homomorphism from `G` to an MF group kills `K`, and

```text
Rad_MF(G) = pi^-1(Rad_MF(V)),     D_G(L) = pi^-1(D_V(L)).            (2)
```

So `G` is not MF, and if `V` is residually finite both groups in (2)
equal `K`. Equivalently: MF-ness of this linear extension would force
every compressor of every Kazhdan subgroup to preserve its fixed-point
set.

**No points are adjoined to `X`.** With `x_i = u^i x`, the backward
orbit `x_0, x_(-1), x_(-2), ...` is `L`-fixed and pairwise distinct,
so the finitary permutation
`p = (x_(-1) x_(-2))(x_(-3) x_(-4))` centralizes `L`, and `v = up`
still compresses `L` while fixing `a = x_(-1)` and `b = x_(-3)` and
sending `x` to `ux`. That is the entire difference from the earlier
adjoined-point statement, and it is what makes canonical objects such as
`GL_fin(F_2^(V/L)) x| Q` accessible instead of enlargements of them.

The witness is the involution `z = T_(ab)`, central in
`H = <L, v, T_(xb), T_(a,ux)>` and lying in `D_H(L)`; the criterion is
applied inside `H` and the conclusion propagates by ambient normal
closure, since transvections generate `K`.

DERIVATION
backward-orbit-compressor-modification-proof

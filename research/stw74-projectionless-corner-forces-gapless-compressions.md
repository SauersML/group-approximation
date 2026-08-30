---
rg: 2
id: stw74-projectionless-corner-forces-gapless-compressions
kind: claim
title: A stabilized projection over a projectionless corner has only gapless scalar compressions
---

Let `D` be a projectionless C\*-algebra and let `0!=p` be a projection in
`M_n(D)`.  For every scalar vector `xi` in `C^n`, set

```text
a_xi = (xi* tensor 1) p (xi tensor 1) in D_+.
```

Whenever `a_xi!=0`, zero is an accumulation point of the nonzero spectrum of
`a_xi`.  Equivalently, there is no `epsilon>0` for which

```text
sigma(a_xi) subset {0} union [epsilon,infinity).
```

This remains true when `p` is full and properly infinite.  Therefore proper
infiniteness of the finite projective module `pD^n` does not by itself make a
coordinate polar decomposition available; a proof of the LXXIV hinge must
create a spectral gap rather than merely a nonzero coordinate compression.

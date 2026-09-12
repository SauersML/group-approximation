---
rg: 2
id: waldhausen-hnn-vertex-higher-whitehead-injectivity
kind: claim
title: A Whitehead-contractible HNN edge injects every connective Whitehead group
distinct_from:
  waldhausen-hnn-vertex-whitehead-injectivity: that assumes only ordinary Wh(L)=0 and concludes injectivity only on ordinary Whitehead groups; this assumes the whole edge Whitehead space is contractible and concludes injectivity on every homotopy group.
---

Let

```text
H = HNN(V; L, alpha, beta)
```

be an HNN extension with injective edge maps. If Waldhausen's whole
Whitehead space `Wh_Z(L)` is contractible, then for every `i>=0` the
vertex inclusion induces an injection

```text
Wh_i(V)=pi_i Wh_Z(V) -> pi_i Wh_Z(H)=Wh_i(H).
```

No regular-coherence hypothesis on `L` is imposed; contractibility of its
Whitehead space is the explicit hypothesis.

**ESTABLISHED 2026-08-30** by
[[waldhausen-hnn-vertex-higher-whitehead-injectivity-proof]].

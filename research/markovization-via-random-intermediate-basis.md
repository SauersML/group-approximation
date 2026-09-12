---
rg: 2
id: markovization-via-random-intermediate-basis
kind: route
title: Dead - randomize the intermediate basis so dephased transitions compose on average
target: regular-character-markovization
requires: []
---

**Dead in the proposed form.** Dephase each leg in a fresh Haar-random
intermediate basis and hope the averaged Markov composition equals the
transition of the product. `haar-random-basis-depolarization` computes the
average exactly:

```text
E[P_C P_A] = (J+P_D)/(d+1),
```

not `P_D`. The method retains only `1/(d+1)` of the coherent transition and
injects a depolarized background. Coupled higher-order latent randomness is a
different route and is not invalidated here.

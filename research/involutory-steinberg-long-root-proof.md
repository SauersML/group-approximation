---
rg: 2
id: involutory-steinberg-long-root-proof
kind: route
title: Conjugation by an involution reverses its commutator
target: involutory-steinberg-simple-root-forces-long-root-involution
requires: []
---

First compare conjugation of `c` by `p` with `c^*`. Expanding the words,

```text
p c p^*=p^2 q p^* q^* p^*,
c^*=q p q^* p^*.
```

Replace the leading `p^2` by `I`, at cost `sigma`, and then the remaining
first `p^*` by `p`, again at cost
`||p^*-p||_2=||p^2-I||_2=sigma`. Hence

```text
||p c p^*-c^*||_2<=2 sigma.                              (ISL1)
```

The approximation of `a` by `c` and the centrality defect give

```text
||p c p^*-c||_2
 <=||p(c-a)p^*||_2+||p a p^*-a||_2+||a-c||_2
 <=2 gamma+kappa.                                       (ISL2)
```

Combining `(ISL1)--(ISL2)` yields

```text
||c-c^*||_2<=2 gamma+kappa+2 sigma.                      (ISL3)
```

Since `c` is unitary, `||c^2-I||_2=||c-c^*||_2`. Finally,

```text
||a^2-I||_2
 <=||a^2-c^2||_2+||c^2-I||_2
 <=2||a-c||_2+||c^2-I||_2,
```

which together with `(ISL3)` is `(ISR2)`.


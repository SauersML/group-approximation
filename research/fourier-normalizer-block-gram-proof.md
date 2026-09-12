---
rg: 2
id: fourier-normalizer-block-gram-proof
kind: route
title: Fourier-expand each normalizer block and apply Parseval
target: fourier-normalizer-words-control-block-gram-leakage
requires: []
---

For `i!=k`, direct block multiplication gives

```text
E_i [P D^r P^*,D]_add E_k
 =(zeta^k-zeta^i) sum_j zeta^(rj)P_(ij)P_(kj)^*.
```

At Fourier mode `r=0`, the inner sum is

```text
sum_j P_(ij)P_(kj)^*=E_i PP^*E_k=0.
```

Parseval over `Z/m`, followed by orthogonality of the `(i,k)` matrix blocks,
therefore gives `(FNG1)`.  For `i!=k`,
`|zeta^k-zeta^i|^2>=4 sin^2(pi/m)`, proving `(FNG2)`.

If `X=P D^r P^*`, then

```text
XDX^*D^*-I=(XD-DX)X^*D^*,
```

so unitary invariance of the normalized Hilbert--Schmidt norm identifies
each additive commutator norm with the displayed ordinary group-word defect.

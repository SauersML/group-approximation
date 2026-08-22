---
rg: 2
id: rstar-hadamard-relative-c4-proof
kind: route
title: Track one Hadamard off-diagonal term through two parity marginals and two equality segments
target: rstar-hadamard-escape-violates-relative-c4
requires:
  - one-binary-marginal-block-escape
  - term-pairing-does-not-bypass-signed-hecke-holonomy
  - overlap-subdivision-preserves-coherent-piece-obstruction
---

On the escaped two-plane, the Hadamard conjugates of `e_r,e_s` are

```text
f_r=(e_r+e_s+E_rs+E_sr)/2,
f_s=(e_r+e_s-E_rs-E_sr)/2.
```

Conjugating by `W=sum_i h_i e_i` gives `(RHC2)`.  Summing assignment
projections with the sign of coordinate `y` gives `(RHC4)`.  Because the
rotation is confined to this one plane, no third assignment projection has
an `(r,s)` coefficient.

Two points in one parity coset have even Hamming distance.  Distinctness and
agreement in the preserved coordinate therefore give two other differing
coordinates, proving whole-term recurrence on the original endpoint.

In a length-at-least-two equality chain, the paired intermediate term is
literally the same group-ring term in its left and right segment equations.
It is therefore also a piece.  With disjoint vertex alphabets the endpoint
pairing boundary is the concatenation of those two recurrent term words,
up to inversion.  It is a product of two pieces, contradicting `C(4)`.

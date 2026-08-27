---
rg: 2
id: random-whole-face-pinchings-contract-transverse-l2
kind: claim
title: Random whole-face pinchings contract exact transverse L2 energy at the Hamiltonian-gap rate
distinct_from:
  random-code-anchor-pinchings-contract-exact-transverse-energy: that uses random coordinate anchors and the code distance; this uses arbitrary whole-face conditional expectations and the established adjoint face-Hamiltonian gap.
  gapped-face-pinchings-give-same-hilbert-code-pvm-rounding: that projects directly to the common commutant and rounds coordinates; this gives an explicit randomized implementation and exact finite-step contraction.
  random-anchor-contraction-does-not-yet-enter-the-diffuse-basin: that fences nonlinear coordinate-anchor iteration; this is the exact linear whole-face theorem before re-reflection.
---

Let `Phi_c` be the `L_2`-orthogonal conditional expectation onto the
commutant of an exact bounded face PVM, put

```text
H=(1/|C|)sum_c(I-Phi_c),
K=intersection_c ran(Phi_c),
E_K=the orthogonal projection onto K,
```

and assume the uniform gap

```text
<X,HX> >= gamma||X-E_KX||_2^2.                           (RWF1)
```

For a uniform random face `c` and every `X in L_2(M)`, one has

```text
E_c ||Phi_cX-E_KX||_2^2
 <= (1-gamma)||X-E_KX||_2^2.                             (RWF2)
```

For independent uniform faces `c_1,...,c_k`,

```text
E ||Phi_(c_k)...Phi_(c_1)X-E_KX||_2^2
 <= (1-gamma)^k||X-E_KX||_2^2.                           (RWF3)
```

The estimates are dimension-free, completely amplified, and include all
multiplicity-space directions.  Thus the established repeated-LDPC adjoint
face gap gives an optimal stochastic **linear** contraction; no coloring or
deterministic ordering is needed.

This theorem assumes one exact family of face PVMs acting on the same
Hilbert space.  It does not exactify repeated approximate occurrences, and
it does not say that taking spectral signs after every pinching preserves
the contraction.

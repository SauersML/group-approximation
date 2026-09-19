---
rg: 2
id: code-distance-full-pinching-proof
kind: route
title: Decode the commuting reference atomwise, then apply de la Salle with the code adjoint gap
target: code-distance-upgrades-pair-energy-to-full-pinching
requires:
  - de-la-salle-full-pinching-rounds-one-reflection
  - joint-pinching-costs-linear-generator-gap
---

Let `(q_x)_(x in F_2^L)` be the joint PVM of `(S_i)`, allowing zero atoms.
On atom `x`, a violated parity row contributes `4` to the squared defect.
Thus `(CDP1)` and `(CDP2)` imply

```text
E_(x~tau(q_x)) dist(x,C)/L <= E_par/(4 kappa).            (CPF1)
```

Choose a nearest codeword `c(x)` and set

```text
S'_i=sum_x (-1)^(c(x)_i)q_x.
```

These are commuting code reflections, and

```text
(1/L)sum_i||S_i-S'_i||_2^2
 =4 E_x dist(x,C)/L <= E_par/kappa,                       (CPF2)
```

which proves `(CDP4)`.  Since

```text
||[R,S'_i]||_2
 <= ||[R,S_i]||_2+2||S_i-S'_i||_2,
```

averaging the squared inequality gives

```text
D(R,S') <=2D(R,S)+8E_par/kappa.                           (CPF3)
```

For the code PVM `(q'_c)` obtained by merging equal decoded atoms, the
matrix block `q'_c R q'_(c')` is an adjoint eigenvector with character
`c+c'`.  If `c!=c'`, code distance gives `|c+c'|>=delta L`.  Formula `(JPG4)`
therefore proves `(CDP6)`.  The de la Salle specialization gives

```text
||R-R'||_2^2 <=20||R-E_Q(R)||_2^2
              <=(5/delta)D(R,S').
```

Insert `(CPF3)` to obtain `(CDP5)`.


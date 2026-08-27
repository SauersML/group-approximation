---
rg: 2
id: de-la-salle-full-pinching-rounds-one-reflection
kind: claim
title: Full joint-PVM pinching rounds one reflection with a dimension-free same-algebra constant
distinct_from:
  gapped-face-pinchings-give-same-hilbert-code-pvm-rounding: that uses a uniform face-Hamiltonian gap to project every coordinate to a common commutant; this is the exact one-PVM terminal rounding theorem and identifies its full-pinching input.
  sequential-pinchings-have-sharp-linear-disturbance-loss: that lower-bounds disturbance accumulated by sequential coordinate measurements; this computes the Fourier spectral gap between pairwise generator energy and the one-step joint-pinching hypothesis.
  de-la-salle-pauli-game-starts-after-the-same-pvm-gate: that audits a Pauli-game theorem assuming primitive large PVMs; this imports the cardinality-free orthogonalization theorem for two arbitrary PVMs.
---

ESTABLISHED.  Let `(q_x)_(x in X)` be a finite PVM in a finite tracial von
Neumann algebra `(M,tau)`, let `R=R^*=R^(-1)`, and let

```text
E_Q(T)=sum_x q_x T q_x,
Delta_Q(R)=||R-E_Q(R)||_2^2.                              (DFP1)
```

There is a reflection `R'` in `M`, commuting with every `q_x`, such that

```text
||R-R'||_2^2 <= 20 Delta_Q(R).                            (DFP2)
```

The number of atoms, the matrix dimension, and the ranks of the atoms do not
occur in the constant.  This is a direct specialization of Mikael de la
Salle, *Orthogonalization of Positive Operator Valued Measures*,
arXiv:2103.14126v2, Theorem 1.4 (Theorem 4 in the published version).

Indeed put `p_+=(1+R)/2`, `p_-=(1-R)/2`.  Tracial orthogonality of the
pinching gives the exact identity

```text
sum_(sigma in {+,-}) sum_x ||[p_sigma,q_x]||_2^2
   = ||R-E_Q(R)||_2^2.                                   (DFP3)
```

To check it, for `p=p_+` one has

```text
sum_x ||[p,q_x]||_2^2=2||p-E_Q(p)||_2^2;
```

the `p_-` summand is identical and `R-E_Q(R)=2(p-E_Q(p))`.
De la Salle's theorem supplies a PVM `(p'_+,p'_-)` commuting with `(q_x)`
and

```text
sum_sigma ||p_sigma-p'_sigma||_2^2 <=10 Delta_Q(R).
```

Taking `R'=p'_+-p'_-` gives `(DFP2)`.

This theorem is exactly downstream of the current balanced-overlay gate.
It requires one already exact joint PVM and controls the new reflection by
its disturbance under the **whole** joint pinching.  It does not infer that
disturbance from average commutators with a list of generators; the sharp
gap between those inputs is recorded in
`joint-pinching-costs-linear-generator-gap`.


---
rg: 2
id: two-code-character-cut-recenters-to-one-coordinate
kind: claim
title: A two-code-character cut recenters to one coordinate spectral projection
distinct_from:
  common-character-rotation-is-flat-for-involution-jacobian: that shows a fixed old cut sees a simultaneous rotation only quadratically; this moves the cut along the exact gauge orbit and makes its new boundary a complete-pair commutator row
  code-distance-upgrades-pair-energy-to-full-pinching: that starts from a whole commuting reference PVM; this treats one two-leaf character cut before a global PVM exists
---

Let `Q_1,...,Q_L` be reflections in a finite tracial matrix algebra and let
`p` be a projection, `q=1-p`.  Put

```text
X_i=pQ_ip+qQ_iq,        R_i=sgn(X_i).
```

Assume that the terminal signs on the two leaves are distinct scalar code
characters:

```text
R_i=chi_i p+psi_i q,       chi_i,psi_i in {+1,-1},
chi!=psi.                                                   (TCR1)
```

For every coordinate `k` with `chi_k!=psi_k`, define the exact spectral cut

```text
p_k=(I+chi_k Q_k)/2.                                       (TCR2)
```

Then

```text
||p-p_k||_2^2 <=(1/2)||[p,Q_k]||_2^2,                     (TCR3)

(1/L)sum_i||[p_k,Q_i]||_2^2
 =(1/(4L))sum_i||[Q_k,Q_i]||_2^2.                         (TCR4)
```

If exact positive-distance parity is present, with the row consequence
`(APL7)`, then

```text
(1/L)sum_i||[p_k,Q_i]||_2^2 <=E_com/(4 kappa).            (TCR5)
```

Thus the full common-character rotation from
`common-character-rotation-is-flat-for-involution-jacobian` is pure gauge:
the old fixed cut may have boundary of order `theta^2`, but the recentered
spectral cut has zero boundary on the exact rotated representation and
`O(E_com)` boundary in general.  The estimate is independent of character
multiplicity, matrix dimension, code length, and the angle in the
two-subspace CS decomposition.

## Attempts

Trying to charge the old boundary to contraction involution residual is
impossible because the rotated two-character example has quadratic boundary
and quartic residual.  Replacing the cut, rather than repairing its old
blocks, is essential.  The theorem treats one binary cut only; applying it
sequentially to a large character menu can still lose the character decision
tree depth.

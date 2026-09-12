---
rg: 2
id: role-packed-bcs-gap-proof
kind: route
title: Factor the spin packet trace and specialize the adaptive ring compiler to one source
target: role-packed-bcs-gap-is-one-idempotent
requires:
  - non-ce-bcs-has-robust-approximate-energy-gap
  - role-multiplexing-is-minimax-max-selection
  - finite-adaptive-selected-atom-ring-tree
---

On the negative central sector, finite Stone--von Neumann gives

```text
H=C^m tensor H_0,
```

with the role packet acting on the first factor.  Every operator commuting
with the full packet, including the corrected shared BCS tuple and the
reducing carrier, lies in `I_m tensor B(H_0)`.  The diagonal Pauli atoms are
rank-one projections on `C^m`.  Therefore their traces factor and give
`(RBG3)`.  The robust BCS estimate `(RBG1)` gives `(RBG4)`.  Fixed finite
packet exactification and averaging into its commutant contribute only a
dimension-independent `O(sqrt(E))` loss.

Orthogonality of the role atoms proves directly that `B_f` is a projection.
In the perfect BCS trace all `P_i` vanish, proving `(RBG5)` and exact
completeness.

Finally specialize the equations `(FAR1)--(FAR2)` to the one fixed
idempotent `B_f`: set `a_n=q_nB_f`, adjoin one arrow with range `d_n`
orthogonal to `q_n`, and set `q_(n+1)=q_n+d_n`.  Murray--von Neumann
equivalence and orthogonal trace additivity give `(RBG7)`.  The stated depth
then exceeds the marked-sector capacity exactly as in the finite adaptive
compiler.

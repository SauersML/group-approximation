---
rg: 2
id: weyl-derivative-reset-preserves-schur-spin-scale
kind: claim
title: An invertible selector derivative gives a transverse Weyl reset at the unchanged Schur spin scale
distinct_from:
  selector-free-spin-reset-leaves-contexts-independent: that amalgamates only over a common spin subgroup and leaves the two selector charts unrelated; this constructs a transverse selector inside one finite overgroup and forces its two signs to balance.
  translation-symmetrized-schur-child-reset: that translates the full Boolean cube and leaves only a scalar stationary ray; this translates one selector bit and uses the orbit-product derivative as a nondegenerate return packet.
  flip-endpoints-cancel-schur-current: that restricts to a smaller endpoint on which the two child types fuse; the derivative packet here has exactly the baseline spin dimension, so total baseline multiplicity is preserved rather than divided by a smaller packet size.
---

Let

```text
U(x)=C+sum_(j=1)^k x_j A_j in M_N(F_2)                  (WDR1)
```

be an everywhere-invertible affine pencil and fix `i` with `A_i` invertible.
Let `A=K(U)` be its class-two Schur baseline packet, with central involutions
`J,z_1,...,z_k` and commuting row/column generators `p_r,q_s`.

Take two copies `A^(0),A^(1)` sharing the same center, make noncentral
generators in different copies commute, and put the shifted pencil
`U(x+a e_i)` in copy `a`.  The formulas

```text
tau_i(z_i)=J z_i,
tau_i(z_j)=z_j                    (j!=i),
tau_i(p_r^(a))=p_r^(a+1),
tau_i(q_s^(a))=q_s^(a+1)                           (WDR2)
```

define an involutive automorphism.  Let `s_i` implement it in the finite
semidirect product `R_i`.

Define orbit-product words

```text
P_r=p_r^(0)p_r^(1),             Q_s=q_s^(0)q_s^(1).     (WDR3)
```

They commute with `s_i`, every `z_j`, and satisfy

```text
[P_r,Q_s]=J^((A_i)_(rs)).                               (WDR4)
```

Thus

```text
L_i=<J,P_r,Q_s>
```

is the nondegenerate fixed-sign packet `K(A_i)`.  Its unique `J=-1` spin
simple has dimension `2^N`, exactly the dimension of every selector-sector
spin simple of `A`; no scale is lost.

The subgroup

```text
D_i^new=<J,s_i,z_j : j!=i>                              (WDR5)
```

is elementary abelian and centralizes `L_i`.  It is transverse to the old
selector bit:

```text
s_i z_i s_i^(-1)=Jz_i,
z_i s_i z_i^(-1)=Js_i.                                  (WDR6)
```

Consequently, in every exact finite-dimensional representation with `J=-1`,
conjugation by `z_i` exchanges the two `s_i` eigenspaces while fixing `L_i`
and all unreset selectors.  Conditional on every character of the other
selectors, the two fresh signs have equal multiplicity.

More importantly, on that same conditional carrier,

```text
total multiplicity of the two old A-spin types
 = multiplicity of the L_i spin type.                    (WDR7)
```

Both sides are simply the Hilbert dimension of the carrier divided by
`2^N`.  Thus `(WDR7)` forgets one old selector coordinate while retaining the
integer multiplicity currency at the original Schur baseline scale.

For a fixed packet, flexible finite-group exactification and common-overlap
polar alignment turn `(WDR6)--(WDR7)` into a weighted multiplicity estimate
with loss `C sqrt(E)`, independent of ambient matrix dimension.  The theorem
is local: a finite chain of these cells still has a regular stationary flow,
so it does not by itself supply the global contractive return.

The same construction applies to any nonzero selector direction `v` for
which `A(v)=sum_j v_jA_j` is invertible. Choose a linear selector basis sending
`v` to one coordinate, or equivalently let `s_v` multiply every `z_j` with
`v_j=1` by `J`. The two-copy orbit product then has commutator matrix `A(v)`.
In particular the gauge-share flip `(A_x,B_x)->(JA_x,JB_x)` is admissible for
the invertible-direction compiler.

---
rg: 2
id: stw22-variable-factor-weighted-selection-proof
kind: route
title: Select weighted orthogonal copies inside continuously moving factor fibres
target: stw22-expectation-fields-have-uniform-traces
requires:
  - stw22-tracefree-fibre-gap-ideals-force-trace-continuity
artifacts:
  - research/artifacts/stw22-variable-factor-selection-audit-2026-08-30.md
---

Condition `(CEF)` first gives the bundle structure.  Pointwise operations
preserve bounded `2`-norm continuity, and uniform operator-norm closure is
immediate.  A uniformly `2`-Cauchy bounded net has a pointwise limit in
each von Neumann algebra `N_x`, and that limit is uniformly
`2`-continuous.  Hence `M` is tracially complete.  Evaluation at `x` is
onto: if `z in N_x`, then

```text
s_z(y)=E_y(z)
```

belongs to `M` by `(CEF)` and satisfies `s_z(x)=z`.  Thus the `2`-norm
fibre is the finite factor `N_x`, and

```text
E(a)(x)=tau(a(x))
```

is the canonical central expectation.

## Moving-factor weighted lifting

Fix `m>=1` and `s<1/m`.  For a positive contraction `a in N_x` with
`tau(supp(a))<=s`, let `F_x(a)` be the set of tuples
`(v_1,...,v_m) in N_x^m` satisfying

```text
v_j^*v_j=a,
(v_i v_i^*)(v_j v_j^*)=0       (i!=j).                 (VFS1)
```

These sets are nonempty: the support of `a` has `m` orthogonal equivalent
copies in the finite factor `N_x`, and multiplication of the implementing
partial isometries by `a^(1/2)` gives `(VFS1)`.

We need the following lower-lifting fact.

```text
x_n -> x,   ||a_n-a||_2 -> 0,   tau(supp(a_n))<=s,
v in F_x(a)
  ==> there are v_n in F_(x_n)(a_n) with ||v_n-v||_2 -> 0.   (VFS2)
```

Here tuple norms mean the maximum of the component `2`-norms.  We verify
`(VFS2)` rather than assuming a continuous support field.

Write `v_j=w_j a^(1/2)` using the polar partial isometry.  Choose
`eta>0` outside the point spectrum of `a` and put

```text
q=1_[eta,infinity)(a),       q_n=1_[eta,infinity)(a_n).
```

After an arbitrarily small change of `eta`, spectral perturbation gives
`||q_n-q||_2 -> 0`.  By `(CEF)`, `E_(x_n)(w_jq)->w_jq` in `2`-norm.
Set

```text
y_(j,n)=E_(x_n)(w_jq)q_n in N_(x_n).
```

Then `y_(j,n)^*y_(j,n)->q_n` and the cross-range defects tend to zero in
`L^1`.  Correct them successively.  After the first `j-1` ranges have been
chosen, compress `y_(j,n)` by the complement of those ranges and take its
polar part.  Its initial projection misses a subprojection of `q_n` whose
trace tends to zero; fill that missing subprojection by a partial isometry
into the unused range complement.  The fill has `2`-norm equal to the
square root of the missing trace.  Since `m tau(q_n)<=ms<1`, this procedure
has enough unused range at every step.  It gives partial isometries
`w_(j,n)^hi in N_(x_n)` with common initial projection `q_n`, pairwise
orthogonal ranges, and

```text
w_(j,n)^hi q_n -> w_jq       in ||.||_2.                (VFS3)
```

The compression, polar correction, and fill lose only the `2`-norm of the
displayed multiplicative and orthogonality defects.  Those defects tend to
zero because conditional expectation is contractive and multiplication is
`2`-continuous on the unit ball.

Let `p_n=supp(a_n)` and `r_n=p_n-q_n`.  The strict slack gives

```text
m tau(p_n)<=ms<1.
```

Therefore the complement of the high range projections contains `m`
orthogonal projections equivalent to `r_n`.  Choose the corresponding
partial isometries `w_(j,n)^lo` independently and set

```text
v_(j,n)=(w_(j,n)^hi+w_(j,n)^lo)a_n^(1/2).
```

These tuples satisfy `(VFS1)` exactly.  Their uncontrolled low parts are
harmless because

```text
||(w_(j,n)^lo a_n^(1/2))||_2^2
 =tau(a_n r_n) <= eta.                                  (VFS4)
```

For fixed `eta`, `(VFS3)` and functional calculus control the high parts;
then `eta->0` controls `(VFS4)`.  A diagonal choice proves `(VFS2)`.

## Zero-dimensional selection

Let `Z subset K` be closed and let `a:Z -> R_+` be a bounded
`2`-continuous section with

```text
sup_(z in Z) tau(supp(a(z))) <= s<1/m.                  (VFS5)
```

Regard `F_z(a(z))` as a closed nonempty subset of the common complete
metric ball of `L^2(R)^m`.  Statement `(VFS2)` says exactly that this
set-valued map is lower semicontinuous.

For completeness, zero-dimensional selection is obtained directly by
successive finite clopen refinements.  Choose a summable positive sequence
`epsilon_n`.  Inductively construct a locally constant tuple `f_n` on a
finite clopen partition such that

```text
dist(f_n(z),F_z(a(z)))<epsilon_n             (z in Z).  (VFS5a)
```

On an atom of the `n`-th partition and at a point `z`, choose
`y_z in F_z(a(z))` within `epsilon_n` of the atom's value.  Lower
semicontinuity supplies a neighbourhood on which every fibre set meets the
`epsilon_(n+1)`-ball about `y_z`.  A finite clopen refinement subordinate to
these neighbourhoods, with value `y_z` on each child, gives `(VFS5a)` at
stage `n+1` and

```text
sup_z ||f_(n+1)(z)-f_n(z)||_2<epsilon_n.                (VFS5b)
```

The initial finite clopen partition is obtained by the same argument from a
finite cover, taking `epsilon_0` larger than the diameter of the common unit
ball.  Equations `(VFS5a)--(VFS5b)` make the locally constant maps uniformly
Cauchy in `2`-norm.  Their limit `(v_1,...,v_m)` is continuous, and its
distance to each fibre set is zero.  Closedness of every fibre set gives

```text
v_j(z)^*v_j(z)=a(z),
(v_i(z)v_i(z)^*)(v_j(z)v_j(z)^*)=0.                     (VFS6)
```

Because the limit belongs to `F_z(a(z)) subset N_z^m` pointwise, each
`v_j` is a section in `M`.

## Fibre-gap replication

Fix `x in K`, let `a in K_x` be a positive contraction, and put
`c=(a-epsilon)_+`.  Given `m`, Chebyshev's inequality and
`||a(t)||_2->0` at `x` give a clopen neighbourhood `V` such that

```text
sup_(t in V) tau(supp(c(t))) < 1/(2m).                  (VFS7)
```

Replace `c` by `1_Vc` modulo `J_x` and apply `(VFS5)--(VFS6)` with
`s=1/(2m)`.  Extending the selected sections by zero gives
`v_1,...,v_m in K_x` with common source `c` and orthogonal ranges.  Hence
every bounded positive trace `sigma` on `K_x/J_x` satisfies

```text
m sigma(c)=sigma(sum_j v_jv_j^*) <= ||sigma||.
```

Let first `m` and then `epsilon` tend to their limits.  Every fibre gap is
bounded-trace-free, so the exact fibre-gap criterion gives the trace
formula in the claim.

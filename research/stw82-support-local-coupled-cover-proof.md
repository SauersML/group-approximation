---
rg: 2
id: stw82-support-local-coupled-cover-proof
kind: route
title: Repair support-covering cutdowns and merge their orthogonal bands
target: stw82-support-local-coupled-covers-merge-colours
requires:
  - stw82-quasicentral-cutdowns-repair-to-banded-order-zero
---

We use the uniform stability lemma proved in
`stw82-quasicentral-cutdowns-repair-to-banded-order-zero-proof`: an
approximately order-zero cpc map on a fixed finite-dimensional algebra is
uniformly close to a cpc order-zero map in the same target algebra.

For each `v,k`, define

```text
theta_(v,k)(x)
 =c_(v,k)^(1/2) phi_v(x) c_(v,k)^(1/2).
```

This is a cpc map into the stated hereditary algebra.  If `x,y` are
orthogonal positive contractions, then

```text
theta_(v,k)(x)theta_(v,k)(y)
 =c_(v,k)^(1/2) phi_v(x)
   [c_(v,k),phi_v(y)] c_(v,k)^(1/2),
```

so (L2) makes its order-zero defect uniformly small.  Apply the stability
lemma, with perturbation tolerance below `epsilon/(2d)`, to obtain a cpc
order-zero map `psi_(v,k)` in the same hereditary algebra.

It remains to check that a cover of the order-zero support, rather than a
partition of the multiplier unit, reconstructs the map.  Let `pi_v` be the
supporting homomorphism of `phi_v`, so

```text
phi_v(x)=pi_v(x)h_v=h_v pi_v(x).
```

For every contraction `x in F_v`,

```text
norm((1-s_v)phi_v(x))
 =norm((1-s_v)h_v pi_v(x))
 <=norm((1-s_v)h_v)<delta.                            (R1)
```

Also

```text
theta_(v,k)(x)-c_(v,k)phi_v(x)
 =c_(v,k)^(1/2)[phi_v(x),c_(v,k)^(1/2)].              (R2)
```

Summing (R2), using (R1), and then adding the order-zero repair errors gives

```text
norm(phi_v(x)-sum_k psi_(v,k)(x))
 <=(d+1)delta+d epsilon/(2d).
```

Choose `delta` below the finitely many stability thresholds and below
`epsilon/(2(d+1))`.

Finally, (L3) makes the hereditary algebras belonging to distinct `v` and
the same `k` annihilate one another.  Their repaired maps have orthogonal
ranges.  The fixed-`k` direct sum is therefore cpc order zero, exactly as in
`stw82-coupled-operator-partition-proof`.

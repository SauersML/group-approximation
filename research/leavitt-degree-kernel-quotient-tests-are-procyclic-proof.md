---
rg: 2
id: leavitt-degree-kernel-quotient-tests-are-procyclic-proof
kind: route
title: Kill every perfect Leavitt free factor in finite and solvable targets
target: leavitt-degree-kernel-quotient-tests-are-procyclic
requires:
  - degree-kernel-abelianization-is-infinite-cyclic
  - leavitt-unit-group-has-no-finite-normal-subgroup
  - leavitt-gl-equals-el-and-perfect-unit-group
---

The degree-kernel decomposition is

```text
N_m = (*_(i=0)^(m-1) G_i) * <z>,
G_i=t^iGt^(-i),                     z=t^m.              (LDQ1)
```

Let `phi:N_m->K` have finite target.  Its restriction to each `G_i` is a
homomorphism from `G` to a finite group, hence is trivial by
`leavitt-unit-group-has-no-finite-normal-subgroup` (whose first conclusion is
that `G` has no nontrivial finite quotient).  By the free-product universal
property, `phi` factors through the retraction of `(LDQ1)` onto `<z>=Z`.
This proves the finite statement.  Conversely every finite cyclic quotient of
`<z>` occurs, so the profinite completion is exactly `Zhat`, not merely a
quotient of it.

Now let `K` be solvable, with no finiteness assumption.  The image of a
perfect group under any homomorphism is perfect.  A solvable perfect group is
trivial: iterating the derived series would otherwise leave the image fixed
and never reach `1`.  Since `G` is perfect by
`leavitt-gl-equals-el-and-perfect-unit-group`, `phi(G_i)=1` for every `i`, and
the same free-product argument factors `phi` through `<z>`.

Under the retraction `N_m-><z>`, a word `w` with `deg_t(w)=m` maps to `z`
because `z=t^m`.  Therefore its image generates every cyclic image of `N_m`.

Finally set `L_w=<<w>>_F`.  It lies in `N_m` because `N_m` is normal in `F`
and contains `w`.  The established computation
`N_m^ab=Z`, with `[w]` a generator, gives

```text
(N_m/L_w)^ab=0,
```

so `Q_w=N_m/L_w` is perfect.  If `Q_w` had a nontrivial finite or solvable
quotient, composing with `N_m->Q_w` would give a finite or solvable image of
`N_m` in which `w` is trivial.  But every such image is cyclic and generated
by the image of `w`, hence is trivial.  This proves all assertions.

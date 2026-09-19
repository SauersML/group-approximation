---
rg: 2
id: fournier-facio-compact-monomial-no-go-proof
kind: route
title: Remove compact actor errors with the singular charged diagonal state
target: fournier-facio-compact-monomial-near-witness-impossible
requires:
  - fournier-facio-monomial-near-witness-impossible
---

Let `D=ell^infinity(X)` be the atomic diagonal algebra and let

```text
phi_mu(T)=integral_X <T delta_x,delta_x> dmu(x)          (FCMP1)
```

be the charged diagonal state.  Pure singularity means that every finite
subset of `X` has `mu`-charge zero.  The diagonal coefficient of a compact
operator belongs to `c_0(X)`: for every positive tolerance its superlevel
set is finite.  Integration against `mu` therefore kills that coefficient,
and hence

```text
phi_mu(K)=0                       for every compact K.   (FCMP2)
```

Fix monomial lifts as in `(FCM1)`.  For `T in B(ell^2(X))`, expansion of

```text
pi(g)^* T pi(g)-M_g^* T M_g
```

is a sum of products having a compact factor.  It is compact, so invariance
of `phi_mu` under `Ad(pi(g))` and `(FCMP2)` imply invariance under
`Ad(M_g)`.

Put

```text
d_pi(g,h)=pi(gh)-pi(g)pi(h),
d_M(g,h)=M_(gh)-M_g M_h.
```

Their difference is compact.  Hence

```text
d_pi(g,h)^*d_pi(g,h)-d_M(g,h)^*d_M(g,h)
```

is compact as well.  The charged near-representation identity for `pi` and
`(FCMP2)` give

```text
phi_mu(d_M(g,h)^*d_M(g,h))=0.                           (FCMP3)
```

This is the charged state form of every near-multiplication row for `M`.

It remains only to check that the pointwise essential-freeness formulation
also survives.  If `K` is compact, then for every `epsilon>0` the set

```text
{x in X : ||K delta_x|| >= epsilon}                     (FCMP4)
```

is finite.  Otherwise an infinite orthonormal sequence chosen from `(FCMP4)`
would be weakly null while its image under the compact operator `K` failed
to converge to zero in norm.  Thus `(FCMP4)` has zero `mu`-charge.  Applied
to each `K_g`, this says that `pi(g)delta_x` and `M_g delta_x` are
`mu`-almost everywhere arbitrarily close.  The essential-freeness tests for
`pi` therefore transfer to `M`.

We have produced an essentially free charged monomial near representation
of `G`.  This is excluded by
`fournier-facio-monomial-near-witness-impossible`, proving the target.

---
rg: 2
id: atlas-full-large-finite-escape-has-simple-local-factor-proof
kind: route
title: Use normal generation by A5 and classify compatible vertex kernels
target: atlas-full-large-finite-escape-has-simple-local-factor
requires:
  - atlas-large-k22-has-faithful-a5-completion
  - atlas-q96-c144-cycle-has-faithful-a8-quotient
artifacts:
  - experiments/atlas_a4_full_large_simple_factor_kernels.g
  - research/artifacts/atlas-a4-full-large-simple-factor-kernels.json
---

In `Gamma_box`, the subgroup `L` normally generates.  Indeed, after setting
`r,u,t,s` to one, the relation `(ct)^3=1` together with `c^2=1` kills `c`,
and then `(cz)^2=1` together with `z^3=1` kills `z`.  Since `L~=A5` is
perfect, `Gamma_box` is perfect as well.

Start with a finite faithful-vertex quotient and divide it by a maximal proper
normal subgroup.  The result `S` is nonabelian simple because the source is
perfect.  The intersection of the maximal normal subgroup with `L~=A5` is
normal in `L`.  It cannot be all of `L`, because `L` normally generates;
hence it is trivial and `L` injects.

For `F'=S3(r,u) x S3(z,c)`, the first `S3` lies in the injected `L`.  A
compatible normal kernel is therefore disjoint from it.  The only remaining
proper possibility would kill the order-three element `z`; but `z=1` in
`(zb)^3=1` forces the injected involution `b` to be one.  Hence `F'` injects.

For `J~=S4`, a normal kernel disjoint from the injected point stabilizer
`<t,s>~=S3` can only be the normal Klein four group.  Its marked double
transposition is `c`, already nontrivial in the injected `F'`, so this kernel
is also impossible.  Thus `J` injects.

Finally a kernel in `C=A4 x A4` must be disjoint from both injected overlaps

```text
A=<r,z> ~= C3 x C3,             H=<r,b> ~= A4.
```

The exact normal-subgroup audit leaves orders `[1,4,4]`.  Both order-four
quotients are `C3 x A4`, and the displayed words `(SF-4)` normally generate
the two distinct kernels.  The same verifier independently checks the
compatible normal kernels of `F'` and `J`, obtaining only the identity.  This
proves `(SF-2)` and the divisibility statement.

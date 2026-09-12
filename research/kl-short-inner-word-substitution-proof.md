---
rg: 2
id: kl-short-inner-word-substitution-proof
kind: route
title: Solve the inner equation u(t) = z over the one-relator quotient in z, then push w through the solution
target: kl-substituting-a-short-inner-word-preserves-injectivity
requires:
  - kl-length-at-most-five-equations-are-solvable
---

Put `H = (G * <z>)/<<v>>`. By hypothesis `G -> H` is injective.

**Inner equation.** Consider `e = u(t) z^(-1) in H * <t>`. Its coefficients lie
in `H`: those of `u` through `G -> H`, and `z^(-1)`. Its variable length is
`ell_t(u) <= 5`, and `deg_t(e) = deg_t(u) != 0`. By
`kl-length-at-most-five-equations-are-solvable`, applied with coefficient group
`H`, the map `H -> P = (H * <t>)/<<e>>` is injective. In `P`, `u(t) = z`.

**Pushing `w` through.** Let `phi : G * <t> -> P` be the identity on `G` with
`t -> t`, and let `psi : G * <z> -> P` be the composite `G * <z> -> H -> P`.
The homomorphisms `phi o sigma_u` and `psi` agree on `G`, and on `z`:

```text
phi(sigma_u(z)) = phi(u) = u(t) = z = psi(z)     in P.
```

So `phi o sigma_u = psi`, and `phi(w) = phi(sigma_u(v)) = psi(v) = 1`, because
`v` dies in `H`. Hence `phi` factors through `(G * <t>)/<<w>>`.

**Injectivity.** The composite `G -> (G * <t>)/<<w>> -> P` equals
`G -> H -> P`, a composite of two injections. So `G -> (G * <t>)/<<w>>` is
injective.

The degree formula `deg_t(w) = deg_z(v) deg_t(u)` follows by composing
`sigma_u` with the degree map `G * <t> -> Z`.

---
rg: 2
id: truncated-polynomial-binary-weyl-expander-tower-proof
kind: route
title: Use the top-coefficient Frobenius pairing and relative-T adjoint expansion
target: truncated-polynomial-binary-weyl-expander-tower
requires:
  - elementary-linear-semidir-pair-relative-t
  - relative-t-heisenberg-adjoint-quantum-expansion
---

Represent every member of `R_n` by its unique polynomial of degree below
`n`. The bilinear form `(a,d) |-> ell_n(ad)` is nondegenerate: if the lowest
nonzero coefficient of `a` is at degree `j`, then multiplication by
`u^(n-1-j)` exposes it to `ell_n`. This proves nondegeneracy of `(TPW1)`;
alternation follows from
`omega_n((a,b),(a,b))=ell_n(2ab)=0`.

On the standard basis `(e_x)_(x in R_n)` of `H_n`, set

```text
X_a e_x=e_(x+a),
Z_b e_x=(-1)^(ell_n(bx)) e_x.
```

The `X_a,Z_b` obey the Weyl commutation law determined by `(TPW1)`. Any
operator commuting with all `Z_b` is diagonal, and commuting also with all
translations `X_a` makes that diagonal constant. Thus their projective action
is irreducible. Equivalently, the Weyl operators span `End(H_n)`, whose
dimension is `|R_n|^2`; in particular `dim H_n=|R_n|=2^n`.

For `g in EL_2(R_n)`, determinant one preserves the ring-valued alternating
form

```text
((a,b),(c,d)) |-> ad+bc.
```

It therefore preserves `(TPW1)`. Twisting the irreducible Weyl system by `g`
gives another irreducible system with the same central character, so an
intertwining unitary exists and is unique up to phase. Choosing these
intertwiners yields the projective Clifford--Weil action and hence the
projective affine action in item 3.

For `(TPW2)`, direct calculation gives

```text
omega_(n+1)((ua,b),(uc,d))
 = ell_(n+1)(u(ad+bc))
 = ell_n(ad+bc).
```

Its image has codimension two. The vectors `(1,0)` and `(0,u^n)` pair to
one and pair trivially with every `(ua,b)` having `deg(a),deg(b)<n`.
They are therefore a hyperbolic orthogonal complement. Finite
Stone--von Neumann uniqueness turns orthogonal symplectic sum into tensor
product of spin modules, proving item 4.

Finally, quotienting the fixed relative-Kazhdan pair over `R` gives the
projective representations above at every `n`; their translation subgroup
is projectively irreducible. The relative-T adjoint-expansion theorem supplies
one lazy channel and one gap independent of `n`, proving item 5.


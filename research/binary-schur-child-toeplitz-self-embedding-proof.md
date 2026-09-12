---
rg: 2
id: binary-schur-child-toeplitz-self-embedding-proof
kind: route
title: Use the two-site Toeplitz head as the old relative-Pauli matrix coordinate
target: binary-schur-child-toeplitz-self-embedding
requires:
  - oriented-schur-child-branching-identity
---

For a forbidden selector `x`, write

```text
I_x=M_2(M_D(k)),
C_x=diag(M_D(k),M_D(k)).
```

If `a=[a_rs]`, set

```text
phi_x(a)=[diag(a_rs,a_rs)]_(r,s).
```

After reordering the head and child-sign tensor coordinates this is
`a |->(a,a)`, so it is a unital injection
`I_x->M_2(C_x)`.  Taking the direct sum over forbidden selectors proves
`(BST3)` effectively.

Put `e_i=x^iPy^i`.  From `yx=1` and `P=1-xy` one gets

```text
P^2=P,             Px=0,             yP=0,
e_i e_j=0 (i!=j),  sum_(i<N)e_i=1-x^Ny^N.              (1)
```

For `a,b in I`, these identities give

```text
(x^iay^j)(x^kby^ell)=delta_(j,k)x^i(ab)y^ell.          (2)
```

Consequently the two-site head is `M_2(I)`, its unit is
`P+xPy=1-x^2y^2`, and `hat_phi` is a unital homomorphism from `I` into that
head.  The head and the tail corner `x^2y^2` are orthogonal.  Formula `(BST5)`
is therefore a unital homomorphism on `Bsharp=k(1-P) direct_sum I`.  Its
images of `x,y` satisfy

```text
Sigma(y)Sigma(x)=y^2x^2=1,
1-Sigma(x)Sigma(y)=1-x^2y^2=Sigma(P),                  (3)
```

so the universal property of `(BST4)` extends it to an endomorphism of
`Rsharp`.

A terminating normal-form reduction uses `yx=1`, `xy=1-P`, `ax=0`, and
`ya=0` for `a in I`.  Every word containing `I` reduces to one
`x^iay^j`; the words containing no `I` give the Laurent quotient.  Linear
independence follows from the standard unilateral-shift representation on
`direct_sum_(n>=0)V`, with `V` a faithful `I`-module: `x` shifts forward,
`y` shifts backward, and `a in I` acts as `a` on site zero and as zero on the
other sites.  This proves `(BST7)` and the exact sequence

```text
0 -> M_fin(N,I) -> Rsharp -> k[z,z^-1] -> 0.            (4)
```

On the ideal, `(BST5)` is the block substitution

```text
x^iay^j |-> x^(2i)hat_phi(a)y^(2j),                    (5)
```

which is injective because `phi` is.  On the quotient it is the injective
map `z |->z^2`.  If `Sigma(r)=0`, `(4)` first puts `r` in the ideal and `(5)`
then gives `r=0`.  The quotient also shows that `Sigma` is not surjective.

Finally `(BST8)` follows by telescoping, and the module statement is the
sectorwise identity `(a,a)`: restriction adds the two corrected-child
multiplicities.  The accompanying exact audit exhausts the smallest case
`I=M_2(F_5)`, checks all `5^8` multiplication pairs, checks the induced
matrix-unit substitution, and verifies the binary carrier supports through
depth seven.

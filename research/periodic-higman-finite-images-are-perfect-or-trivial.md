---
rg: 2
id: periodic-higman-finite-images-are-perfect-or-trivial
kind: claim
title: Finite images of the cyclic Higman base are perfect, and trivial when the twist is
distinct_from:
  three-higman-bs-seams-vanish-fourth-is-product-holonomy: that analyses which Higman--Baumslag--Solitar seams vanish in a four-matcher holonomy computation; this is about arbitrary finite quotients of one cyclic four-generator Higman-type system carrying an automorphism.
  periodic-higman-mapping-torus-is-word-hyperbolic: that is the geometric statement about the ascending mapping torus; this is pure finite-group theory about the images of its base and uses no hyperbolicity.
---

**ESTABLISHED.**  Let `rho : G -> Q` be any homomorphism to a finite group,
where `G` contains the cyclic Higman base `F = <x_0,x_1,x_2,x_3>` and an element
`t` with `t x_i t^-1 = [x_i, x_(i-1)]`.  Put

```text
H = rho(F),   h_i = rho(x_i),   alpha = Ad(rho t) restricted to H.
```

Since `t F t^-1 <= F` and `H` is finite, `alpha` is an automorphism of `H`, and

```text
alpha(h_i) = [h_i, h_(i-1)],   H = <h_0,h_1,h_2,h_3>.               (3)
```

**Perfectness.**  `H = <alpha(h_i)> <= [H,H]`, so

```text
H = [H,H].                                                          (4)
```

Every nontrivial finite image of the base is perfect; in particular no
nontrivial solvable finite group occurs.

**Trivial twist forces trivial image.**  If `alpha = 1` then `(3)` reads
`h_i = [h_i, h_(i-1)]`, equivalently

```text
h_(i-1)^-1 h_i h_(i-1) = h_i^2,                                     (5)
```

which are exactly the cyclic Higman relations.  Higman's four-generator group
has no nontrivial finite quotient, hence

```text
alpha = 1  ==>  H = 1.                                              (6)
```

So a finite quotient can retain the base only through a NONTRIVIAL twist, and
the order of that twist is the whole obstruction.  That order is what
`periodic-higman-period-spectrum-criterion` quantifies over.

## Attempts

- Ruling out nontrivial `alpha` by a counting or solvability argument: blocked
  by `(4)`, which only gives perfectness, and perfect finite groups with
  automorphisms of small order are abundant.
- Hoping that odd twist order is impossible: FALSE, refuted explicitly by
  `periodic-higman-spectrum-contains-three`.

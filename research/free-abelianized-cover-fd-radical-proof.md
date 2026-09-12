---
rg: 2
id: free-abelianized-cover-fd-radical-proof
kind: route
title: A Fox derivative in the dummy generator detects the commutator, and the eigenspace permutation factors through the base
target: free-abelianized-cover-has-nontrivial-fd-radical
requires:
  - free-abelianized-cover-is-torsion-free
artifacts:
  - research/artifacts/torsion-free-cover-fd-radical-and-heisenberg-2026-09-08.md
---

The prerequisite supplies the exact sequence

```text
1 -> A -> E -> G -> 1,     A = R/[R,R] free abelian,                  (FA1)
```

for the presentation `F = F(X u {z})` with `q(z) = 1`; adjoining the dummy
generator only enlarges the free group by one basis element and `R` by the
normal closure of `z`, so the prerequisite applies verbatim.

## 1. The detector: nontriviality of the commutator

Define `D : F -> Z[G]`, where `Z[G]` is the free abelian group on `G` with
`G` acting by left translation, by

```text
D(x) = 0   (x in X),      D(z) = 1,
D(uv) = D(u) + q(u) D(v),      D(s^-1) = -q(s)^-1 D(s)  on generators.
```

`D` is well defined on reduced words: deleting an adjacent pair `s s^-1`
changes the value by `q(u)(D(s) + q(s)D(s^-1)) = 0`.  This is the Fox
derivative `d/dz` composed with the linear extension of `q`.

For `r, r' in R` we have `q(r) = 1`, so `D(rr') = D(r) + D(r')`: the
restriction `D|_R` is a homomorphism into an abelian group and therefore
kills `[R,R]`.

Now let `q(f) = g` and compute the commutator `w = f z f^-1 z^-1`, which lies
in `R` because `q(w) = g 1 g^-1 1 = 1`:

```text
D(fz)       = D(f) + g,
D(fzf^-1)   = D(f) + g + q(fz) D(f^-1) = D(f) + g - g g^-1 D(f) = g,
D(w)        = g + q(fzf^-1) D(z^-1)    = g - 1.                        (DET)
```

`Z[G]` is free abelian on `G`, so `g - 1 != 0` exactly when `g != 1`.  Since
`D|_R` kills `[R,R]`, `(DET)` gives `w not in [R,R]`, i.e.

```text
g != 1   ==>   [fbar, zbar] != 1   in E.                              (FDR1)
```

## 2. What an exact finite-dimensional representation sees

Let `rho : E -> U(d)` be a homomorphism.  The unitaries `rho(A)` commute, so
`C^d` splits into their joint eigenspaces

```text
C^d = H_1 (+) ... (+) H_k,     rho(a)|_(H_j) = chi_j(a) I,   chi_j distinct.
```

Finite generation of `A` is not needed: pick a non-scalar element of the
family, split into its eigenspaces (a single unitary diagonalizes by taking an
eigenvector and inducting on the orthogonal complement, which it preserves),
and recurse inside each summand.  Commutativity keeps every summand invariant
and each split lowers a dimension, so the process terminates.

For `e in E` and `a in A`, normality of `A` gives
`rho(a) rho(e) v = rho(e) rho(e^-1 a e) v = chi_j(e^-1 a e) rho(e) v` for
`v in H_j`, so `rho(e) H_j` is again a joint eigenspace, with character
`chi_j( e^-1 (.) e )`.  Thus `E` permutes `H_1, ..., H_k`.  Elements of `A`
act by scalars on each `H_j`, hence fix every index, so the permutation
homomorphism kills `A` and factors through `G`:

```text
G -> Sym(k).                                                          (PERM)
```

## 3. The commutator is finite-dimensionally invisible

Let `g in Res_fin(G)` and `q(f) = g`.  `Sym(k)` is finite, so `(PERM)` sends
`g` to the identity permutation: `rho(fbar)` preserves each `H_j`.  Because
`q(z) = 1` we have `z in R`, so `zbar in A` and `rho(zbar)` is the scalar
`chi_j(zbar)` on `H_j`.  A scalar commutes with any operator preserving the
space it is scalar on, so on every `H_j`

```text
rho(fbar) rho(zbar) = rho(zbar) rho(fbar),
```

and since the `H_j` span, `rho([fbar,zbar]) = I`.  This holds for every `rho`,
which is `(FDR2)`.

## 4. Conclusion

If `G` is not residually finite, choose `g != 1` in `Res_fin(G)` and any
`f` with `q(f) = g`.  Then `(FDR1)` makes `[fbar,zbar]` a nontrivial element
of `E` and `(FDR2)` puts it in `Rad_fd(E)`, so `Rad_fd(E) != 1`, which is
`(FDR3)`.  A non-MF `G` is not residually finite, since residually finite
groups are MF (`mf-positive-controls`), so the hypothesis is satisfied by
every input the transfer question is about.

Note the argument produces the same conclusion for `Res_fin(E)`, because a
finite quotient of `E` has a faithful finite-dimensional unitary
representation; `Rad_fd <= Res_fin` makes the statement about `Rad_fd` the
sharper one.

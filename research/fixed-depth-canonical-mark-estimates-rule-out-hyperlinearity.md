---
rg: 2
id: fixed-depth-canonical-mark-estimates-rule-out-hyperlinearity
kind: claim
title: Depth-dependent canonical mark estimates are enough to refute hyperlinearity
distinct_from:
  instance-modulated-kleene-microstate-diagonal: that permits compiler constants depending on the source program; this removes uniformity across proof depths for one fixed marked group.
  approximate-relative-leavitt-cell-kills-active-trace: that supplies one dimension-free endpoint after a decoder; this is the double-limit principle allowing decoder constants to grow arbitrarily with finite depth.
---

Let `Gamma=<X|R>` be finitely presented and let `1!=w in Gamma`.  Suppose
there are numbers `b_N>=0` with `b_N->0` such that, for every `N`, there are a
finite word window `F_N` and a finite constant `C_N` with the following
property.  Every unitary tuple `U` satisfies

```text
||w(U)-I||_2^2
 <= b_N+C_N (def_R(U)+sep_(F_N)(U)),                    (FDM1)
```

where `def_R` is the maximum normalized-HS defining-relator defect and

```text
sep_(F_N)(U)=max_(g in F_N, g!=1) |tr(g(U))|             (FDM2)
```

is the error from the canonical delta trace on that finite window.  Then
`Gamma` is not hyperlinear.

Indeed, on a canonical-trace microstate sequence both errors in `(FDM1)` tend
to zero for each fixed `N`.  Taking the sequence limit first gives

```text
limsup ||w(U_n)-I||_2^2<=b_N
```

for every `N`, and then `N->infinity` makes the limit zero.  But canonical
trace separation of the nonidentity word `w` gives

```text
||w(U_n)-I||_2^2=2-2 Re tr(w(U_n))->2,
```

a contradiction.

There is no requirement that `C_N` be bounded, computable uniformly in `N`,
or related to the matrix dimension.  Each finite-depth consequence is taken
after the microstate error has already gone to zero.  This is the correct
quantifier order for a fixed-group root-character proof and is strictly
weaker than the all-representations modulus requested by
`affine-leavitt-steinberg-hs-coefficient-decoder`.

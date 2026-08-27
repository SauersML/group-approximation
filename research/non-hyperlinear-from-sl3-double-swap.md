---
rg: 2
id: non-hyperlinear-from-sl3-double-swap
kind: route
title: The double-swap group at a large prime reaches the goal through outlier confinement plus the outlier involution exclusion
target: non-hyperlinear-group
requires:
  - arithmetic-double-swap-extension-is-binary-coset-wreath
  - sl3-double-swap-involution-is-outlier-carried
  - sl3-outliers-carry-no-balanced-free-involution
---

Fix `p >= 11` and instantiate the double-swap extension at the pair
`Lambda = SL_3(Z) <= Gamma = SL_3(Z[1/p])`:

```text
E_p = Gamma *_Lambda (Lambda x C_2),   finitely presented.
```

Suppose `E_p` were hyperlinear, with canonical-character microstates
`phi_n`.  In the tracial ultraproduct these give a trace-preserving
embedding of `L(E_p)`, hence of `N = L(Gamma)`, together with the swap
involution `s`: self-adjoint, in `iota(B)' cap M` for `B = L(Lambda)`,
centered, and free from `N` with amalgamation over `B` (Britton normal
form for the amalgam `E_p`, exactly as in
`hnn-amalgamated-free-haar-unitary-proof` with `L(C_2)` for `L(Z)`).
`sl3-double-swap-involution-is-outlier-carried` says the lattice
microstates of any such model are uniform outliers;
`sl3-outliers-carry-no-balanced-free-involution` says uniform outliers
carry no such `s`.  Contradiction: `E_p` is not hyperlinear, and it is a
finitely presented witness for `non-hyperlinear-group`.  By the swap
identification `(DSW4)` the arithmetic double
`D_p = Gamma *_Lambda Gamma` is then a second finitely presented
witness.

Position among the goal's leaves: the only open input is
`sl3-outliers-carry-no-balanced-free-involution`, which is implied by
`sl3-z-weakly-ucp-stable` (the leaf of the two earlier reductions) and
not conversely.  This is therefore the weakest leaf currently wired to
the goal, and the first that asks nothing about repairing approximate
representations -- only that one moment pattern cannot occur on the
sector that repair cannot reach.

---
rg: 2
id: authenticated-coarse-fine-return-collapse-proof
kind: route
title: Lift the corona representation, apply the return at each coordinate, and read off the rank contradiction
target: authenticated-coarse-fine-return-forces-mf-collapse
requires:
  - rank-deficient-return-row-has-operator-norm-one
  - opnorm-packet-exactification-is-dimension-free
---

Suppose some homomorphism `Theta : Gamma -> U(Q)`,
`Q=prod_n M_(d_n)/sum_n M_(d_n)`, has `Theta(z) != 1`.

**Coordinate lifts.**  As in `fd-mark-stability-mf-invisibility-proof`, choose
unitary lifts `U_n=(phi_n(sigma))_(sigma in S)`.  For each of the finitely
many `rho in R`, the word `rho(U_n)` represents `Theta(rho)=1`, so
`||rho(U_n)-I||_op -> 0`; taking the maximum over the finite set `R`,

```text
Def_R(U_n) -> 0.
```

Finiteness of the presentation is used exactly here, and only here: a maximum
over infinitely many relators need not vanish.

**The mark survives.**  `Theta(z) != 1` means the sequence `z(U_n)-I` does not
lie in `sum_n M_(d_n)`, so there are `c>0` and a subsequence along which
`||z(U_n)-I||_op >= c`.  Restrict to it.

**Apply the hypothesis.**  For `n` large, `Def_R(U_n)` is below the threshold
and `z(U_n)` is bounded away from `I`, so the authenticated return produces
`P_n != 0`, exact `r by r` and `s by s` matrix-unit systems with the common
identity `P_n`, minimal corners `e_n`, `f_n`, and the evaluated unitary `J_n`
with

```text
||(1-f_n)J_n e_n||_op <= omega(Def_R(U_n)) -> 0.
```

The `o(1)` packet perturbation is legitimate and costs nothing: by
`opnorm-packet-exactification-is-dimension-free` the rounding modulus depends
only on `r,s`, and telescoping the fixed word `J` over an `O(eta)` change of
its letters moves `J_n` by `O(|J| eta)`, with `|J|` fixed.

**Contradiction.**  `P_n != 0` and both systems are exact with identity
`P_n`, so by `(ROW6)`

```text
rank(e_n)=rank(P_n)/r > rank(P_n)/s=rank(f_n),
```

and `rank-deficient-return-row-has-operator-norm-one` gives, for every `n`,

```text
||(1-f_n)J_n e_n||_op = 1.
```

This contradicts the previous display once `omega(Def_R(U_n))<1`.

Hence no corona representation keeps `z` nontrivial, i.e. `Theta(z)=1` for
every `Theta`, which is `(AMR2)`.  For `(AMR3)`: `Rad_MF(Gamma)` is an
intersection of kernels of homomorphisms out of `Gamma`, hence normal, so it
contains `<<z>>_Gamma=Gamma`.

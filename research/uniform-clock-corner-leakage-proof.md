---
rg: 2
id: uniform-clock-corner-leakage-proof
kind: route
title: Square the compressed clock block and retain its complementary excursion
target: uniform-clock-corner-is-not-a-reflection
requires:
  - uniform-clock-reflection-block-encodes-game-hamiltonian
---

The established compression identity is

```text
Q(1-C)Q=H tensor Q,
```

which is equivalent to `(UCC1)`. Because `C=C^*=C^(-1)`, insert
`1=Q+(1-Q)` between its two factors:

```text
Q=Q C^2 Q
 =(Q C Q)^2+Q C(1-Q)C Q.
```

Substituting `(UCC1)` gives

```text
Q C(1-Q)C Q
 =[1-(1-H)^2] tensor Q
 =H(2-H) tensor Q,
```

which proves `(UCC2)`. Since `0<=H<=1`, the positive operator
`H(2-H)` vanishes exactly when `H=0`; this proves `(UCC3)`. Taking the
trace proves the equality in `(UCC4)`, and `H(2-H)>=H` proves its lower
bound.

For a unitary `W`, the same block identity gives

```text
||(1-Q)WQ||_2^2=tau(Q)-||QWQ||_2^2.
```

If `QWQ` converges in normalized Hilbert--Schmidt norm to `QCQ`, the right
side converges to
`tau(Q)-||QCQ||_2^2=tau(QH(2-H))`. Therefore first-corner approximation
to `C` supplies positive leakage rather than the vanishing leakage used by
the finite-order compression telescope.

Finally, `(UCC5)` is block diagonal. On clock block `j`, its only
nonidentity factor is `(1-L_j)+L_jX`, which is an involution because `L_j`
commutes with the flag flip. Distinct `c_j` have disjoint clock support and
commute. Their product restricts to this controlled involution on every
clock block, hence equals `C`; its square is one. This proves the exact
finite-lamp construction and its torsion obstruction.

---
rg: 2
id: uniform-clock-corner-is-not-a-reflection
kind: claim
title: The uniform zero-flag corner of the Fanizza clock reflection is a strict contraction
artifacts:
  - research/artifacts/fanizza-wandering-dependency-audit-2026-08-23.md
invalidates:
  - fanizza-compression-implies-localized-square-return
  - fanizza-wandering-dirichlet-return-route
distinct_from:
  uniform-clock-reflection-block-encodes-game-hamiltonian: that proves the full controlled clock operator is a reflection and computes its first corner Dirichlet form; this computes the square and leakage of that corner and shows it is not itself a reflection.
  fanizza-verifier-d16-charger-globalizes-ground-support: that uses the transverse flag-X basis and shows the native flag-Z carrier is not invariant; this gives the exact operator-valued leakage formula and audits the two downstream promotion routes which incorrectly require invariance.
---

Let `C`, `H`, and

```text
Q=1 tensor q_s tensor q_0
```

be the controlled clock reflection, losing Hamiltonian, and uniform
zero-flag carrier of
`uniform-clock-reflection-block-encodes-game-hamiltonian`. Under the
canonical identification of `Q` with the system space,

```text
Q C Q=(1-H) tensor Q,                                  (UCC1)
Q C(1-Q)C Q=H(2-H) tensor Q.                          (UCC2)
```

Consequently

```text
(Q C Q)^2=Q    iff    H=0.                             (UCC3)
```

In particular, the full operator `C` is a reflection, but its selected
corner is not a corner reflection whenever the Hamiltonian is nonzero.
The identity `C^2=1` returns through the complementary clock/flag space;
it cannot be squared inside `Q`.

More quantitatively, for every normalized trace on the system factor,

```text
||(1-Q)C Q||_2^2
 = tau(Q H(2-H))
 >= tau(Q H).                                          (UCC4)
```

Thus approximating `QWQ` by `QCQ` forces the off-corner leakage of a unitary
`W` to converge to the generally positive value in `(UCC4)`. It does not
give the vanishing leakage needed to telescope powers of `W`.

This invalidates two existing Fanizza implications, without refuting the
open word-construction target itself.

- `fanizza-compression-implies-localized-square-return` substitutes
  `V_m^2=Q` after compressing the full clock reflection. The correct square
  is `(1-H_m)^2 tensor Q`, so the substitution is valid only on the zero
  Hamiltonian sector.
- `fanizza-wandering-dirichlet-return-route` invokes
  `compressed-reflection-kills-even-cesaro-mark` on this same corner. That
  theorem assumes a reducing corner unitary `V=QVQ`, `V^2=Q`; `(UCC1)--(UCC4)`
  show that its hypothesis is absent here.

The established two-copy inequality still gives

```text
D_R <= C_m H_m=C_m Q(1-C)Q,
```

so the clock reflection remains a valid one-step Dirichlet package. What
is missing is a return mechanism controlling excursions out of `Q`, not
merely an ordinary word whose first compression agrees with `C`.

## Exact native wordization attempt

There is no hidden construction in the finite clock itself. On the selected
representation, introduce for each clock value `j` the controlled involution

```text
c_j=1-e_(jj)+e_(jj)((1-L_j)+L_j X).                   (UCC5)
```

The `c_j` commute, have order two, and

```text
product_j c_j=C.                                      (UCC6)
```

Thus the direct finite-lamp wordization of the established reflection is an
order-two word. It exactly packages the Hamiltonian but cannot be the
wandering word. Declaring the controls only in a chosen representation
does not impose them on canonical matrix microstates; imposing their finite
lamp relations makes the product torsion. Hence the controlled-clock
reflection and two-copy Hamiltonian alone reach a sharp fork: exact native
wordization or wandering, but not both. A successful extension must add a
payload-coupled, dimension-independent rule controlling the complementary
excursion in `(UCC2)` while leaving an infinite normal form.

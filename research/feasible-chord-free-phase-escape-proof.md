---
rg: 2
id: feasible-chord-free-phase-escape-proof
kind: route
title: Install the finite common sign and rotate two collided atoms through independent free phases
target: feasible-chord-collision-has-free-phase-block-escape
requires:
  - finite-relative-commutant-chord-is-bounded-integer-feasibility
  - free-phase-context-escape-criterion
  - one-binary-marginal-block-escape
---

Feasibility of `(WIF3)` and
`chord-regauging-is-relative-commutant-feasibility` give `(FCC1)` with
`U_i in A_i'`.  Replace the endpoint context partitions by their `U_i`
conjugates.  This changes neither previously frozen separator marginals nor
the context projection relations, and the two chord signs now literally
equal `Z`.

Choose a full rank-one coordinate refinement `(e_j)_(j=1)^D` of the selected
endpoint partition which simultaneously diagonalizes its frozen binary
marginals and `Z`.  By the collision hypothesis, `e_r<=P_a` and `e_s<=P_b`
with `a!=b` lie in one joint sign fiber.  Let `H_rs` be the Hadamard rotation
on their two-dimensional span and the identity elsewhere.  It commutes with
every frozen marginal and with `Z`.

Let `F_D=<h_1,...,h_D>` and put

```text
W=sum_(j=1)^D e_j tensor h_j,
V=W(H_rs tensor 1).                                     (FCP1)
```

Orthogonality of the `e_j` makes `W`, hence `V`, an exact corner unitary in
`q C[K times F_D]q`.  Both factors in `(FCP1)` commute with all frozen signs
and with `Z`.  Conjugation by `V` preserves orthogonality, the sum of the
context atoms, all old signed marginals, and the chord sign.

In `V P_a V*`, the Hadamard cross term between `e_r` and `e_s` acquires the
reduced free coefficients `h_r h_s^-1` and `h_s h_r^-1`.  Because `P_a`
contains `e_r` but not `e_s`, these terms do not cancel in its coarse sum.
The same holds with opposite cross sign for `P_b`.  Linear independence of
reduced words in `C[F_D]` therefore shows

```text
V P_a V*, V P_b V* notin q C[K]q.                      (FCP2)
```

This proves the construction.  Conversely, if the frozen signs and `Z`
separate the supported assignments, each `P_a` is a joint spectral projection
of those signs.  Any unitary commuting with all of them fixes every `P_a`.
This is exactly the necessity half of
`free-phase-context-escape-criterion`, and proves the claimed sharp boundary
for endpoint-conjugation cells.


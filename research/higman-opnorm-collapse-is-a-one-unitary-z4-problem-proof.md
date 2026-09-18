---
rg: 2
id: higman-opnorm-collapse-is-a-one-unitary-z4-problem-proof
kind: route
title: Amplify a tuple into its four cyclic rotations, and read an order-four orbit back as a tuple
target: higman-opnorm-collapse-is-a-one-unitary-z4-problem
requires: []
artifacts:
  - experiments/higman-minimax-2026-09-17/equivariant_search.py
---

Notation is as in `(HZ1)`--`(HZ3)` of the target.

*Item 1, from an order-four orbit to a tuple.*  Let `P` and `S` be unitaries in
`U(N)` with `S^4=1`, and put `U_i=S^i P S^(-i)` for `i=0,...,3`.  Since
`S^4=1`, the same formula with `i=4` gives `U_4=P=U_0`.  So the indices of the
tuple are consistent modulo four.  For every `i`,

```text
U_i U_(i+1) U_i^* - U_(i+1)^2
 = S^i ( P (S P S^*) P^* - (S P S^*)^2 ) S^(-i).
```

Operator norm is unitarily invariant.  Hence all four relator defects equal
`def_S(P)`, and `||U_i-1||=||S^i(P-1)S^(-i)||=||P-1||`.

*Item 2, from a tuple to an order-four orbit.*  Let `U_0,...,U_3` be in
`U(L)`.  Put `N=4L`, `C^N=C^L(+)C^L(+)C^L(+)C^L` with blocks indexed by
`Z/4`, and define

```text
P = diag(U_0,U_1,U_2,U_3),
S (x_0,x_1,x_2,x_3) = (x_1,x_2,x_3,x_0).
```

`S` is a permutation of blocks with `S^4=1`, and `S P S^*=diag(U_1,U_2,U_3,U_0)`.
Indeed, `S^* (x_0,...,x_3)=(x_3,x_0,x_1,x_2)`.  Applying `P` gives
`(U_0x_3,U_1x_0,U_2x_1,U_3x_2)`, and applying `S` gives
`(U_1x_0,U_2x_1,U_3x_2,U_0x_3)`.  All operators involved are block diagonal,
so

```text
P (S P S^*) P^* - (S P S^*)^2
 = diag( U_iU_(i+1)U_i^* - U_(i+1)^2 : i=0,1,2,3 ).
```

The norm of a block-diagonal operator is the maximum of the block norms.  So
`def_S(P)=def(U)`, and likewise `||P-1||=max_i||U_i-1||`.
`experiments/higman-minimax-2026-09-17/equivariant_search.py` (mode `amp`)
checks this identity numerically on the stored twelve-dimensional witness:
both sides are `0.309828`.

*Item 3, profiles.*  Item 1 maps every feasible pair for `m^(4)_c(N)` to a
tuple in `U(N)^4` with the same defect and the same distance.  Hence
`m_c(N)<=m^(4)_c(N)`.  Item 2 maps every tuple feasible for `m_c(L)` to a pair
feasible for `m^(4)_c(4L)` with the same values.  Hence
`m^(4)_c(4L)<=m_c(L)`.  Both profiles are nonincreasing.  For `m^(4)` pad `P`
by `1` and `S` by `1`, since `S (+) 1` still has fourth power `1`.  So the two
limits exist, and the chain

```text
m_c(4L) <= m^(4)_c(4L) <= m_c(L)
```

shows that they coincide.  `(HZ4)` follows from item 1 of
`higman-opnorm-defect-profile-has-dim-twelve-witness`.

*Item 4, diagonal form.*  `S` is normal with `S^4=1`, so `S=W D W^*` for a
unitary `W` and a diagonal `D` with entries in `{1,i,-1,-i}`.  Put
`P'=W^*PW`.  Then `def_S(P)=||P' D P' D^* P'^* - D P'^2 D^*||`.  Multiplying by
`D^*` on the left and by `D` on the right leaves the norm unchanged and gives
`||R P' R^* - P'^2||` with `R=D^*P'D`.  Also `||P-1||=||P'-1||`.

*Item 5, grading collapse.*  If `P` commutes with `S`, then `SPS^*=P`.  The
defect becomes `||P-P^2||=||1-P||`, because `P` is unitary.  If `P` is within
`eta<1` of an operator `P_0` in `{S}'`, first replace `P_0` by the unitary part
`V=P_0|P_0|^(-1)` of its polar decomposition.  `P_0` is invertible because
`eta<1`.  `P_0^*` commutes with `S`, because `S^*=S^3`, so `V` commutes with
`S`.  The singular values of `P_0` lie within `eta` of `1`, so
`||V-P_0||=|| |P_0|-1 ||<=eta` and `V` is within `2eta` of `P`.  Changing `P` by at most `2eta` changes `def_S` by at
most `10eta`: the expression has three factors of `P` or `SPS^*` in the first
term and two in the second.  So `||P-1||<=def_S(P)+12eta`.

---
rg: 2
id: finite-free-burnside-linear-opnorm-modulus
kind: claim
title: Finite ordinary free Burnside groups give linear power-law moduli
distinct_from:
  matrix-restricted-burnside-gap: that asks for the modulus for every exponent, including the regime where the ordinary free Burnside group is infinite; this closes the entire finite-free-Burnside regime and leaves that frontier untouched.
  restricted-burnside-finiteness: that says the finite restricted quotient R(m,N) exists for every m and N by Zelmanov; finiteness of R alone does not make its finite-residual relators consequences of the abstract exponent law, while this claim assumes the ordinary group B(m,N) itself is finite.
  exponent-two-modulus-is-the-commutator-norm: that gives a sharp explicit identity for one exponent and three words; this gives a generally nonexplicit power-area coefficient for every relator whenever B(m,N) is finite.
  finite-group-opnorm-support-profile: that corrects an approximate model of a fixed finite presentation to an exact representation; this performs no rounding and directly telescopes finitely many Nth-power defects.
---

**ESTABLISHED.**  Put

```text
K_N = << w^N : w in F_m >>,
B(m,N) = F_m / K_N.
```

For `r in K_N`, define its `N`-power area to be the least `L` for which
there are words `u_1,...,u_L,v_1,...,v_L in F_m` with the exact free-group
identity

```text
r = product_(t=1)^L v_t u_t^N v_t^(-1).                         (FBM1)
```

(The inverse of an `N`th power is again an `N`th power, so signs can be
absorbed into the words `u_t`.)  Such a finite `L` exists by the definition
of normal closure.  A certificate (FBM1), with
`W_r={u_1,...,u_L}`, gives every unitary tuple `U in U(d)^m` the exact
dimension-free estimate

```text
||r(U)-I||_op
 <= sum_(t=1)^L ||u_t(U)^N-I||_op
 <= L max_(w in W_r) ||w(U)^N-I||_op.                            (FBM2)
```

If `r` is freely trivial, pad the empty certificate by `1^N`, so that
`L>=1` and `W_r` is nonempty.

Now suppose the **ordinary** free Burnside group `B(m,N)` is finite.  Its
trivial subgroup is finite-index normal, hence its finite residual is
trivial and the canonical map

```text
B(m,N) -> R(m,N)
```

is an isomorphism.  Fix the canonical presentation on the images of the
free generators,

```text
R(m,N)=<x_1,...,x_m | s_1,...,s_k>.
```

Every named relator `s_j` then belongs to `K_N`.  Fix one certificate
(FBM1) for it, of length `L_j>=1`, and let `W_j` be precisely the finite set
of base words occurring in that certificate.  For every `eps>0`, every
matrix size `d`, and every `U in U(d)^m`,

```text
max_(w in W_j) ||w(U)^N-I||_op < eps/(L_j+1)
   ==> ||s_j(U)-I||_op < eps.                                   (FBM3)
```

Thus the hypothesis controls only the finitely many named powers
`w^N` with `w in W_j`; it assumes nothing about powers of other words.
Both `W_j` and `L_j` depend on `m,N,s_j` and the chosen finite certificate,
but not on `d` or `eps`.

In particular, for the sharpened target
`delta_N=2 sin(pi/N)` one may take
`eta_j=delta_N/(L_j+1)`.  This establishes
`matrix-restricted-burnside-gap` throughout the finite ordinary
free-Burnside regime.  The classical positive cases give this conclusion
for every finite `m` and `N in {2,3,4,6}`.

## Scope

Zelmanov's theorem makes the **restricted** group `R(m,N)` finite for every
`m,N`; it does not say that the ordinary `B(m,N)` is finite for every
exponent.  If `B(m,N)` is infinite, then in any finite presentation of
`R(m,N)` on the canonical generators at least one relator lies outside
`K_N`.  No decomposition (FBM1) exists for that relator, and the general
dimension-free modulus problem remains open exactly there.

ROUTES

finite-free-burnside-linear-opnorm-proof

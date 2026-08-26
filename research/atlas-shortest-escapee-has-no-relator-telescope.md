---
rg: 2
id: atlas-shortest-escapee-has-no-relator-telescope
kind: claim
title: Neither dangerous commutator of the shortest Atlas escapee lies in the relator normal closure
distinct_from:
  atlas-shortest-escapee-literal-control-firewall: that shows the four visible controls generate only an order-twenty-four parabolic; this excludes every exact conjugate-relator telescope, even one using longer controls or all Atlas relators.
  atlas-escapee-defect-charges-inversion-commutator-energy: that lower-bounds inversion energy whenever an escapee defect improves; this proves that the two load-bearing energy terms cannot be upper-bounded by the standard word-factorization telescope.
  atlas-kernel-window-length-nine: that detects short words outside the cartesian kernel by finite quotients; this uses survival in the canonical Leavitt quotient to separate two particular cartesian-kernel commutators from the Atlas relator normal closure.
---

**ESTABLISHED NORMAL-CLOSURE FIREWALL.**  Retain the notation of
`atlas-shortest-escapee-literal-control-firewall`:

```text
a=8461,             b=8621,             c=8241,
E_w=6||[A_a,B_b]||_2^2+3||[A_a,B_c]||_2^2+||[A_a,B_a]||_2^2.
```

In the free product of the two Atlas charts put

```text
r_b=[a_1,b_2],                 r_c=[a_1,c_2].         (NRT1)
```

Let `T_St` denote the full `4,636`-word analytic relator list, and let `C`
be its `4,564` cartesian controls.  Then

```text
r_b notin <<T_St>>,            r_c notin <<T_St>>,    (NRT2)
```

and hence neither word belongs to `<<C>>`.

Indeed the canonical map to the Leavitt quotient sends

```text
r_b |-> x_13(1),
r_c |-> x_15(1)x_13(1),                                (NRT3)
```

and both displayed elementary matrices are nonidentity.  Every word of
`T_St` maps to the identity by construction, proving `(NRT2)`.

Consequently there is no finite identity of either form

```text
r_b=prod_j q_j s_j^(+-1)q_j^(-1),
r_c=prod_j q_j s_j^(+-1)q_j^(-1),       s_j in C,     (NRT4)
```

or even with `s_j in T_St`.  Thus neither load-bearing term can be charged by
the usual exact word telescope: evaluate `(NRT4)`, telescope the product,
and use unitary invariance to bound the left defect by the sum of the relator
defects.  The obstruction is not merely that the most visible controls sit
in the wrong parabolic; the target words survive after **all** Atlas relators
are imposed.

**ANALYTIC COERCIVITY IS STILL OPEN.**  `(NRT2)` rules out only bounds whose
proof is an exact product-of-conjugates certificate.  A spectral-gap or
operator-Jacobian inequality on the restricted family of two regular chart
representations need not come from a free-product word identity.  Therefore
this result neither proves nor refutes

```text
E_w(U) <= C_w sum_(s in C) ||pi_U(s)-1||_2^2.
```

The full-control local/global endpoint remains exactly that analytic
question; scalar trace stationarity and the bounded Hessian scan still do not
decide it.

The canonical finite-factor evaluation is computed in
`atlas-shortest-escapee-has-exact-leavitt-tracial-energy`: all relators vanish
there while `E_w=18`.  Thus any surviving coercivity theorem must use finite
dimensionality and would already select the nonhyperlinear branch.

DERIVATION
atlas-shortest-escapee-no-relator-telescope-proof

---
rg: 2
id: exhausting-ideal-reservoirs-have-lift-or-quotient-separator
kind: claim
title: Exhausting ideal reservoirs have an exact lift or a quotient-level separation functional
distinct_from:
  finite-relator-reservoir-repairs-every-fd-packet: that asks for one finite reservoir which repairs every finite-dimensional packet exactly; this allows the reservoir depth to grow and identifies the exact alternative when no uniform depth exists.
  finite-packet-triangle-repair-is-ideal-block-choi-feasibility: that gives a finite-dimensional dual certificate for failure at one packet and one depth; this controls an exhausting sequence and explains precisely when such certificates have a quotient-level ultralimit.
  point-norm-approximate-ucp-sections-close-to-exact: that closes already-constructed approximate ucp lifts; this manufactures those approximate lifts from vanishing distance to the affine relator reservoirs and proves the complementary separation statement.
  km-triangle-relator-kernel-has-no-relative-gap: that gives low relator energy in arbitrary unitary representations; this is a convex distance dichotomy for ucp lifting and does not use a spectral inverse.
---

**ESTABLISHED.**  Let `q:A->>Q=A/I` be a unital C-star quotient, let
`E subset Q` be a finite-dimensional operator system, and let

```text
t:E->A       unital, self-adjoint, linear,       q t=id_E.   (ERD1)
```

Let

```text
L_1 subset L_2 subset ... subset I
```

be finite-dimensional self-adjoint linear spaces whose union is dense in
`I`.  Put `V_m=L_sa(E,L_m)`, let `C=UCP(E,A)`, and use the operator norm on
the finite-dimensional-domain map space to define

```text
delta_m=dist(t+V_m,C)
       =inf { ||t+d-phi|| : d in V_m, phi in UCP(E,A) }.    (ERD2)
```

Then `delta_m` decreases, and exactly one of the following equivalent
alternatives occurs.

1. `inf_m delta_m=0`.  The inclusion `E->Q` has an exact ucp lift to `A`.
2. `delta:=inf_m delta_m>0`.  There is a bounded real functional
   `bar ell` on the self-adjoint map space `L_sa(E,Q)` such that

   ```text
   bar ell(id_E-q phi)>=delta       for every phi in UCP(E,A). (ERD3)
   ```

   In particular `id_E` is strictly separated from all liftable ucp maps and
   has no ucp lift.

Conversely, an exact ucp lift forces the first alternative.  Thus

```text
E is ucp liftable
 iff lim_m dist(t+L_sa(E,L_m),UCP(E,A))=0.                 (ERD4)
```

Proof: `exhausting-reservoir-distance-dichotomy-proof`.

## Relation to the finite-packet ideal-block certificate

Assume now that `A=C^*(G_0)` is the RFD virtually free algebra in the
Kac--Moody triangle and that `L_m` are increasing finite relator reservoirs.
For every fixed `m` with no depth-`m` repair, the contrapositive of
`finite-reservoir-compactness-lifts-ucp-repairs` gives a finite packet
representation `rho_m`.  With

```text
J_m=rho_m(I),       z_m=1_(J_m),
```

`finite-packet-triangle-repair-is-ideal-block-choi-feasibility` supplies a
dual Choi certificate `F_m`.  Pull it back to the one fixed Banach space by

```text
ell_m(s)=F_m(z_m rho_m o s),       s:E->A.                 (ERD5)
```

Then `ell_m` annihilates `V_m`, regardless of the packet dimension and
regardless of the support projection `z_m`, and

```text
ell_m(t)>sup { ell_m(phi):phi in UCP(E,A) }.               (ERD6)
```

Consequently, if the pullbacks can be normalized to `||ell_m||=1` while the
gaps in `(ERD6)` stay bounded below, every weak-star tail cluster point
annihilates `L_sa(E,I)` and descends to a separator of the form `(ERD3)`.
This is the rigorous ultralimit use of the ideal-block certificates: moving
packet dimensions and moving `z_m` disappear only after the pullback `(ERD5)`.

There is also a sharp warning.  Mere strict separation at each finite depth
does **not** bound the normalized gaps in `(ERD6)`; the finite-dimensional
separators can become arbitrarily ill-conditioned as `m`, `dim(rho_m)`, and
`z_m` vary.  Such degeneration does not by itself produce a positive vector
state or a low-relator-spectrum representation, because `F_m` is a general
signed real Choi functional.  The invariant object is the global distance
`(ERD2)`: if that distance tends to zero, point-norm lifting closure gives the
desired exact lift; if it stays positive, the proof produces `(ERD3)` without
any unjustified compactness of the raw packet certificates.

At the explicit triangle, low-relator-spectrum finite-dimensional witnesses
do exist, but for the independent reason proved in
`km-triangle-relative-gap-failure-has-fd-full-support-witnesses`.  They occur
on both sides of `(ERD4)` and therefore cannot serve as a diagnostic for
failure of uniform reservoir depth.

On the concrete finite-dimensional three-face system, the complementary
separator branch is further constrained by
`three-face-quotient-separators-are-not-one-face-local`: compatible
symmetry averaging preserves the separation gap, but no resulting separator
can factor boundedly through one face.  In particular it cannot collapse to the
closing-face prefix Gram/cyclic-holonomy witness, because the closing-face
Fourier expectation has an explicit ucp lift.  No bounded decomposition into
The finite-dimensional face-sum admits a bounded splitting, and every such
face decomposition retains a tree-face component of norm at least
`delta/4`.

DERIVATION
exhausting-reservoir-distance-dichotomy-proof

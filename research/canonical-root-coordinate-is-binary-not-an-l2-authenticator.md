---
rg: 2
id: canonical-root-coordinate-is-binary-not-an-l2-authenticator
kind: claim
title: A canonical root coordinate is binary and does not authenticate the row coefficient
distinct_from:
  orthogonal-hecke-row-packs-common-source-energy-into-one-root: that constructs the row coefficient and states the desired one-root estimate; this identifies the exact information supplied by that root on canonical microstates and proves that fixed-root exactification cannot supply the missing coupling.
  hs-steinberg-root-kernel-is-linear-sofic: that asks for a rank-metric decoder for an entire coefficient quotient; this gives the necessary-and-sufficient qualitative kernel-reflection property for only the single OHR coefficient.
---

Let

```text
g=x_12(R_Q)
```

be the root word from
`orthogonal-hecke-row-packs-common-source-energy-into-one-root`, and let
`U_n` be canonical-delta normalized-Hilbert--Schmidt microstates for the
ambient finitely presented group.  The row coefficient is

```text
R_Q=sum_(j=1)^m E_(j1) tensor D_j,
D_j=a_j V_j^*Q-V_j^*QZ_j.                              (CRB1)
```

All factors in `D_j` are contractions.  Hence

```text
||D_j||_2<=2,
m||R_Q||_2^2=sum_j||D_j||_2^2,
||R_Q||_2^2<=4.                                        (CRB2)
```

The single root coordinate has a sharp dichotomy, but the useful branch of
that dichotomy is precisely the still-open decoder.

## Canonical root dichotomy

### Theorem

Let `Gamma` be a group, let `g in Gamma`, and let `A_n` be any matrices
decoded from canonical-delta microstates `U_n` of `Gamma`, with

```text
limsup_n ||A_n||_2^2<=B.                               (CRB3)
```

Then:

1. if `g!=1`,

   ```text
   lim_n ||g(U_n)-I||_2^2=2
   ```

   and consequently

   ```text
   limsup_n (||A_n||_2^2-(B/2)||g(U_n)-I||_2^2)<=0;     (CRB4)
   ```

2. if `g=1`, then `||g(U_n)-I||_2 ->0`, and for every fixed finite `K`

   ```text
   ||A_n||_2^2<=K||g(U_n)-I||_2^2+o(1)                (CRB5)
   ```

   holds if and only if `||A_n||_2->0`.

### Proof

Canonical-delta convergence says

```text
tr(g(U_n))->tau_Gamma(g),
tau_Gamma(g)=1_(g=1).
```

For a unitary word,

```text
||g(U_n)-I||_2^2=2-2 Re tr(g(U_n)).                    (CRB6)
```

This proves both limits.  In the nonidentity case `(CRB3)` and `(CRB6)`
give `(CRB4)`.  In the identity case the right side of `(CRB5)` tends to
zero, so `(CRB5)` is equivalent to `||A_n||_2->0`.  The converse uses the
vanishing `||A_n||_2^2` itself as the `o(1)` term.  ∎

For the OHR row, take `B=4`.  If the root word is nontrivial, the estimate
with `K=2` is automatic but useless: its right side converges to `4`, not to
zero.  To make the root pay defining-relator energy one imposes `g=1` (or
puts it in the relator normal closure).  In that quotient `(OHR6)` is
equivalent, on canonical microstates, to

```text
||R_Q(U_n)||_2->0
iff
sum_j||a_jV_j^*Q-V_j^*QZ_j||_2^2->0.                  (CRB7)
```

Thus the root name has compressed the syntax to one coordinate, but it has
not weakened the analytic theorem at all.

## The weakest one-coordinate hypothesis

No full coefficient-ring decoder is logically necessary.  The exact
minimal sequential property is the following **one-coordinate kernel
reflection**:

```text
For every canonical matrix-microstate sequence U_n,
Phi(x_12(R_Q))=1 in the tracial matrix ultraproduct
implies R_Q(U_n)=0 in L2 of that ultraproduct.           (CRB8)
```

Here `Phi` denotes only the ultraproduct group homomorphism; `(CRB8)` does
not ask for a coefficient homomorphism.  By the theorem, `(CRB8)` is
necessary and sufficient for the qualitative canonical version of `(OHR6)`
when the root is a relator.  It is strictly weaker than
`hs-steinberg-root-kernel-is-linear-sofic`, but it is not a consequence of
root-group exactification.

A convenient stronger sufficient hypothesis would be a single decoded
coefficient shadow `pi_n` on the finite span containing `R_Q`, with constants
independent of matrix dimension, such that

```text
||R_Q(U_n)-pi_n(R_Q)||_2=o(1),
||pi_n(R_Q)||_2
   <=C||x_12(R_Q)(U_n)-I||_2+o(1).                     (CRB9)
```

Then `(OHR6)` follows with `K=C^2` after absorbing the cross term.  Notice
that only this one coefficient must be reflected; multiplication on the
rest of the ring is unnecessary.  Conversely, taking
`pi_n(R_Q)=R_Q(U_n)` shows that `(CRB9)` contains no hidden gain over the
kernel-reflection assertion unless `pi_n` is obtained independently from
the Steinberg coordinates.

## Exact finite-root countermodel to the Gowers--Hatami shortcut

Fixed finite-root exactification supplies no relation between a root
character reservoir and the analytic capacity cut.  This failure already
has an exact canonical finite model.

Let `E_1` be the order-eight extraspecial Pauli group with involutions
`X,Z,J` and

```text
[X,Z]=J,                    J central.                 (CRB10)
```

Use its left regular representation and normalized regular trace.  Put

```text
Q=(I+X)/2,                  a=Z,       V=I,       Z_0=Z.
```

The uncompressed covariance word is exact:

```text
aV-VZ_0=0.                                             (CRB11)
```

But the capacity-compressed row is

```text
D=aVQ-VQZ_0=ZQ-QZ=(1-J)ZX/2,
||D||_2^2=tau((1-J)/2)=1/2.                            (CRB12)
```

Now tensor this packet with the left regular representation of any fixed
finite row-root group, together with all of its shear normalizers.  Every
finite root multiplication table is exact, every nonidentity root element
has canonical trace zero, all Fourier atoms have their exact Plancherel
weights, and every named shear is an exact permutation.  A designated
identity root coordinate has distance zero.  Nevertheless the independent
capacity-compressed row `(CRB12)` has fixed positive energy.

This is not asserted to be a microstate of the full proposed `St_5`
presentation.  It is an exact countermodel to the proposed *proof inputs*:

```text
fixed finite root exactification
+ canonical Plancherel profile
+ exact shear covariance
+ exact uncompressed packet covariance
does not imply one-coordinate kernel reflection.       (CRB13)
```

Gowers--Hatami can make the finite root table exact, but it acts only on the
root factor in this model and leaves `(CRB12)` unchanged.  The missing
relation must therefore be a genuinely mixed matrix-coordinate statement
which authenticates the same analytic `Q` inside the root multiplicity
reservoir.  Rectangular label-expansion/multiplicity-contraction is the
larger version of the same decoupling.

## Consequences for the OHR lane

- The one-root construction remains the smallest live endpoint: `(CRB8)`
  would close it without decoding the coefficient ring.
- Canonical trace supplies no favorable quantitative interpolation for a
  relator root.  It changes the problem into the binary kernel-reflection
  assertion `(CRB8)`.
- Gowers--Hatami exactification of any fixed root window cannot prove
  `(CRB8)` without an additional mixed source-authentication relation.
- A valid next theorem must couple the root coordinate to the capacity cut
  `Q`, for example by a same-reservoir boundary payment or a common-carrier
  transverse-recovery estimate.  More finite root tables or more accurate
  Plancherel bookkeeping do not address the countermodel.

The audit therefore neither proves nor refutes `(OHR6)` for the full
Steinberg presentation.  It proves exactly what remains: one qualitative
root-kernel reflection implication for one coefficient, and it rules out
the fixed-finite-root/Gowers--Hatami shortcut to that implication.

The positive cyclic acceptance compressor does not evade this audit.
`cyclic-acceptance-return-is-one-root-but-still-needs-kernel-reflection`
shows that its return defect is syntactically smaller than `R_Q` and has a
dimension-free lower bound, but an exact D8-tensored model still decouples it
from an identity root coordinate.  Its one-root endpoint is `(CRB8)` with
`C_acc=D(T_game(G)-G)` substituted for `R_Q`.

## Attempts

- **Use canonical trace separation of the root.**  This works only when the
  root is nonidentity, where the root distance tends to `sqrt(2)` and cannot
  pay vanishing covariance energy.  Making the root a relator moves the
  construction to the other branch, where the desired estimate is exactly
  the row-collapse assertion `(CRB7)`.
- **Exactify a fixed finite row-root group with Gowers--Hatami.**  The exact
  Pauli/row-root product `(CRB10)--(CRB13)` retains every finite table and
  Plancherel condition while its capacity-compressed row has energy `1/2`.
  Exactification never couples the independent analytic cut to the root
  multiplicity reservoir.
- **Decode the whole coefficient quotient.**  This would suffice, but it is
  the substantially stronger open claim
  `hs-steinberg-root-kernel-is-linear-sofic`.  The remaining OHR endpoint
  needs only the one-coefficient kernel reflection `(CRB8)`.

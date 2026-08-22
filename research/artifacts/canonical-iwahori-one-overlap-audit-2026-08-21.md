# Canonical Iwahori transfer: one-overlap and trace-square audit

Date: 2026-08-21

## The exact scalar

For a projection `P` and unitary `U`, set

```text
t=tau(P),       alpha=tau(PUPU^*)=||PUP||_2^2.
```

Then

```text
||[P,U]||_2^2=2(t-alpha).                                    (A1)
```

The desired transfer is therefore saturation of the single universal
compression bound `alpha<=t`.  Centering `P` gives the normalized spherical
coefficient

```text
phi_P(g)=(tau(P rho(g) P rho(g)^*)-t^2)/(t(1-t)),             (A2)
```

and

```text
1-phi_P(g)=||[P,rho(g)]||_2^2/(2t(1-t)).                     (A3)
```

If `P` commutes with the first Iwahori vertex, `(A2)` is positive definite
and bi-invariant under that vertex.  A transfer failure of size `epsilon`
therefore gives an explicit spherical dent at most `1-2epsilon^2` on one
fixed second-vertex generator.

## Why scalarized Gao data stop before this scalar

Gao's scalar relative-embeddability model consists of an embedding into
`prod_omega A_k` and a commuting-square carrier `prod_omega B_k`.  The
commuting square transports conditional expectations of SOURCE elements;
the arithmetic Hecke-tower theorem consequently fixes orthogonality and
bimodule dimensions of `closure(N rho(g) N)`.

The projection in canonical Iwahori transfer is instead an AMBIENT element
of `rho(C_+)'`.  It need not belong to the carrier or to the source group
factor.  Its compression `P rho(g) P` is therefore an additional mixed
moment, not one of the conditional first moments or source bimodule inner
products fixed by Gao's data.  The precise missing statement is `(COH1)`,
not another use of Hecke-word orthogonality.

## Trace-square blindness

The conjugation character identity

```text
tr_(End(M_d))(Ad_U)=|tr_d(U)|^2                              (A4)
```

averages over `d^2` adjoint directions.  A centered positive-density
projection is one unit vector in that space, not a positive fraction of its
directions.  The block flip

```text
P=diag(1_m,0_m),       U=[[0,1_m],[1_m,0]]
```

has `tr(P)=1/2`, `tr(U)=0`, `U^2=1`, but `phi_P(U)=-1` and
`||[P,U]||_2=1`.  Hence canonical group-word trace squares cannot control
the required coefficient.  Residual-finite tensor camouflage preserves
`(A2)` while canonicalizing all group-word traces, in agreement with this
calculation.

The remaining finite-coordinate problem is now one real number: prove that
the liftable Iwahori geometry forces `alpha/t -> 1`.  Neither canonical
character, positive physical rank, nor the scalar Gao Hecke tower does so
formally.

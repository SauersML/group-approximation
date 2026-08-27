---
rg: 2
id: three-label-affine-lowering-no-go-proof
kind: route
title: Split every answer over three central atoms and compute all affine supports
target: three-label-affine-lowering-no-go
requires:
  - mipstar-bcs-tracial-nonru-exists
  - paddock-slofstra-bcs-forbidden-projection-dictionary
  - fu-mastel-zhang-cc-to-synchronous-cv
  - tracial-support-affine-linearization
---

Let `B_0` be the tracially satisfiable, non-`R^U` BCS supplied by
`mipstar-bcs-tracial-nonru-exists`, and let `S` be its associated synchronous
game.  In the tracial GNS quotient write its answer PVMs as

```text
(P_(i,a))_(a in O_i),       sum_a P_(i,a)=1.                 (TLS1)
```

The quotient trace is faithful.  The absence of an `R^U` representation is
equivalent to `omega_qa(S)<1` by the perfect-strategy dictionary.

## Three-label split preserves both sides of the gap

Define `S^(3)` to have answers `(a,t)`, where `t in F_3`, and verifier

```text
lambda^((3))((i,j),(a,t),(b,u))
  = lambda((i,j),a,b) 1_(t=u).                             (TLS2)
```

For every finite-dimensional strategy for `S^(3)`, coarse-grain its answer
PVMs over `t`.  Every round accepted by `(TLS2)` is accepted by the resulting
strategy for `S`, so

```text
omega_qa(S^(3)) <= omega_qa(S) < 1.                       (TLS3)
```

For completeness let `(e_t)_(t in F_3)` be the minimal projections of `C^3`
with its uniform trace and put

```text
Q_(i,a,t)=P_(i,a) tensor e_t.                             (TLS4)
```

These are PVMs.  Products with unequal labels vanish, and products with equal
labels inherit the original perfect correlations.  Hence `(TLS4)` is a
perfect tracial strategy for `S^(3)`.

Let `B^(3)` be the standard Paddock--Slofstra BCS associated to `S^(3)`.
Its BCS algebra has the trace induced by `(TLS4)`.  An `R^U` representation of
`B^(3)` would give a perfect quantum-approximable strategy for `S^(3)`, and
coarse-graining would give one for `S`, contrary to `(TLS3)`.  Thus `B^(3)`
is not `R^U`-satisfiable.  Applying the Fu--Mastel--Zhang incidence conversion
to `B^(3)` and repeating the tracial incidence calculation gives a perfect
pairwise-oracularizable commuting strategy.  Its finite-dimensional gap
follows by their soundness contrapositive.

## Exact support of the standard BCS conversion

Use active bits `x_(i,a,t) in F_2`, so their activity projections are the
`Q_(i,a,t)`.  The standard conversion has two types of contexts.

First, for every question `i` it has the one-hot relation on all
`x_(i,a,t)`.  Faithfulness and `(TLS4)` show that its tracial support is

```text
{ e_(a,t) : P_(i,a) != 0 }.                              (TLS5)
```

The affine hull of `(TLS5)` sets the zero coordinates to zero and imposes the
single odd-parity equation on the remaining coordinates.

Second, for every rejected pair it has a two-bit NAND context.  Put

```text
Q=Q_(i,a,t),       R=Q_(j,b,u).                          (TLS6)
```

The rejection relation gives `QR=0`.  If `Q` and `R` are nonzero, faithfulness
gives positive trace to their active atoms.  It also gives

```text
tau(1-Q-R)>0.                                            (TLS7)
```

Indeed, when `t=u`, the projection `1 tensor (1-e_t)` lies below `1-Q-R`;
when `t!=u`, the unused third label projection `1 tensor e_v`,
`v notin {t,u}`, lies below it.  Thus the NAND support is exactly
`{00,10,01}`, whose affine hull is all of `F_2^2`.  If exactly one of `Q,R`
is zero, the support is respectively `{00,01}` or `{00,10}` and its affine
hull merely fixes the zero coordinate.  If both vanish, both coordinates are
fixed to zero.  Hence no NAND context gives a relation between two nonzero
answer coordinates.

For each question choose any `a_i` with `P_(i,a_i)!=0`, which exists by
`(TLS1)`, and set

```text
x_(i,a_i,0)=1,       x_(i,a,t)=0 otherwise.             (TLS8)
```

This obeys every zero-coordinate equation and every odd-parity row described
above.  It is therefore a classical solution of the affine-support system.
The commutation ancillas in `finite-linear-commutation-system-to-lcs` extend
scalarly, so `(TLS8)` is also a perfect classical strategy for `L_tau`.

---
rg: 2
id: kun-thom-compression-survives-amenable-near-model
kind: claim
title: The Kun--Thom strict compression occurs in an essentially free amenable genuine representation
distinct_from:
  hyperlinear-near-representation-criterion: That is the abstract equivalence between hyperlinearity and free amenable near representations; this constructs the relevant witness explicitly on the residually finite Kun--Thom actor and computes its compressed fixed spaces.
  near-representation-amenability-dichotomy: That asks for some finite-dimensional remnant of an amenable near representation; this shows that bare finite-dimensional remnants can all have zero charge and therefore cannot see the compression.
  normal-closure-fixes-gamma-fixed-algebra: That is a rigidity theorem for diagonal algebras in sofic permutation ultraproducts; this proves why an arbitrary Kahl--Schneider basis charge supplies no analogous diagonal algebra.
  macroscopic-child-only-adjoint-sector-is-terminal: That consumes a positive-density adjoint excess; this countermodel makes the entire fixed projection charge-null.
---

**ESTABLISHED COUNTERMODEL TO THE COMPRESSION-ONLY ROUTE.**  Let
`Gamma<G` be the explicit Kun--Thom Theorem E pair and choose a strict
compressor

```text
t Gamma t^(-1) < Gamma.                                  (KNA1)
```

There are a Hilbert space `H`, an orthonormal basis `X`, a probability charge
`mu` on `P(X)`, and a **faithful genuine representation**

```text
pi:G -> U(H)                                               (KNA2)
```

with all of the following properties.

1. `mu_bullet` is `pi(G)`-invariant.  Hence `pi` is an amenable
   `mu`-near representation in the sense of Kahl--Schneider; in fact its
   multiplicativity defect is identically zero.
2. It is essentially free for `mu`:

   ```text
   mu({x: |<x,pi(g)x>|<=epsilon})=1
                  for g!=1 and every epsilon>0.            (KNA3)
   ```

3. Faithfulness retains the strict subgroup inclusion

   ```text
   pi(t Gamma t^(-1)) < pi(Gamma),                         (KNA4)
   ```

   but their Hilbert fixed spaces are exactly equal:

   ```text
   H^(pi(t Gamma t^(-1)))=H^(pi(Gamma)),
   pi(t) H^(pi(Gamma))=H^(pi(Gamma)).                      (KNA5)
   ```

4. If `P_Gamma` is the common fixed-space projection in `(KNA5)`, then

   ```text
   mu_bullet(P_Gamma)=0.                                   (KNA6)
   ```

Thus amenability of a near unitary representation does not turn the strict
infranormal compression into a positive-charge child-only sector.  It is
compatible even with an exact, faithful representation and an essentially
free charge.

## Construction

The Kun--Thom actor `G` is finitely generated, infinite and residually finite.
Choose a descending residual chain of finite-index normal subgroups
`N_n normal G` with trivial intersection, put `F_n=G/N_n`, and let

```text
H=directSum_n ell^2(F_n),
X=disjointUnion_n F_n,
pi=directSum_n lambda_(F_n) o q_n.                         (KNA7)
```

For a nonprincipal ultrafilter `omega`, define

```text
mu(A)=lim_(n->omega) |A intersect F_n|/|F_n|.              (KNA8)
```

Left translations preserve each uniform measure, so `mu_bullet` is exactly
`pi(G)`-invariant.  The residual chain makes `pi` faithful and makes
`q_n(g)!=1` eventually for every `g!=1`; a nonidentity left translation has
zero diagonal, proving `(KNA3)`.

Put `Gamma_n=q_n(Gamma)`.  In every finite quotient,

```text
q_n(t) Gamma_n q_n(t)^(-1) <= Gamma_n.                    (KNA9)
```

The two finite subgroups in `(KNA9)` are conjugate and hence have the same
cardinality, so equality holds.  Their fixed projections on `ell^2(F_n)`
are therefore the same Reynolds projection

```text
P_n=|Gamma_n|^(-1) sum_(h in Gamma_n) lambda_(F_n)(h),     (KNA10)
```

and `q_n(t)` normalizes its range.  Taking direct sums proves `(KNA5)`.
The abstract inclusion remains strict by faithfulness, proving `(KNA4)`.
Finally

```text
mu_bullet(directSum_n P_n)
  =lim_(n->omega) tr_(F_n)(P_n)
  =lim_(n->omega) 1/|Gamma_n|=0,                           (KNA11)
```

because `Gamma` is infinite and the residual chain separates it.  This is
`(KNA6)`.

Every finite-dimensional subrepresentation returned by the
Bekka--Valette theorem can likewise be supported on a finite-rank projection,
and every finite-rank projection has `mu_bullet`-mass zero in this model.
Therefore a bare near-representation analogue of “there exists a nonzero
finite-dimensional subrepresentation” would not close the charge argument;
one needs a **positive-charge** or Cartan-visible conclusion.

## Exact remaining interface

This is not an amenable near representation of the Kun--Thom wreath or of
the double, and proves neither group hyperlinear.  It rules out only the
attempt to derive a contradiction from the actor compression and charge
amenability alone.  A successful Kahl--Schneider proof must use the lamp
relations to recover a `mu`-visible abelian/Cartan algebra on which the actor
acts classically.  Kahl--Schneider invariance of `mu_bullet` does not provide
that: their unitaries may mix the basis and need not normalize its diagonal
masa.  This is exactly the separate `invariant-cartan-completion` gate.

Proof: `residual-finite-compression-near-model-proof`.

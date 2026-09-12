---
rg: 2
id: stabilizer-checks-either-have-logical-shears-or-erase-payload
kind: claim
title: Finite stabilizer checks either admit an exact logical shear or carry no intrinsic payload
distinct_from:
  expander-parity-checks-have-dense-clifford-shears: that gives an explicit dense codeword shear fixing a CSS parity family and a named transverse chart; this identifies the exact normalizer boundary for every finite stabilizer check space.
  generator-column-pauli-test-globalizes-but-does-not-pin-sites: that concerns recovery of a growing Pauli factor up to global conjugacy; this works inside one already exact finite stabilizer sector and classifies when check-only incidence can constrain its logical payload.
  finite-clifford-couplings-cannot-prune-a-forbidden-atom: that studies fixed controlled-Clifford predicate couplings on finite BCS atoms; this is the check-algebra normalizer dichotomy before any nonlinear predicate is coupled.
---

Let `V=F_2^(2n)` with its standard symplectic form `omega`, and let
`P(v)` be an irreducible `n`-qubit Pauli packet.  A finite stabilizer/CSS
check gadget is an isotropic subspace `R<=V`; choose a joint check character
whose spectral projection `p` is nonzero.  Put

```text
k=n-dim(R),             L=R^perp/R.                       (SCB1)
```

The quotient `L` is nondegenerate symplectic of dimension `2k`, and the
selected carrier has the canonical form

```text
pH = C^(2^k) tensor K,                                   (SCB2)
```

where `K` is the representation multiplicity.  The intrinsic logical Pauli
algebra is `M_(2^k)(C) tensor 1_K`.

If `k>0`, choose `ell,m in R^perp` whose classes obey
`omega(ell,m)=1`.  On `pH`, let

```text
Q=P(ell),             M=P(m),             W=exp(pi i Q/4). (SCB3)
```

Then `W` commutes with every stabilizer check, so all syndrome/check defects
remain exactly zero, while

```text
W M W*=iQM,                 ||WMW*-M||_(2,p)=sqrt(2).      (SCB4)
```

Here `||.||_(2,p)` is normalized by the trace of `p`.  The norm identity is
exact: `Q` and `M` anticommute, and the normalized logical trace of the
nonidentity Pauli `Q` is zero.  Thus every check-only gadget which retains
even one logical qubit has a constant-size coherent logical motion invisible
to **all** of its checks.  Adding more redundant checks, improving distance,
or proving stronger LTC soundness for the same stabilizer subgroup cannot
remove `(SCB3)`.

Conversely, the logical Pauli normalizer quotient is trivial exactly when

```text
R^perp/R=0,             equivalently dim(R)=n.             (SCB5)
```

Then `k=0` and the selected irreducible Pauli carrier is one-dimensional:
the checks have erased every intrinsic quantum payload.  In a nonirreducible
representation `(SCB2)` may still contain `K`, but the checks act as scalars
on `K` and authenticate none of it.  They have not protected a payload;
they have moved it into a completely free multiplicity reservoir.

Therefore the exact stabilizer-code boundary is:

```text
nontrivial authenticated logical carrier
    => exact zero-syndrome logical gauge,

no logical gauge
    => no intrinsic Pauli payload.                         (SCB6)
```

This does not say fault-tolerant verification is impossible.  It says its
missing ingredient cannot be a stronger linear code property.  A compiler
must couple the computation to relations outside the stabilizer check
algebra.  The clean option is a gauge-covariant nonlinear verifier: transport
the payload and its predicate through the same logical gauge, and make the
predicate detect failure only through gauge-invariant joint incidence.
Alternatively one may add a transverse family generating the logical matrix
algebra, but then the payload coupling—not stabilizer distance or local
testability—is doing the pinning.


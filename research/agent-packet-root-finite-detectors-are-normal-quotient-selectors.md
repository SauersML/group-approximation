---
rg: 2
id: agent-packet-root-finite-detectors-are-normal-quotient-selectors
kind: claim
title: Every finite packet-to-root displacement gadget is only a normal-quotient selector
distinct_from:
  agent-a4-bridge-transfers-forbidden-mass-but-stops-at-root-kill: That transfers a Reynolds projection to two literal order-three displacements but loses the intended perfect coefficient model; this classifies every finite overgroup or finite induction gadget proposed to repair that coupling.
  agent-pk-affine-ghost-survives-quotient: That exhibits an affine ghost for one projective-kernel quotient; this gives the general representation-theoretic reason that finite packet phases can only remove quotient-compatible type sets.
  agent-first-hit-scalar-or-projective-phase-dichotomy: That classifies scalar versus Schur phases in first-hit transport; this includes arbitrary finite projective extensions and representation-induction detectors through the regular representation of their root-killed quotient.
---

Let `H` be a finite packet group, let `q in C[H]` be a nonzero orthogonal
projection, let `K` be a finite group containing `H`, and let `z in K` have
fixed odd order.  Put

```text
N=H intersect <<z>>_K,        Q=K/<<z>>_K.             (FDS1)
```

The following are equivalent.

1. There is `C<infinity` such that every finite-dimensional unitary
   representation `rho` of `K` satisfies

   ```text
   tr(rho(q)) <= C ||rho(z)-1||_2^2.                  (FDS2)
   ```

2. The image of `q` under the quotient map

   ```text
   C[H] -> C[H/N]                                    (FDS3)
   ```

   is zero.

Thus a finite overgroup, a finite representation-induction bridge, or a
finite projective-phase cell can force packet mass into root displacement
only when setting the root equal to `1` already kills `q` by an ordinary
normal quotient of the packet.  It cannot recognize an arbitrary physical
simple block which merely happens to have zero mass in one designated
perfect trace.

The obstruction is the regular representation of `Q`.  Its restriction to
`H/N` is `[Q:H/N]` copies of the regular representation.  Hence it contains
every `H/N`-type.  If `(FDS3)` does not kill `q`, this gives an exact finite
representation with

```text
rho(z)=1,                 tr(rho(q))>0,                (FDS4)
```

contradicting every proposed displacement inequality.  Equivalently,
Frobenius reciprocity says that every `H/N`-irrep occurs in the restriction
of some `Q`-irrep; no finite overgroup can simply omit a selected surviving
packet type.

Conversely, if `(FDS3)` kills `q`, every irreducible `K`-representation in
which `z=1` kills `q`.  There are finitely many remaining irreducibles, and
the maximum of

```text
tr(sigma(q))/||sigma(z)-1||_2^2
```

over them is finite.  Direct-sum decomposition proves `(FDS2)`.  Fixed
finite-group HS correction gives the approximate version of `(FDS2)` with a
dimension-independent presentation-error term.

There is a matching perfect-model obstruction.  Any exact representation
with `z=1` factors on `H` through `H/N`.  Hence a proposed perfect packet
representation can extend with `z=1` only if it kills `N`.  If that packet
representation is faithful on `H` and `q!=0`, then `N=1`, `(FDS3)` is
impossible, and no finite detector exists.

For an arbitrary finitely presented infinite mixed cell `Gamma`, the same
argument gives the necessary condition

```text
every finite-dimensional representation of
Gamma/<<z>> kills q.                                  (FDS5)
```

If the quotient is finite, RFD relative to `H`, virtually free, or has a
finite quotient retaining `q`, it fails.  Escaping the theorem therefore
requires a genuinely infinite non-RFD quotient in which a nonzero packet
projection is already finite-dimensionally invisible.  That is not a
finite-detector construction; it recreates the BCL/Toeplitz residual before
the desired normalized-HS estimate has been proved.

There is also a precise positive boundary, which shows why ordinary Kazhdan
machinery does not evade the quotient condition.  Suppose

```text
N=<<z>>_Gamma
```

has property `(T)`, and let `s_1,...,s_r` be a finite Kazhdan set for `N`.
Write each `s_j` as a product of at most `ell` conjugates of `z` and `z^-1`.
If `q` is zero in the full group algebra of the root-killed quotient, then
every finite-dimensional unitary representation satisfies

```text
tr(rho(q)) <= (r ell^2/kappa) ||rho(z)-1||_2^2,        (FDS6)
```

where `kappa` is the squared Kazhdan constant.  Indeed, the `N`-fixed
projection is `Gamma`-invariant and is killed by `q`; apply the Kazhdan
inequality to an orthonormal basis of `Ran rho(q)` and use

```text
||rho(s_j)-1||_2 <= ell ||rho(z)-1||_2.
```

Thus a property-`(T)` normal closure can robustify an **algebraic** quotient
selector, but it cannot turn trace-specific vanishing of `q` into a selector.
To exploit a genuinely infinite non-RFD quotient where `q` is killed only by
finite-dimensional representations, one needs a finite-dimensional-only
spectral gap not supplied by ordinary property `(T)`.  This is exactly the
missing normalized-HS rigidity, now expressed without packet bookkeeping.

In particular, the newly isolated coupling

```text
physical q mass -> displacement of x(q)
```

cannot be supplied by any finite packet overgroup, induction table, or
finite Schur/projective phase unless the perfect support is already cut out
by an ordinary packet quotient.  Nonlinear BCS supports are precisely the
case where that quotient condition generally fails.

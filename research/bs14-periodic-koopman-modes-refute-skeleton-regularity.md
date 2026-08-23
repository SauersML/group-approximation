---
rg: 2
id: bs14-periodic-koopman-modes-refute-skeleton-regularity
kind: claim
title: Exact BS14 packets have arbitrarily slow regular Koopman modes
distinct_from:
  bs14-full-commutant-finite-period-preconditioner: that perturbs an arbitrary exact skeleton to bounded-period data with a dimension-dependent inverse bound; this constructs exact long-period packets and proves no dimension-free inverse exists before using the Iwahori relations.
  weyl-defect-koopman-spectral-regularity: that asks whether the projected defect of a full approximate arithmetic tuple avoids these modes; this proves the BS skeleton and its canonical trace data alone do not force that avoidance.
---

**ESTABLISHED PERIODIC FIREWALL.**  For every `L>=2`, put

```text
N=4^L-1,                    omega=exp(2 pi i/N).        (BKM1)
```

On `C^L`, with indices modulo `L`, define

```text
V e_j=omega^(4^j)e_j,       H e_j=e_(j-1).             (BKM2)
```

The `V`-eigenvalues are distinct and

```text
H V H^(-1)=V^4.                                        (BKM3)
```

Thus `(H,V)` is an exact finite-dimensional `BS(1,4)` packet.  Its base
commutant `Z={V}'` is the diagonal algebra, and `psi=Ad(H)` cyclically shifts
its `L` coordinates.

Let `zeta=exp(2 pi i/L)` and let

```text
c=diag(1,zeta,zeta^2,...,zeta^(L-1)).                  (BKM4)
```

Then `c` is orthogonal to the fixed algebra, `||c||_2=1`, and, up to shift
orientation,

```text
psi(c)=zeta c,
phi=(1-psi)c=(1-zeta)c,
||phi||_2=|1-zeta|<=2 pi/L.                            (BKM5)
```

The minimum-norm solution of `(1-psi)x=phi` is `x=c`.  Equivalently its
Koopman weighted norm is exactly

```text
sum_lambda |hat phi(lambda)|^2/|1-lambda|^2=1.         (BKM6)
```

Therefore no dimension-free estimate of the form

```text
||(1-psi)^(-1)phi||_2<=C||phi||_2                      (BKM7)
```

holds on the regular sector of exact BS skeletons.  An orthogonal direct sum
of packets with `L->infinity` has unbounded inverse on the closure of the
finite-stage regular sectors: eigenvalue one lies in its approximate
spectrum.  Pure-point accumulation already defeats the estimate; a diffuse
model is not needed.

This is stronger than a warning about arbitrary cyclic shifts: `(BKM1)--
(BKM3)` realize every bad shift inside the explicit odd fourth-power orbit
dynamics used by the Iwahori lane.  Hence neither exact BS
exactification, atomless limiting base spectrum, Parseval, nor the label
lacunarity can imply `weyl-defect-koopman-spectral-regularity`.

The construction does **not** refute the full arithmetic claim, because it
does not realize `phi` as the projected Weyl defect of a tuple satisfying the
involution and both Iwahori cubic relations with comparable error.  Those
three non-amenable relations are the only possible source of the missing
mode suppression.

In particular the Ruelle--Perron--Frobenius slogan must not be interpreted as
an `L^2` spectral gap on the regular sector.  The gap is available only in a
stronger regularity norm.  Proving that the arithmetic defect belongs to that
regularity class is exactly the unresolved theorem.

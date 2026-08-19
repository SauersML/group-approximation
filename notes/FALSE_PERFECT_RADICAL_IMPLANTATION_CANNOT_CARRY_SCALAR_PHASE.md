# Perfect radical implantation cannot carry the scalar Clifford phase

Date: 2026-08-13

## Outcome

The MF-radical implantation construction and the existing Connes-embeddable
Clifford detector cannot be spliced in the most direct way.  The obstruction
is purely algebraic.

Let `A` be a perfect group, let `a in A` normally generate `A`, and let

```text
f : A -> M
```

be a group homomorphism.  If `f(a)` is central in `M`, then `f` is trivial.
To see this, compose `f` with the quotient map

```text
M -> M / Z(M).
```

The composite kills `a`, so normal generation makes the composite trivial.
Thus `f(A)` lies in `Z(M)` and is abelian.  But a homomorphic image of a
perfect group is perfect, so `f(A)` is trivial.

The reusable statement is kernel-checked in
`GroupApproximation/Sofic/NormallyGeneratedMFObstruction.lean` as

```text
hom_eq_one_of_isPerfect_of_map_normalGenerator_mem_center.
```

## Application to the `PSL(2,13)` implantation

The credited arithmetic input remains
[`eekarabiyik/SL2F13`](https://github.com/eekarabiyik/SL2F13/tree/main), as
recorded in `SL2F13_RADICAL_APPLICATION_AUDIT.md`.  Let `a` be an involution
of the perfect simple group `A=PSL(2,13)` and form

```text
H_13 = E *_(<w>=<a>) A.
```

The MF-radical argument is valid: the embedded copy of `A` lies in the MF
radical of `H_13`.  However, the known CE representation of `E` detects the
marked word by the scalar value

```text
w |-> -1.
```

If that representation extended to `H_13`, its restriction to `A` would send
the normal generator `a=w` to the central scalar `-1`.  The theorem above
would make the restriction trivial, forcing `a` to map to `1`, a
contradiction.  Therefore the scalar Clifford detector does not extend
across this amalgam.

## Consequence for the hyperlinear program

This closes a tempting radical-collision shortcut:

```text
MF-radical scalar sign
  + perfect/simple radical implantation
  != CE-visible implanted sign.
```

It does not show that `H_13` is nonhyperlinear.  A hypothetical hyperlinear
detector could represent `a=w` noncentrally in the ambient target while it
remains central relative only to the image of `E`.  What is ruled out is the
specific existing detector in which `w` is the scalar `-1`, and more
generally every central-phase detector.

Accordingly the arithmetic implantation is a valid non-MF application but
does not solve the phase-locking part of the hyperlinear problem.  The active
nonhyperlinear endpoint remains finite-multiplicity recovery of the paired
coefficient radical quotient, where multiplication becomes operator support
rather than an additive character sign.

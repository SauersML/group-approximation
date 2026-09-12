---
rg: 2
id: matrix-ulam-stability-needs-full-unit-ball-control
kind: claim
title: Dimension-free matrix Ulam stability begins after full unit-ball control
artifacts:
  - research/compression-leakage-is-the-unit-ball-defect-proof.md
distinct_from:
  multi-kraus-frame-energy-is-the-full-relative-pd-gate: that identifies the complete relative coefficient body with Kraus-frame energy; this isolates the strictly stronger hypothesis needed to invoke matrix Ulam stability.
  almost-full-hecke-frame-gives-flexible-corner: that fills a corner once an almost-full relative frame is known; this does not produce uniform multiplicativity on a matrix unit ball.
---

Alekseev--Thom, *The hyperfinite II_1-factor is Ulam stable*,
arXiv:2606.07369v1, Definition 2.1 and Theorem 3.5, prove the following
dimension-free matrix theorem. There is a modulus `omega(epsilon)` tending
to zero, independent of `n`, such that a map

```text
phi : M_n(C)_{<=1} -> M_{<=1}
```

which is uniformly `epsilon`-additive, scalar homogeneous, multiplicative,
star preserving, and unital on the whole operator-norm unit ball is
`omega(epsilon)`-close there to a unital star homomorphism after passing to
a finite corner of a semifinite amplification of `M`.

For a unital star homomorphism `pi:M_n(C)->N`, a projection `p in N`, and
the compression `phi_p(x)=p pi(x) p`, every hypothesis except
multiplicativity is exact, while

```text
phi_p(xy)-phi_p(x)phi_p(y)
  = p pi(x) (1-p) pi(y) p.                         (MUS1)
```

Consequently the Alekseev--Thom input for a compression is precisely the
uniform leakage estimate

```text
sup_{||x||,||y||<=1} ||p pi(x)(1-p)pi(y)p||_2 <= epsilon.  (MUS2)
```

A finite list of marked word defects is not a formal substitute for (MUS2).
Already in `M_2(C)`, compression to `p=e_11` is exactly multiplicative on
the diagonal unitary `diag(1,-1)`, but its multiplicative defect at
`x=e_12, y=e_21` has normalized `L2` norm one.

Thus Theorem 3.5 can correct an Iwahori Stinespring compression once a
dimension-free estimate from the concrete presentation defects to the full
unit-ball leakage has been proved. It does not supply that estimate. In
particular, applying it directly to the two marked Iwahori cubics would be
circular. The root remains open.

DERIVATION
compression-leakage-is-the-unit-ball-defect-proof

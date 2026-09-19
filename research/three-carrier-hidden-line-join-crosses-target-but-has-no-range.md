---
rg: 2
id: three-carrier-hidden-line-join-crosses-target-but-has-no-range
kind: claim
title: Three hidden-sign lines cross the target but do not force a one-atom range
artifacts:
  - research/three-carrier-hidden-line-source-selector-proof.md
distinct_from:
  two-carrier-support-join-stays-below-target: that proves the join of two hidden lines remains below capacity; this adds the third nonzero line and constructs a linear combination with full source support.
  qutrit-complementary-jacobson-signs-minimal-router-finite: that recombines four sign quarters in an acyclic finite packet; this uses three C-conjugate mixed S/T carriers containing the long-router occurrence.
---

Extend the covectors from `(TCC1)` by

```text
phi_2=phi_0+phi_1=(0,1),
mathsf U_i=I+T E_(c_3,phi_i),
mathsf Y_i=V mathsf U_i,                 i=0,1,2.       (THL1)
```

Thus `mathsf U_i=k^i mathsf U_0 k^(-i)` and
`mathsf U_0=g_2^2Ug_2^(-2)`. Their hidden signs satisfy

```text
Z_i=I+(qT)E_(v,phi_i),           Z_2=Z_0Z_1.            (THL2)
```

For `tau=+` put

```text
X_i=G_(sigma,+)mathsf Y_iG_(sigma,+),
X=X_0+(1/4)X_1+(1/16)X_2.                              (THL3)
```

Then `X` is bounded below on the whole `G_(sigma,+)` carrier. In
particular,

```text
supp abs(X)=G_(sigma,+).                                (THL4)
```

After the qutrit source cut `R=e_0+e_1` this gives the exact ranks

```text
tau(supp abs(XR))=5/72             if sigma=+,
tau(supp abs(XR))=1/16             if sigma=-.          (THL5)
```

Both cross the target capacity:

```text
5/72-1/18=1/72,               1/16-1/18=1/144.         (THL6)
```

Thus three is the sharp source-selector threshold. The three initial
supports are the three nonzero hidden-sign lines

```text
Z_0=+1,              Z_1=+1,              Z_0Z_1=+1,
```

whose join is the identity on every joint `Z_0,Z_1` sector.

This is not yet a Hall contradiction. For any target atom `e_b`, the
unitarily routed operator `g_2XR` still has the source rank `(THL5)`,
so its range cannot be contained in `Ee_b`, whose trace is `1/18`.
The tautologically target-contained compression

```text
Ee_b g_2 X R
```

must lose at least `1/72` of initial rank in the all-plus row and at
least `1/144` in the other surviving row.

Equivalently, the shortest three-carrier family solves the source-polar
problem but not the range-authentication problem. A nonhyperlinearity
proof now needs an algebraic relation forcing the unwanted qutrit output
atoms to cancel before the target projection. Merely applying the target
cut cannot retain the newly recovered source.

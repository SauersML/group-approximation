---
rg: 2
id: stw81-normalize-unequal-frames-and-drop-heavy-colour
kind: route
title: Normalize the light and heavy returned frames and discard one heavy colour
target: stw81-local-reconstructive-subdivision-forces-af
requires:
  - stw81-projectionless-rotating-overlap-degeneracy
  - stw81-positive-scalar-order-zero-approximation-is-scalar
---

Write

```text
a_i=S_i^0(1_D),                  b_i=S_i^1(1_D),
c=1-gamma,                       d=gamma.
```

These are positive contractions.  Applied to the unit, (LRS2) gives

```text
norm(a_0+a_1-c1)<epsilon,
norm(b_0+b_1-d1)<epsilon.                            (NUR1)
```

In particular,

```text
a_0+a_1<=(c+epsilon)1,
b_0+b_1<=(d+epsilon)1.                               (NUR2)
```

Normalize the two rows by

```text
h_i=a_i/(c+epsilon),             k_i=b_i/(d+epsilon).
```

They are subunital pairs, and their defects from the unit satisfy

```text
norm(1-h_0-h_1)<=2epsilon/(c+epsilon),
norm(1-k_0-k_1)<=2epsilon/(d+epsilon).                (NUR3)
```

Let

```text
eta=max(2epsilon/(c+epsilon),2epsilon/(d+epsilon)).
```

Condition (LRS3) gives `h_i k_i=0`.  Once `eta<1/8`, apply
`stw81-projectionless-rotating-overlap-degeneracy`.  One of `h_0,h_1` has
norm at most

```text
alpha(eta)=(1-sqrt(1-8eta))/2.                       (NUR4)
```

Consequently one first-row map, say `S_i^0`, has norm

```text
norm(S_i^0)=norm(S_i^0(1_D))
 <=(c+epsilon)alpha(eta).                            (NUR5)
```

Here equality of map norm and unit-value norm uses positivity of `S_i^0`.
For every contraction `a in E`, discard this colour and estimate

```text
norm(ca-S_(1-i)^0(a))
 <=norm(ca-(S_0^0+S_1^0)(a))
   +norm(S_i^0(a))
 <=epsilon+(c+epsilon)alpha(eta).                     (NUR6)
```

Here `gamma`, and hence `c=1-gamma>0`, stays fixed.  Letting `epsilon` tend
to zero makes `eta` and the right side of (NUR6) tend to zero.  The
surviving map factors through a finite-dimensional algebra and has a c.p.c.
order-zero return.  Thus `c id_D` has nuclear dimension zero.  Apply
`stw81-positive-scalar-order-zero-approximation-is-scalar` to conclude
`D=C1_D`.

We check the subdivision reduction.  Suppose an original incoming map has
coordinates `psi_i^r:D->F_i^r`, and its outgoing colour `phi_i^r` is
replaced by finitely many order-zero maps

```text
theta_(i,s)^r:F_i^r->D.
```

Send `a` to the tuple containing one copy of `psi_i^r(a)` for every `s`.
This diagonal repetition into a direct sum remains c.p.c. because the norm
on the direct sum is the maximum of the coordinate norms.  For each global
label, sum the corresponding `theta_(i,s)^r`.  Same-label orthogonality
makes this direct-sum return c.p.c. order zero.  Separate reconstruction of
the original chart gives (LRS2), while orthogonality between same-labelled
pieces from the two charts gives (LRS3).  The number of copies never enters
(NUR1)--(NUR6).

For base-dependent scalar or operator cutdowns, perform this regrouping in
the section algebra and then evaluate at a transition point.  Evaluation is
a star homomorphism, hence preserves complete positivity, contractivity,
order zero, and same-label orthogonality.  Thus arbitrary finite subdivision
depth at each approximation stage is covered.

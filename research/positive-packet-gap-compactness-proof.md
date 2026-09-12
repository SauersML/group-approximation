---
rg: 2
id: positive-packet-gap-compactness-proof
kind: route
title: Center positive packet witnesses on unit-zero maps and pass only a persistent gap
target: positive-packet-witness-gap-endpoint
requires:
  - ideal-block-infeasibility-has-positive-reservoir-witness
---

Let `s:E->A` be a ucp lift.  Then

```text
h=t-s in L_sa(E,I),       h(1)=0.                         (1)
```

Because `E` is finite-dimensional and the union of the `L_m` is dense in
`I`, choose self-adjoint maps

```text
d_m:E->L_m,       d_m(1)=0,       ||d_m-h||->0.            (2)
```

Central compression of a cp map is cp, so

```text
theta_m=z_m rho_m s in UCP_(z_m)(E,J_m).                  (3)
```

Use `(PGC3)`, then subtract the reservoir direction `rho_m d_m`, which is
annihilated by `(PGC2)`:

```text
gamma_m
 <=Omega_m(z_m rho_m(t-s))
 = Omega_m(z_m rho_m(h-d_m))
 <= C ||h-d_m|| ->0.                                     (4)
```

This proves `(PGC4)` directly.  In particular a nonvanishing gap contradicts
a ucp lift; no vector extraction is required.

For the explicit quotient separator, suppose along a subsequence, still
indexed by `m`, that `gamma_m>=gamma>0`.  On the fixed real Banach space

```text
X_0={k in L_sa(E,A):k(1)=0}
```

define

```text
ell_m(k)=Omega_m(z_m rho_m k).                            (5)
```

The maps `z_m rho_m` are contractive star homomorphisms into `J_m`, hence
`||ell_m||<=C`.  If `k:E->L_m` and `k(1)=0`, `(PGC2)` gives `ell_m(k)=0`.
Moreover, for every `phi in UCP(E,A)`, central compression gives an element
of `UCP_(z_m)(E,J_m)`, so

```text
ell_m(t-phi)>=gamma_m>=gamma.                             (6)
```

Take a weak-star cluster point `ell` of `(ell_m)`.  Every fixed unit-zero map
into `L_k` is killed by the whole tail, so density gives

```text
ell(k)=0       for every k:E->I with k(1)=0.              (7)
```

Equation `(6)` survives the limit.  Thus `ell` descends through the quotient
of `X_0` by its ideal-valued subspace and is at least `gamma` on `t-phi` for
every ucp `phi`.  An exact lift would make one such difference ideal-valued,
contradicting `(7)`.  This is the claimed quotient obstruction.

Notice what was and was not retained.  Positivity of `Omega_m` was essential
for obtaining the packet-dimension-independent norm bound in the prerequisite,
but after restricting to unit-zero differences and passing through moving
targets `J_m`, the invariant limit is the bounded separator `(7)`, not a
positive functional on one fixed Choi algebra.  The only additional invariant
is the scalar gap.

It remains to verify the sharpness example.  A ucp map `theta:C^2->M_2` is
specified by an effect

```text
P=theta(delta_1), theta(delta_2)=I_2-P, 0<=P<=I_2.        (8)
```

For `T+v_c` the first effect would be

```text
diag(2+c,-1+c).
```

Positivity requires `c>=1`, whereas the upper bound by `I_2` requires
`c<=-1`; hence the affine slice is empty.  Formula `(PGC8)` is nonnegative
on cp maps because both coordinate images of a cp map out of `C^2` are
positive.  It annihilates `(PGC7)`, and

```text
Omega(T)=2+2=4,
Omega(theta)=P_11+(I_2-P)_22=1+P_11-P_22<=2.
```

The upper bound is attained by `P=diag(1,0)`.  Finally `(PGC10)` is immediate.
This proves both the compactness endpoint and the claimed impossibility of a
positivity-only soft-vector extraction.

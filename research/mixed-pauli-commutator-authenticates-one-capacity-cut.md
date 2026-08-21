---
rg: 2
id: mixed-pauli-commutator-authenticates-one-capacity-cut
kind: claim
title: One mixed Pauli commutator exactly authenticates one capacity cut
distinct_from:
  canonical-root-coordinate-is-binary-not-an-l2-authenticator: that shows an independently named root cannot authenticate the analytic row; this adds the smallest mixed relation identifying the root with the actual same-reservoir commutator.
  orthogonal-hecke-row-packs-common-source-energy-into-one-root: that treats the full multi-context row with arbitrary covariance defects; this proves the exact one-involution/one-covariance component identity which kills the CRB12 decoupled-factor model.
  global-covariance-misses-capacity-compression: that shows uncompressed covariance leaves an uncontrolled capacity commutator; this names that commutator itself as the root coordinate and computes its exact energy.
---

Let `X,Z` be self-adjoint unitaries and put

```text
Q=(I+X)/2.                                               (MPC1)
```

Thus `Q` is the positive capacity cut of `X`.  Introduce one unitary root
coordinate `Y` and the genuinely mixed word

```text
r_mix=Y^(-1) X Z X Z.                                   (MPC2)
```

The relation `r_mix=1` says only

```text
Y=[X,Z]=XZXZ.                                           (MPC3)
```

It does **not** set either side equal to the identity.  This one relation is
the smallest same-reservoir repair of the decoupled Pauli/root model in
`canonical-root-coordinate-is-binary-not-an-l2-authenticator`.

## Exact authentication identity

### Theorem

For every finite tracial von Neumann algebra, and in particular for every
finite matrix algebra,

```text
||ZQ-QZ||_2^2
 =1/4 ||XZXZ-I||_2^2.                                  (MPC4)
```

Consequently, if `(MPC3)` holds exactly, then

```text
||ZQ-QZ||_2^2=1/4||Y-I||_2^2.                          (MPC5)
```

Without assuming the mixed relation exactly,

```text
||ZQ-QZ||_2^2
 <=1/2||Y-I||_2^2+1/2||r_mix-I||_2^2.                  (MPC6)
```

The constants are independent of matrix dimension and no source/range
rounding is involved.

### Proof

Since `X=X^*=X^(-1)` and `Z=Z^*=Z^(-1)`,

```text
ZQ-QZ=(ZX-XZ)/2.                                       (MPC7)
```

Writing `c=XZXZ`, direct multiplication and tracial cyclicity give

```text
4||ZQ-QZ||_2^2
 =2-2 Re tau(c)
 =||c-I||_2^2,                                         (MPC8)
```

which is `(MPC4)`.  Under `(MPC3)` this is `(MPC5)`.  In general,

```text
||c-I||_2
 <=||c-Y||_2+||Y-I||_2
 =||r_mix-I||_2+||Y-I||_2.
```

Squaring and using `(a+b)^2<=2a^2+2b^2` proves `(MPC6)`.  ∎

The exact constant `1/4` in `(MPC5)` is optimal: equality is the identity,
not an estimate.

## The CRB12 model is no longer decoupled

Take the extraspecial Pauli group

```text
E_1=<X,Z,J | X^2=Z^2=J^2=1, J central, [X,Z]=J>
```

in its left regular representation.  Then

```text
Y=J,
Q=(I+X)/2,
||ZQ-QZ||_2^2=1/2,
||Y-I||_2^2=2.                                         (MPC9)
```

Thus `(MPC5)` holds exactly.  The old construction is no longer a
countermodel to authentication: its leakage is recorded, at the correct
scale, by the nontrivial root coordinate `Y`.

At the same time `(MPC9)` is the essential regular-witness firewall.  The
mixed relation does not force `Y=1` and does not force `Q` to commute with
`Z` in an infinite, regular, or arbitrary tracial representation.  It only
prevents the root coordinate from being placed on an independent tensor
factor while the capacity commutator lives elsewhere.

## HALT firewall

If the capacity cut vanishes in an exact HALT extension, then

```text
Q=0,             X=-I.
```

For arbitrary `Z`,

```text
[X,Z]=I.
```

Hence the mixed cell extends with `Y=I` and imposes no condition on `Z`.
The cell is therefore vacuous on a vanished capacity cut in precisely the
required sense.

More generally, if the construction is supported on a packet corner, one
must first represent that corner cut by the positive spectral projection of
the supported involution `X`; replacing it by an unrelated analytic
projection reintroduces the CRB12 decoupling.

## Composition with a finite-dimensional root breaker

Suppose a separate theorem, valid only for canonical finite-matrix
microstates, gives

```text
||Y(U_n)-I||_2^2<=K_root E_root(U_n)+o(1).              (MPC10)
```

Then `(MPC6)` immediately yields

```text
||ZQ-QZ||_2^2
 <=(K_root/2)E_root+(1/2)||r_mix-I||_2^2+o(1).          (MPC11)
```

This is the desired finite-dimensional-only conclusion after composition:
the mixed cell performs exact source authentication, while `(MPC10)` alone
is responsible for distinguishing matrices from the surviving regular or
properly infinite witness.

It is important not to add `Y=1` as a universal relator.  Doing so combines
with `(MPC3)` to impose `[X,Z]=1` in every representation, including the
regular witness.  The mixed relation and the finite-dimensional root breaker
must remain logically separate.

## Compatibility with a characteristic-two Steinberg root

In characteristic two, a Steinberg root coordinate has order two.  The local
packet

```text
Y^2=1,       [Y,X]=[Y,Z]=1,       Y=XZXZ              (MPC12)
```

is exactly the `D_8` Pauli presentation, so there is no local torsion or
centrality obstruction to taking `Y=x_12(r)` and adjoining `(MPC2)` as an
ordinary mixed group relator.  Whether a chosen full `St_5` coefficient
presentation admits the required exact global completion is a separate
embedding question; the minimal cell itself is consistent and has the
explicit regular model `(MPC9)`.

## Finite universal cells cannot do the second job

The mixed cell solves authentication, not root collapse.  If one tries to
make the entire actuator a finite group and asks every finite-dimensional
representation to kill `Y`, its left regular representation is a faithful
finite-dimensional representation and therefore forces `Y=1` algebraically.
So no finite universal packet can simultaneously

```text
authenticate the leakage,
kill Y in every finite matrix representation,
and retain Y in an exact regular witness.               (MPC13)
```

The second job needs an infinite actuator and a genuinely
finite-dimensional-only multiplicity/capacity theorem.  This is exactly the
proper division of labor suggested by `(MPC11)`.

## Attempts

- **Use `[X,Z]=1` directly.**  By `(MPC4)` this kills the leakage, but it also
  kills it in the regular witness.  It fails the exact-witness firewall.
- **Keep an independent root coordinate.**  The exact product countermodel
  in `canonical-root-coordinate-is-binary-not-an-l2-authenticator` then has
  root defect zero and leakage energy `1/2`.  Relation `(MPC2)` is the
  minimal coupling which excludes that separation.
- **Make the whole mixed cell finite and demand finite-dimensional root
  collapse.**  The finite group's left regular representation is faithful,
  proving `(MPC13)`.  The root-collapse backend must be infinite and
  matrix-only.
- **Apply the identity to the full OHR row.**  The general defects
  `a_jV_j^*Q-V_j^*QZ_j` are not commutators of one involution with its
  spectral cut.  `(MPC4)` closes the CRB12 one-cut obstruction but does not
  by itself authenticate the arbitrary block row `R_Q`.

## Verdict

The smallest genuinely mixed repair exists and is exact:

```text
Y=[X,Z]
quadruple-right-arrow
||[Z,(I+X)/2]||_2^2=1/4||Y-I||_2^2.                   (MPC14)
```

It has the correct HALT behavior and retains the regular `D_8` leakage
witness with `Y` nontrivial.  It eliminates CRB12 as a decoupling
countermodel.  It does not solve non-hyperlinearity: the remaining theorem
is now cleanly the finite-dimensional-only collapse of the authenticated
root `Y`, not another source-alignment estimate.

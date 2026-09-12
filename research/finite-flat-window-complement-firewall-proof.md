---
rg: 2
id: finite-flat-window-complement-firewall-proof
kind: route
title: Hide one coefficient beyond the finite window and apply Stinespring commutant lifting
target: finite-flat-window-does-not-force-complement-lift
requires:
  - exact-projective-codensity-has-a-uniform-trace-square-gap
---

First record the exact commutant-lifting criterion.  Let

```text
K=span closure {pi(g)PH:g in G}.
```

If `U` commutes with every `Ppi(g)P`, define on the algebraic cyclic span

```text
Uhat(sum_i pi(g_i)xi_i)=sum_i pi(g_i)Uxi_i.             (FCP1)
```

The Gram matrix of the left input is

```text
<xi_i,Ppi(g_i^(-1)g_j)P xi_j>_(i,j).
```

Commutation of `U` with every compressed coefficient makes `(FCP1)`
well-defined and isometric.  The same construction with `U*` proves it is
unitary.  It commutes with `pi(G)`, sends `PH` onto itself, and restricts to
`U`; hence it is `U direct_sum Z`.  The converse follows by compressing the
commutation identity.  This proves `(FCI6)<->(FCI7)`.

Now fix finite `F`.  Choose an infinite-order `k in C` with

```text
{k,k^(-1)} disjoint F.                                  (FCP2)
```

Residual finiteness of `A` gives a finite quotient `q:A->Q` in which

```text
q(f) notin {1,q(k),q(k)^(-1)}       (f in F),
q(k)^2!=1.                                               (FCP3)
```

On `ell^2(Q)` put

```text
i e_1=delta_1,       i e_2=delta_(q(k)).                (FCP4)
```

Then

```text
i*lambda(q(f))i=0                         (f in F),
i*lambda(q(k))i=E_21.                                  (FCP5)
```

Let

```text
pi_0(g)=I_2 direct_sum lambda(q(g)),
V xi=sqrt(t)xi direct_sum sqrt(1-t)i xi.                (FCP6)
```

The map `V:C^2->C^2 direct_sum ell^2(Q)` is an isometry, and its compressed
coefficient kernel is

```text
Phi(g)=V*pi_0(g)V=tI_2+(1-t)i*lambda(q(g))i.            (FCP7)
```

Thus `Phi(f)=tI_2` for `f in F`, while

```text
Phi(k)=tI_2+(1-t)E_21.                                  (FCP8)
```

For `U_0=diag(1,-1)`, every named coefficient and polar factor commutes
with `U_0`, but `(FCP8)` does not.  The commutant-lifting criterion therefore
forbids a complement lift.

For canonical camouflage, take exact finite quotient regular
representations `r_n:A->U(L_n)` whose characters converge pointwise to
the canonical character, put `rho_n=I_2 tensor r_n` on `C^2 tensor L_n`,
and tensor the construction:

```text
Pi_n=pi_0 tensor r_n,
P_n=(VV*) tensor I,
U_n=(VU_0V*) tensor I.                                  (FCP9)
```

Under the identification `P_nH_n=C^2 tensor L_n`,

```text
P_nPi_n(g)P_n=Phi(g) tensor r_n(g).                     (FCP10)
```

Equations `(FCI1)--(FCI3)` follow immediately; the retained and ambient
densities are fixed, and `tr(U_n)=0`.

If a finite cyclic shell `W` is prescribed, include every nonidentity
element of `W^(-1)W` in `F`.  Formula `(FCP10)` then computes its complete
Gram matrix: the diagonal entries are the identity and every off-diagonal
entry is `t rho_n(w^(-1)v)`.  Since `U_n` commutes with all of them, the
formula `(FCP1)` gives a well-defined isometry on the entire `W`-shell.
Thus the obstruction is genuinely beyond every prescribed finite depth,
not a failure to synchronize the first boundary layer.

It remains only to verify the uniform floor.  The matrix in `(FCP8)` is
invertible.  Write its polar factor as `R_t`.  Direct two-by-two polar
decomposition gives

```text
R_t=(1/sqrt((1-t)^2+4t^2))
       [[2t, -(1-t)], [1-t, 2t]].                       (FCP11)
```

Consequently `sigma_*` may be taken as the least singular value of
`tI+(1-t)E_21`, and

```text
epsilon_*=1-|tr_2([U_0,R_t])|^2>0.                     (FCP12)
```

Indeed `(FCP11)` is a rotation through an angle strictly between `0` and
`pi/2`, and conjugation by `U_0` reverses that angle; its commutator has
normalized trace `cos(2 theta)`, of modulus strictly below one.

The polar factor in `(FCP10)` at `k` is `R_t tensor r_n(k)`, so its
projective commutator energy with `U_n` is exactly `epsilon_*`.  Apply
`projective-transfer-reduces-to-complement-unitary-extension` with target
`k` (the proof works for every fixed target with its exact transfer
constant `K_k`) to obtain `(FCI5)`.

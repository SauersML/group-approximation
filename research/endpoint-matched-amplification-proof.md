---
rg: 2
id: endpoint-matched-amplification-proof
kind: route
title: Compress the contragredient tensor by the maximally entangled vector
target: endpoint-matched-amplification-is-matrix-range-neutral
requires: []
---

Let `Delta:A->A tensor_max A` be the full group comultiplication,
`Delta(u_g)=u_g tensor u_g`.  Fix a ucp map

```text
Phi:A->M_r tensor M_m.
```

Let `vbar` be the contragredient of `v`, let

```text
Omega=r^(-1/2) sum_i ebar_i tensor e_i,
V:C^m -> Cbar^r tensor C^r tensor C^m,
V xi=Omega tensor xi,
```

and define

```text
Psi(a)=V^* (vbar tensor Phi)(Delta(a)) V.                         (1)
```

Functoriality of the maximal tensor product makes `(1)` ucp.  The standard
maximally-entangled-vector identity gives, for every `g in Lambda`,

```text
Psi(u_g)
 =(tr_r tensor id)((v(g)^* tensor I_m) Phi(u_g)).                 (2)
```

Consequently

```text
 Re sum_s tr_(rm)((v(s) tensor B_s)^* Phi(u_s))
 =Re sum_s tr_m(B_s^* Psi(u_s))
 <=h_m(B).                                                       (3)
```

Taking the supremum over `Phi` proves `h_(rm)(B~)<=h_m(B)`.  Conversely,
for every ucp `Psi:A->M_m`, the map

```text
Phi=(v tensor Psi) circle Delta
```

is ucp and has `Phi(u_s)=v(s) tensor Psi(u_s)`, giving equality in `(3)`.
This proves the support identity.  Also

```text
tr_(rm)((v(s) tensor B_s)^*(v(s) tensor X_s))
 =tr_m(B_s^*X_s),                                               (4)
```

so subtracting the support functions proves the gap identity.  Unitarity of
`v(s)` gives

```text
||v(s) tensor B_s||_2=||B_s||_2,
||v(s) tensor B_s||_op=||B_s||_op.                              (5)
```

For the endpoint statement, let `rho` be any matrix assignment for the
centralizer HNN presentation and let `v` be a genuine representation of
`Gamma`, extended to the HNN generators by `v(t)=I`.  Define

```text
rho~(gamma)=v(gamma) tensor rho(gamma),
rho~(t)=I tensor rho(t).                                        (6)
```

Every relator value in `(6)` is the tensor product of the identity with the
old relator value, so normalized Hilbert--Schmidt defects are unchanged.
Equation `(FER3)` is literal on the first factor, including for generators
outside the overlap.  Apply `(FER2)` to the lattice coordinates and the
matched coefficients `v(s) tensor B_s`.

Finally, for a finite base-word window `W subset Gamma\{1}`, residual
finiteness supplies a finite quotient `q:Gamma->Q` with `q(w)!=1` for every
`w in W`.  Taking `v=lambda_Q circle q` makes
`tr(v(w))=0` on `W` while preserving `(FER2)--(FER3)`.  If a reduced HNN word
has trivial base projection, this argument gives no trace control; indeed
co-density of `Lambda` in finite quotients of `Gamma` forces `q(Lambda)=Q`,
so the amplified stable letter commutes with the entire first-factor base
image.  This is exactly the mixed-Britton firewall stated in the claim.

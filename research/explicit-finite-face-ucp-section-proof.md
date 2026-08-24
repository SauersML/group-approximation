---
rg: 2
id: explicit-finite-face-ucp-section-proof
kind: route
title: Read the finite-quotient averaged section as a Hilbert-module matrix coefficient
target: explicit-finite-face-ucp-section-is-edge-equivariant
requires: []
artifacts:
  - research/artifacts/finite-relator-reservoir-compactness-2026-08-23.md
---

We prove the general statement for a surjection `p:H->>F` with `F` finite.
The triangle instance is obtained by taking `H=E`, `F=P_13`, and `p=q_E`;
the equivalence node supplies that specialization and the two subgroup lifts.

**Complete positivity.**  Let `M:=l^2(F) (x) C^*(H)`, the free right Hilbert
`C^*(H)`-module of rank `|F|`, and let `R` be the right regular representation
of `F` on `l^2(F)`, `R_g delta_x = delta_(x g^(-1))`.  Since `F` is finite,
`R` extends to a faithful unital `*`-homomorphism `C^*(F)->B(l^2(F))`, and
`R (x) 1` is a unital `*`-homomorphism `C^*(F) -> L(M)`.  Put

```text
xi := |F|^(-1/2) sum_(x in F) delta_x (x) u_(sigma(x)) in M. (FFP1)
```

Then `<xi,xi> = 1`, so `xi` is a unit vector, and for `g in F`

```text
(R_g (x) 1) xi = |F|^(-1/2) sum_x delta_(x g^(-1)) (x) u_(sigma(x))
               = |F|^(-1/2) sum_y delta_y (x) u_(sigma(y g)),
<xi,(R_g (x) 1) xi> = |F|^(-1) sum_y u_(sigma(y))^* u_(sigma(y g)),
```

which is `(FF1)`.  Hence `Theta(a)=<xi,(R (x) 1)(a) xi>` for all `a in C^*(F)`,
a compression of a unital `*`-homomorphism by a unit vector of a Hilbert
module -- the Stinespring form -- so `Theta` is completely positive, and unital
because `<xi,xi>=1`.  This proves `(a)`; no lifting theorem is used.

**Section property.**  Apply `p_*` to `(FF1)`.  Since
`p_*(u_(sigma(x)))=u_x`,

```text
p_*(Theta(u_g)) = |F|^(-1) sum_(x in F) u_x^* u_(x g)
                = u_g,
```

which is `(FF2)`.  Note this needs only that `sigma` is a set section; no
positivity is involved.

**Relative equivariance.**  Suppose `L<=F` has a subgroup lift
`L_tilde<=H`, and write `l_tilde` for the unique lift of `l in L`.  Assume
`sigma(xl)=sigma(x)l_tilde`.  For `g in F` and `l in L`,

```text
Theta(u_g u_l) = Theta(u_(g l))
  = |F|^(-1) sum_x u_(sigma(x))^* u_(sigma(x g l))
  = |F|^(-1) sum_x u_(sigma(x))^* u_(sigma(x g)) u_(l_tilde)
  = Theta(u_g) u_(l_tilde),
```

using equivariance at the point `xg`.  Both sides are linear in the second
variable and `C^*(L)` is spanned by its group unitaries, so this is right
module linearity.  Taking `g=1` gives `Theta(u_l)=u_(l_tilde)`.

**Existence of an equivariant `sigma`.**  Choose one `x_i` per right coset
`x_iL`, choose any `sigma(x_i) in p^(-1)(x_i)`, and define
`sigma(x_i l):=sigma(x_i)l_tilde`.  Unique right-coset coordinates make this
well defined, and `p(sigma(x_i)l_tilde)=x_i l`.  Normalize the representative
of `L` so that `sigma(1)=1`.  For the triangle, either `L=P_1` or `L=P_3`.

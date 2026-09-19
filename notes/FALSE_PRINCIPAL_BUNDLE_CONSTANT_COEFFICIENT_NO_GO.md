# Property (T) forces a principal-bundle coefficient defect

Date: 2026-08-11

## 1. Outcome

`FALSE_EXACT_PRINCIPAL_BUNDLE_EXTERNAL_COMPLETION.md` makes the abstract
external `SL_d(Z)` relations exact while prescribing the radical clock
holonomy.  The most direct attempt to add the tangent module would keep the
coefficient operator

`D_k(v) tensor 1_(K_k)`                                `(PCN1)`

constant over the finite external quotient.  That attempt cannot work.

For any fixed Kazhdan generating set of `SL_d(Z)`, some external generator
has a dimension-independent positive normalized Hilbert--Schmidt
commutator with `(PCN1)`.  The reason has two exact parts:

1. property `(T)` forces a positive density of nontrivial fiber holonomies;
2. every nontrivial clock holonomy moves `D_k(e_1)` by squared normalized HS
   distance at least `2` on the primitive coefficient orbit.

Thus the principal-bundle theorem really does close the abstract external
group gate, but its cocycle cannot simply be ignored by the constant
coefficient module.  A successful extension must twist the tangent
characters across the external base so that this cocycle is absorbed, then
prove that the two twists still agree on the fixed positive polynomial
window.

## 2. The clock coordinate on the external quotient

Fix an odd prime `p`.  Put

`M_k=p^k`, `K_k=SL_d(Z/M_k Z)`,                       `(PCN2)`

and let

`t_k=I+e_12`, `s_k=I+e_13`.                           `(PCN3)`

The subgroup `<t_k,s_k>` is `(Z/M_k Z)^2`.  The bundle gauge in the
principal-bundle note may be written

`phi_k(x)=c_k^(-r_k(x))`,                             `(PCN4)`

where

`r_k(t_k x)=r_k(x)+1`,
`r_k(s_k x)=r_k(x)` in `Z/M_k Z`.                    `(PCN5)`

For an external element `g`, its fiber cocycle is

`phi_k(x)^(-1)phi_k(gx)=c_k^(-d_(g,k)(x))`,           `(PCN6)`

where

`d_(g,k)(x)=r_k(gx)-r_k(x) mod M_k`.                 `(PCN7)`

Let

`omega_k=exp(2 pi i/M_k)`,
`z_k(x)=omega_k^(r_k(x))`.                            `(PCN8)`

Every `t_k`-orbit has length `M_k`, and `(PCN5)` makes `z_k` run through
all `M_k`th roots of unity on each orbit.  Hence

`sum_(x in K_k) z_k(x)=0`.                            `(PCN9)`

Moreover

`|z_k(gx)-z_k(x)|^2`
` =|omega_k^(d_(g,k)(x))-1|^2`.                      `(PCN10)`

## 3. Property-(T) density bound

Fix a finite symmetric Kazhdan generating set `S` of `SL_d(Z)` which
contains `t=I+e_12`, and let `kappa>0` be a Kazhdan constant for `S`.
Inflate `z_k` along the quotient map to a vector in `ell^2(K_k)` with
normalized norm one.  Equation `(PCN9)` makes it orthogonal to the
invariant vectors.  Therefore

`max_(g in S) ||g z_k-z_k||_2 >=kappa`.               `(PCN11)`

By `(PCN10)`, for at least one `g in S`,

`E_x |omega_k^(d_(g,k)(x))-1|^2 >=kappa^2`.           `(PCN12)`

The integrand is zero when `d_(g,k)(x)=0` and at most four otherwise, so

`P_x[d_(g,k)(x)!=0] >=kappa^2/4`.                    `(PCN13)`

The maximizing generator may depend on `k`; this is harmless because the
microstate defect uses the maximum over the fixed finite set `S`.  Since
the contribution of `t` itself in `(PCN10)` tends to zero, for all large
`k` the positive lower bound is in fact carried by another generator.

## 4. Every nonzero fiber holonomy is macroscopically visible

Put

`A_k=Z/p^(k+1)Z`, `V_k=A_k^3`,
`F_k=SL_3(A_k)`,                                      `(PCN14)`

and

`c_k=diag(1+p,1,(1+p)^(-1))`.                         `(PCN15)`

On `ell^2(F_k)`, use

`D_k(v)delta_u`
` =exp(2 pi i (u^(-1)v)_1/p^(k+1))delta_u`.           `(PCN16)`

As `u` runs uniformly over `F_k`, `u^(-1)e_1` is uniform on the primitive
vectors

`Prim(V_k)=V_k minus pV_k`.                           `(PCN17)`

Let `0!=j in Z/M_k Z`.  The lifting-the-exponent formula gives

`v_p((1+p)^j-1)=1+v_p(j)<=k`.                         `(PCN18)`

If the valuation in `(PCN18)` is less than `k`, the associated nontrivial
additive character sums to zero on both `V_k` and `pV_k`, hence also on
`Prim(V_k)`.  If it equals `k`, the sum is zero on `V_k` and trivial on
`pV_k`, so its primitive-vector average is

`-1/(p^3-1)`.                                         `(PCN19)`

In either case the real part of the normalized trace is nonpositive.
Consequently

`||R(c_k^j)D_k(e_1)R(c_k^j)^(-1)-D_k(e_1)||_2^2`
` >=2`                                                 `(PCN20)`

for every nonzero `j mod M_k`.  The same statement holds with `c_k^(-j)`.

## 5. Uniform no-go

Represent an external generator `g` by the principal-bundle permutation
from `(PBE9)`.  At the base point `x`, its right `F_k` multiplier is the
element in `(PCN6)`.  If the coefficient operator is kept equal to
`D_k(e_1)` on every base fiber, `(PCN20)` and orthogonality of the fibers
give

`||[Phi_k(g),D_k(e_1) tensor 1]||_2^2`
` >=2 P_x[d_(g,k)(x)!=0]`.                            `(PCN21)`

Combining `(PCN13)` and `(PCN21)` proves

`max_(g in S)||[Phi_k(g),D_k(e_1) tensor 1]||_2^2`
` >=kappa^2/2`.                                       `(PCN22)`

But external monomial substitutions fix constant coefficients, so these
commutators are fixed relations of the square-zero semidirect product.
Equation `(PCN22)` rules out vanishing relation defect.

This is a no-go only for the constant-over-the-bundle coefficient ansatz.
One can cancel `(PCN6)` by allowing the coefficient character itself to
depend on `x`.  Such a cancellation changes the common polynomial
representation, however.  The exact live problem is therefore:

> construct two base-dependent tangent-character fields which absorb the
> principal-bundle cocycle, are asymptotically unitarily equivalent on every
> fixed positive polynomial generator, and retain the marked negative fold.

That formulation is finite and suitable for orbit/synchronization
computation.  Searching the already-ruled-out constant field is obsolete.

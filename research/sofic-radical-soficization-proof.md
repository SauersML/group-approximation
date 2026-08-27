---
rg: 2
id: sofic-radical-soficization-proof
kind: route
title: Residual soficity of the radical quotient from products and locality
target: sofic-radical-soficization
requires: []
---

## Direct proof

Use the standard definition: `G` is sofic when for every finite `F <= G`
and every `epsilon>0` there are a nonempty finite set `V` and a map
`sigma:G->Sym(V)` with

```text
d_H(sigma(g)sigma(h),sigma(gh)) < epsilon        (g,h,gh in F),
d_H(sigma(g),id) > 1-epsilon                     (g in F\{1}),
```

`d_H` the normalized Hamming distance.

**1. Functoriality.**  Let `phi:H->Q` and let `psi:Q->S` have sofic target.
Then `psi phi:H->S` has sofic target, so `Rad_sof(H) <= ker(psi phi)`, i.e.
`psi(phi(Rad_sof(H)))=1`.  Intersecting over `psi` gives
`phi(Rad_sof(H)) <= Rad_sof(Q)`.  No surjectivity is used.

**2. Finite direct products.**  If `G_1,...,G_m` are sofic, so is
`G_1 x ... x G_m`: given `F` and `epsilon`, take approximations
`sigma_i:G_i->Sym(V_i)` for the coordinate projections of `F`, and put
`sigma(g_1,...,g_m)=sigma_1(g_1) x ... x sigma_m(g_m)` on `V_1 x ... x V_m`.
Multiplicative defects add, so they stay below `m*epsilon`; and if
`g!=1` then some `g_i!=1`, and a permutation which is a product moves at
least the fraction that its `i`-th factor moves, so
`d_H(sigma(g),id) > 1-epsilon`.  Rescaling `epsilon` gives the claim.

**3. Countable direct products.**  Let `S_1,S_2,...` be sofic and
`P=prod_n S_n`.  Fix finite `F <= P` and `epsilon>0`.  Every `f in F\{1}`
has a coordinate `n_f` with `f_{n_f}!=1`; let `pi` be the projection of `P`
onto the finitely many coordinates `{n_f : f in F\{1}}`.  Then `pi` is a
homomorphism into a finite product of sofic groups, sofic by step 2, and
`pi` is injective on `F`.  Composing `pi` with an `(pi(F),epsilon)`-
approximation of the target gives an `(F,epsilon)`-approximation of `P`:
multiplicativity is inherited because `pi` is an exact homomorphism, and
separation because `pi(f)!=1` for `f in F\{1}`.  Hence `P` is sofic.  (The
same computation shows soficity is a local property, since `F` only ever
meets the finitely generated subgroup it generates.)

**4. The radical quotient.**  Put `Q=H/Rad_sof(H)`.  For each
`1!=q in Q` choose a homomorphism `phi_q:H->S_q` with sofic target and
`phi_q(q)!=1` — one exists by the definition of the radical, since `q` has
a representative outside `Rad_sof(H)`.  As `H` is countable this is a
countable family, and each `phi_q` factors through `Q`.  The product map

```text
Q --> prod_q S_q
```

is injective.  Its target is sofic by step 3, and soficity passes to
subgroups (restrict the approximations).  Hence `Q` is sofic.

**5. Consequences.**  If `N <| H` has `H/N` sofic then the quotient map is
one of the homomorphisms defining the radical, so `Rad_sof(H) <= N`;
together with step 4 this makes `Rad_sof(H)` the smallest normal subgroup
with sofic quotient.  If `Rad_sof(H)=1` then `H = H/Rad_sof(H)` is sofic by
step 4; conversely if `H` is sofic then the identity is an admissible
homomorphism and the radical is trivial.  This proves the displayed
equivalence.

Nothing beyond the definition of soficity, closure under subgroups, and
countability of `H` is used.

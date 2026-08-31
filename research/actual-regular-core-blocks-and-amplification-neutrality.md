---
rg: 2
id: actual-regular-core-blocks-and-amplification-neutrality
kind: claim
title: Actual regular congruence cores have Plancherel-weighted large blocks, and amplification is selector-neutral
distinct_from:
  core-type-blocks-classify-relative-hole-majorants: that decomposes an arbitrary core and solves the irreducible and right-invariant regimes; this computes the blocks of the regular congruence core used in the authenticated normal form and proves exact matrix-amplification invariance.
  regular-core-window-is-a-hecke-kraus-hull: that identifies the regular relative matrix range as a commutant Kraus hull; this computes its core-type multiplicities and shows that adding copy multiplicity changes neither the selector distance nor near-top coverage.
  regular-iwahori-exactification-is-regular-branch-liftability: that reduces the open theorem to congruence-core endpoint lifting; this audits the representation type of that prescribed core and rules out bounded-multiplicity shortcuts.
---

Let `G` be finite, let `B<G`, put `q=[G:B]`, and use the actual
regular endpoint core

```text
beta_reg=lambda_G restricted to B.                         (ARC1)
```

If `pi_alpha` runs through `Irr(B)` and `d_alpha=dim(pi_alpha)`, then

```text
beta_reg
 =direct_sum_alpha pi_alpha tensor 1_(q d_alpha),

D_reg=beta_reg(B)'
 =direct_sum_alpha 1_(d_alpha) tensor M_(q d_alpha),       (ARC2)

tr_|G|(e_alpha)=d_alpha^2/|B|.                             (ARC3)
```

Moreover, for `rho_reg=Ind_B^G(beta_reg)`,

```text
E_reg=Hom_B(H_(beta_reg),H_(rho_reg))
 =direct_sum_alpha
   Mat_((q^2 d_alpha) by (q d_alpha)).                     (ARC4)
```

Thus the core in the regular congruence normal form is not merely
`lambda_B`: it is the `q`-fold amplification `q lambda_B`. Its commutant
blocks have sizes `q d_alpha`, while their normalized central weights are
the Plancherel weights `d_alpha^2/|B|`. If a near-top band happens to be a
full right `D_reg`-module, its optimal coverage is exactly the Plancherel
mass of its active `B`-types. In general the sharp-band compression need not
be right invariant, so the large blocks alone do not force coverage.

There is an exact amplification firewall. For any prescribed finite core
`beta:B->U(H)`, any selfadjoint involution `X`, and any `r>=1`, set

```text
beta^(r)=beta tensor 1_r,       X^(r)=X tensor 1_r.        (ARC5)
```

For the relative induced selector and every `epsilon`,

```text
D_(beta^(r)) = D_beta tensor M_r,
E_(beta^(r)) = E_beta tensor M_r,
T_(X^(r))    = T_X tensor id_(M_r),
Q_epsilon^(r)= Q_epsilon tensor id_(M_r),                 (ARC6)

Delta_(G,B,beta^(r))(X^(r))
 =Delta_(G,B,beta)(X),                                    (ARC7)

c_(epsilon,beta^(r),X^(r))
 =c_(epsilon,beta,X).                                     (ARC8)
```

Consequently arbitrary copy amplification preserves normalized characters,
normalized Hilbert--Schmidt residuals, the exact selector gap, and the
near-top coverage number, while multiplying every core multiplicity block
by `r`. Therefore regular-character convergence and the four Iwahori
residuals can never imply bounded core multiplicities. Conversely, large
matrix blocks by themselves cannot be the obstruction: pure amplification
does not alter it.

For the Dogon--Vigdorovich authenticated normal form, take
`G=A_N`, `B=B_N`. The literal regular endpoint gives (ARC2)--(ARC4).
More general exact congruence endpoints whose characters tend to the regular
character can have different moving packet multiplicities, and (ARC5)
allows those multiplicities to be enlarged arbitrarily without changing
any normalized hypothesis. A proof must therefore control the position of
the near-top module inside the Plancherel-weighted blocks using the two
cubic rows; neither irreducibility nor a bound on the block sizes is
available. The nonhyperlinear-group root remains open.

DERIVATION
actual-regular-core-block-amplification-proof

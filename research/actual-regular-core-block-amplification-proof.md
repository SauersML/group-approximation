---
rg: 2
id: actual-regular-core-block-amplification-proof
kind: route
title: Compute the regular restricted type algebra and prove amplification neutrality
target: actual-regular-core-blocks-and-amplification-neutrality
requires:
  - core-type-blocks-classify-relative-hole-majorants
  - every-relative-ucp-window-lives-in-one-induced-representation
  - arbitrary-core-near-top-coverage-controls-relative-corner
---

## The restricted regular endpoint

The regular representation of `B` has the standard decomposition

```text
lambda_B
 =direct_sum_alpha pi_alpha tensor 1_(d_alpha).          (ARP1)
```

The left `B`-orbits in `G` are its `q=[G:B]` left cosets. Hence

```text
lambda_G restricted to B = q lambda_B,                   (ARP2)
```

which gives the first line of (ARC2). Schur's lemma gives the commutant
formula in its second line. If `e_alpha` is the central projection onto
the `alpha`-isotypic carrier, then

```text
rank(e_alpha)=d_alpha(q d_alpha),
dim(H_(beta_reg))=|G|=q|B|.                              (ARP3)
```

Dividing the first quantity by the second gives (ARC3).

Induction commutes with direct sums, and the map

```text
C[G] tensor_(C[B]) C[B] -> C[G],
g tensor b |-> gb                                         (ARP4)
```

is the regular `G`-equivalence `Ind_B^G(lambda_B)=lambda_G`. Therefore

```text
rho_reg=Ind_B^G(q lambda_B)=q lambda_G.                  (ARP5)
```

After restriction back to `B`, the `alpha` multiplicity in the domain
is `q d_alpha` and its multiplicity in the codomain is
`q^2 d_alpha`. Taking the `B`-intertwiner space gives (ARC4).

The full-right-module coverage formula in
`core-type-blocks-classify-relative-hole-majorants` now sums the
central weights (ARC3), proving the Plancherel statement. It applies only
when the sharp band is right invariant; no such invariance follows from
(ARP1)--(ARP5).

## Induction and the near-top operator commute with amplification

Write `H^(r)=H tensor C^r`. There are canonical Hilbert-space
identifications

```text
Ind_B^G(beta tensor 1_r)
 =Ind_B^G(beta) tensor C^r,

B(H tensor C^r,H_rho tensor C^r)
 =B(H,H_rho) tensor M_r.                                (ARP6)
```

The commutant and intertwiner equations act only on the first tensor
coordinate. Thus

```text
D_(beta^(r))=D_beta tensor M_r,
E_(beta^(r))=E_beta tensor M_r.                          (ARP7)
```

With normalized Hilbert--Schmidt inner products, the orthogonal projection
onto the second space in (ARP7) is `P_E tensor id_(M_r)`. On a simple
tensor `V tensor A`, the amplified transfer operator is therefore

```text
(P_E tensor id)
 ((rho(x) tensor 1)(V tensor A)(X tensor 1))
 =T_X(V) tensor A.                                      (ARP8)
```

This proves the transfer-operator identity in (ARC6). Functional calculus
then gives the spectral-projection identity there as well.

## Coverage is invariant

Let `c` and `c^(r)` denote the two coverage numbers. If a frame
`(V_j)` in `Q_epsilon E_beta` has carrier

```text
P=sum_j V_j*V_j<=1,
```

then `(V_j tensor 1_r)` is an amplified-band frame with carrier
`P tensor 1_r` and the same normalized trace. Hence `c^(r)>=c`.

Conversely, let `Z` be any feasible positive majorant in the hole dual
for `c`. By (ARP8),

```text
(Q_epsilon tensor id)
 R_(Z tensor 1_r)
 (Q_epsilon tensor id)
 >=Q_epsilon tensor id.                                 (ARP9)
```

The amplified normalized trace of `Z tensor 1_r` equals the original
normalized trace of `Z`. The exact hole dual therefore gives
`c^(r)<=c`. This proves (ARC8).

## The selector distance is invariant

If `Theta:C*(G)->B(H)` is a relative ucp map exact on `beta`, then

```text
Theta^(r)(a)=Theta(a) tensor 1_r                         (ARP10)
```

is relative ucp and exact on `beta^(r)`. Its marked coefficient has
the same normalized Hilbert--Schmidt distance from `X^(r)` as the
original coefficient has from `X`. Taking infima gives

```text
Delta^(r)<=Delta.                                       (ARP11)
```

For the reverse inequality, compose any amplified relative ucp map with
the normalized partial trace

```text
id_(B(H)) tensor tr_r:B(H tensor C^r)->B(H).            (ARP12)
```

This is ucp, sends `beta(b) tensor 1_r` to `beta(b)`, and is a
contraction for the normalized Hilbert--Schmidt norm. Hence its marked
coefficient is no farther from `X` than the amplified coefficient was
from `X tensor 1_r`. Taking the infimum gives
`Delta<=Delta^(r)`, proving (ARC7).

Finally, every word residual and normalized character value of an amplified
tuple is the original matrix tensored with `1_r`. Both normalized trace
and normalized Hilbert--Schmidt norm are unchanged. At the same time (ARP7)
replaces every multiplicity block `M_(m_alpha)` by
`M_(r m_alpha)`. This proves the claimed firewall and its application
to the moving authenticated congruence cores.

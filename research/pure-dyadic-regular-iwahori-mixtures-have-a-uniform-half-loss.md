---
rg: 2
id: pure-dyadic-regular-iwahori-mixtures-have-a-uniform-half-loss
kind: claim
title: Pure dyadic regular Iwahori mixtures have a depth-uniform one-half common-mass ceiling
distinct_from:
  bounded-dyadic-conductor-iwahori-pairs-have-uniform-repair: that repairs arbitrary packets after imposing a conductor bound; this gives a depth-independent exclusion for arbitrary finite mixtures of amplified regular packets.
  depth-shifted-regular-overlap-is-exactly-one-sixteenth: that computes one SL3 parahoric kernel join; this computes the complete rank-one upper/opposite joint conductor table and its weighted Cheeger constant.
  dyadic-radial-shell-couplings-have-one-third-boundary: that treats radial Bruhat--Tits permutation sheets; this treats regular representations of the finite congruence vertex groups and their complete edge restrictions.
---

Let `B=B_+<SL_2(Z)` be the upper Iwahori subgroup and let `sigma:B->B_-`
be the dyadic commensuration. For `a,b>=1`, define

```text
N_a=ker(B -> SL_2(Z/2^a)),
M_b=ker(B --sigma--> B_- -> SL_2(Z/2^b)).              (DRI1)
```

Then

```text
M_b subset N_a                 if b>=a+1,
N_a subset M_b                 if a>=b+1,              (DRI2)
```

while at equal depth

```text
[N_a M_a:N_a]=[N_a M_a:M_a]=2.                        (DRI3)
```

If an irreducible congruence representation `theta` of `B` has upper and
opposite conductors

```text
n(theta)=min{a:N_a subset ker(theta)},
m(theta)=min{b:M_b subset ker(theta)},
```

put

```text
w_(n,m)=sum_(theta:n(theta)=n,m(theta)=m) dim(theta)^2.
```

The complete joint Plancherel branching table is

```text
w_(1,1)=1,
w_(n,n)=5*2^(3n-6)                    (n>=2),
w_(n,n+1)=w_(n+1,n)=2^(3n-3)         (n>=1),          (DRI4)
```

and every other `w_(n,m)` is zero. Thus every irreducible moves by at most
one conductor step under the opposite Iwahori coordinate, with exact
off-diagonal weights growing by a factor eight at each depth.

Now let `lambda_a` be the regular representation of
`G_a=SL_2(Z/2^a)`. For arbitrary finite multiplicity profiles `(r_a)` and
`(s_b)`, suppose

```text
d=sum_a r_a|G_a|=sum_b s_b|G_b|.
```

Restrict `directSum_a r_a lambda_a` through the upper edge and
`directSum_b s_b lambda_b` through the opposite edge. Their maximal common
`B`-subrepresentation has dimension at most

```text
d/2.                                                   (DRI5)
```

The constant is sharp. For a single equal-depth pair the common fraction is
exactly `1/2`; for levels separated by `k>=1` it is `8^(-k)`.

Selberg property `(tau)` upgrades `(DRI5)` to a uniform generator-defect
floor. For a fixed Iwahori generating set there is `kappa_B>0`, independent
of all depths and multiplicities, such that every unitary identification
`V` between the two equal-dimensional regular mixtures satisfies

```text
max_(x in S_B)||rho(x)V-V eta(x)||_2
   >= kappa_B/sqrt(2).                                 (DRI6)
```

Therefore the entire regular/Plancherel pure dyadic tower, including
arbitrary cross-conductor mixtures, is excluded as a low-defect enemy. The
remaining unbounded tower problem is genuinely non-Plancherel: it must use
selected irreducibles whose multiplicity profile is not forced by the
regular branching weights. A depth-uniform integer/HS repair theorem must
control those selected types; bounded branching and regular-character
normalization alone are now known to be insufficient inputs.


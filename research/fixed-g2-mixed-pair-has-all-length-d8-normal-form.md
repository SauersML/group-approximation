---
rg: 2
id: fixed-g2-mixed-pair-has-all-length-d8-normal-form
kind: claim
title: One g2-shifted mixed pair is exhausted at every word length
artifacts:
distinct_from:
  first-uncancelled-g2-mixed-carrier-has-no-hall-deficit: that treats the two shortest orders VU_2 and U_2V; this classifies every word in the same shifted pair.
  g2-one-raw-letter-sign-atlas-is-residually-finite: that closes the one-orientation rows; this shows every remaining row is one of the two already computed mixed carriers.
---

Fix

```text
U_2=g_2^2Ug_2^(-2)=x_(c_3,c_2)(T),
V=x_(c_0,c_3)(S),
P=[V,U_2]=x_(c_0,c_2)(ST).
```

Then

```text
<V,U_2> isomorphic to D_8
```

and every word has a unique collected form

```text
P^epsilon V^delta U_2^gamma,
epsilon,delta,gamma in {0,1}.                           (DAN1)
```

Thus arbitrary alternation in this fixed mixed cell has only four
coefficient regimes:

| `(delta,gamma)` | collected carrier | exact firewall |
|---|---|---|
| `(0,0)` | `1` or `P` | finite `q` envelope |
| `(1,0)` | `V` or `PV` | positive one-raw-letter RF envelope |
| `(0,1)` | `U_2` or `PU_2` | negative one-raw-letter RF envelope |
| `(1,1)` | `VU_2` or `U_2V` | hidden-`Z` rank table |

In the genuinely mixed last row, for every target atom `e_b`,

```text
tau(supp abs(Ee_b g_2^j G_(+,+) w G_(+,+)R))
 <=43/1152 <1/18,

tau(supp abs(Ee_b g_2^j G_(-,+) w G_(-,+)R))
 <=7/192 <1/18,                                        (DAN2)
```

for every integer `j` and `w` in the last row; both negative-`tau`
rows vanish. The one-orientation rows lie in the previously proved
residually finite groups even after arbitrary `g_2` conditioning.

Consequently no longer word in this same `V,U_2` pair can undo the
dihedral half-loss. The next single-word threshold requires a second
inequivalent raw placement, so that its hidden commutator sign is not the
same `Z`. Alternatively one must use genuine interference between
several distinct carriers; repeating the first carrier is exhausted.

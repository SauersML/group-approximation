---
rg: 2
id: odd-tensor-zpc-gluing-proof
kind: route
title: Tensor three complete ZPC models and read the decoded payloads on a product eigenvector
target: odd-tensor-closure-kills-projective-zpc-gluing-identities
requires: []
---

Let `rho_1,rho_2,rho_3` be complete models, extended to representations
`rhot_i` of `Gamma_L` with `rhot_i(J)=-I` and canonical predication `(OTZ2)`.

**1. The tensor product is a marked representation.** Put

```text
Pi(g)=rhot_1(g) tensor rhot_2(g) tensor rhot_3(g).
```

Evaluation of every group word factorizes over the tensor product, so every
defining row of `L` holds exactly in `Pi`, auxiliary rows included, and
`Pi(J)=(-I)^(tensor 3)=-I`. So `(OTZ4)` holds in `Pi`, and on the negative
central sector it reads `U_c=U_d`.

**2. Product eigenvectors.** Choose unit vectors `xi_i` in the joint spectral
subspace of `(Z_c,Z_d,U_q)` at `(s_i,t_i,u_i)` in `rhot_i`. By `(OTZ2)`,

```text
Z_(c,a) xi_i=(-1)^((s_i)_a) xi_i,
G_(c,a) xi_i=(-1)^((s_i)_a u_i) xi_i,
```

since an active branch applies `U_q=(-1)^(u_i)` and an inactive branch applies
the identity. The same holds for `d` with `t_i`. Put
`xi=xi_1 tensor xi_2 tensor xi_3`, a nonzero vector. Then

```text
Pi(Z_(c,a)) xi=(-1)^(s_a) xi,
Pi(G_(c,a)) xi=(-1)^(sum_i (s_i)_a u_i) xi,                         (OZP1)
```

and similarly for `d`.

**3. Decode.** `s` is a sum of three odd vectors, so it is odd and
`E_c xi=xi`. Each `P_(c,a)=(1-Z_(c,a))/2` acts on `xi` as the scalar `s_a`, so

```text
Q_(c,a) xi = s_a product_(b<a)(1-s_b) xi = [a=p(s)] xi.
```

By `(OTZ1)`,

```text
U_c xi=(-1)^(sum_i (s_i)_(p(s)) u_i) xi,
U_d xi=(-1)^(sum_i (t_i)_(p(t)) u_i) xi.
```

Step 1 gives `U_c xi=U_d xi`, and the two signs agree exactly when `(OTZ5)`
holds.

**4. Two-atom form.** With the three points `(s,t,0)`, `(s,t,1)`,
`(s',t',u')` of one model, the selector sums are `s'` and `t'`. The left side
of `(OTZ5)` is

```text
1*(s_(p(s'))+t_(p(t')))+u'*(s'_(p(s'))+t'_(p(t'))) = s_(p(s'))+t_(p(t')),
```

because `s'_(p(s'))=t'_(p(t'))=1`. This is `(OTZ6)`. The singleton case follows
from `(e_a)_(p(e_(a')))=[a=a']`.

The auxiliary generators never enter steps 2 and 3. Only their exactness under
tensor products is used, which holds for every ordinary group relator. This is
the mechanism of `central-character-profiles-affine-under-odd-tensor-products`
and `odd-tensor-closure-forces-a-threehot-hidden-sector`, applied here to
priority-decoded payloads. QED.

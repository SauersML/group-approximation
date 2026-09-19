---
rg: 2
id: involution-mark-clique-bound-proof
kind: route
title: Conjugate each triangle back to the fixed mark and apply centralizer properness once
target: involution-mark-difference-codes-have-uniform-clique-bound
requires:
  - finite-mark-centralizer-commutator-area-is-proper
---

Write `x ~_c y` when `Area_R(x y^(-1))<=c`.  If `x ~_c y`, then replacing
one occurrence of the subword `x` by `y` changes area by at most `c`.
The area of a conjugate word `g w g^(-1)` equals the area of `w`.

Fix an edge `uv` and a common neighbour `w`.  Put

```text
beta_1=b_u^(-1)b_v,   beta_2=b_u^(-1)b_w,   beta_3=b_v^(-1)b_w,
P=a_(u,v) z a_(u,v)^(-1),  Q=a_(u,w) z a_(u,w)^(-1),  T=a_(v,w) z a_(v,w)^(-1).
```

Then `(CDC2)` says `beta_1 ~_A P`, `beta_2 ~_A Q`, `beta_3 ~_A T`.
Freely, `beta_1 beta_3 = beta_2`.  Also `P^(-1) ~_s P`, `PP ~_s 1`, and
likewise for `Q` and `T`.

**Step 1: the triangle commutes, at bounded area.**  Start from
`[P,Q]=PQP^(-1)Q^(-1)` and make these substitutions:

1. `P^(-1)->P` and `Q^(-1)->Q`, cost `2s`.
2. `P->beta_1` and `Q->beta_2`, twice each, cost `4A`.  The word is now
   `beta_1beta_2beta_1beta_2`, freely equal to
   `beta_1beta_1beta_3beta_1beta_1beta_3`.
3. Each `beta_1beta_1->PP->1`, cost `2(2A+s)`.
4. `beta_3beta_3->TT->1`, cost `2A+s`.

In total,

```text
Area_R([P,Q]) <= C_A := 10A+5s.                           (ICP1)
```

**Step 2: return to the fixed anchor.**  Let `a=a_(u,v)` and
`eta=a^(-1)Q a`.  Freely, `[P,Q]=a[z,eta]a^(-1)`, so

```text
Area_R([z,eta]) <= C_A.                                   (ICP2)
```

The element `h_w` represented by `eta` commutes with `z` in `Gamma`, because
`[z,eta]` is null-homotopic.  Apply `(FMC1)` with the fixed word `beta=z`,
whose constants `A_z,B_z` depend only on the presentation and `z`:

```text
d_(K\Gamma)(K,K h_w) <= (C_A+B_z)/A_z = rho_A.
```

So `h_w` lies in one of at most `|Ball_(K\Gamma)(rho_A)|` cosets of the
two-element group `K`.  Hence `h_w` takes at most `2|Ball(rho_A)|` values.

**Step 3: count.**  In `Gamma`, `h_w=a^(-1)b_u^(-1)b_w a`, so `h_w`
determines `b_w`.  Moreover `h_w!=1` because `b_w!=b_u`, and `h_w!=z`
because `b_w!=b_v`.  Adjacent vertices have distinct values, since their
difference is a conjugate of `z!=1`.  Therefore the common neighbourhood of
`uv` takes at most `2|Ball(rho_A)|-2` values.  A clique containing `uv`
consists of `u`, `v` and pairwise distinct common-neighbour values, which
gives `(ICB1)`.

Why the anchor matters: `nested-prefix-centralizer-area-divergence-proof`
anchors FMC at `c_1=beta_1`.  Its constant `B=2|beta_1|/ell` then grows with
the edge.  Conjugating by the edge conjugator `a_(u,v)` costs zero area, so
every triangle is moved to the one fixed anchor `z`.

---
rg: 2
id: stable-abelianized-cover-is-subgroup-monotone
kind: claim
title: The stable free abelianized cover does not depend on the presentation, contains the stable cover of every finitely generated subgroup, and lifts no non-free subgroup
distinct_from:
  dummy-abelianized-cover-df-splits-regular-trace-and-shadow: that splits DF for ONE dummy cover E_z into (REG) and (SH) by traces; this is pure group theory and compares covers of DIFFERENT presentations and of DIFFERENT groups, with no analysis.
  relation-lamp-wreath-is-mf-with-nontrivial-fd-radical: that records E_z = ZG x| E and calibrates it against the MF lamp group; this uses that identification to show the dummy-stabilized cover is a presentation invariant and is monotone along all subgroup inclusions.
  free-abelianized-cover-is-torsion-free: that proves the cover is torsion-free; this proves which subgroups of the base lift to it (exactly the free ones) and which covers embed in it.
  full-mf-radical-abelianized-cover-is-not-mf: that is the open target DF for a fixed presentation; this reduces the part of DF the route uses to a presentation-free invariant that is inherited from any finitely generated subgroup.
artifacts:
  - research/stable-abelianized-cover-subgroup-monotone-proof.md
---

**ESTABLISHED (written proof; not Lean-verified).**  This is a reduction and
invariance statement for the abelianized-cover lane.

## Notation

A **generating map** of a group `H` is an epimorphism `p: F(B) -> H` from a
free group with a countable basis `B`.  Its **cover** is

```text
E(p) = F(B)/[R_p,R_p],   R_p = ker p,   M(p) = R_p/[R_p,R_p].
```

A **finite generating family** of `H` is a finite set `X` with a map
`X -> H` whose image generates `H`; repetitions and letters sent to `1` are
allowed.  For such `X` and `0 <= k <= aleph_0`, write
`E_(H,X,k)` for the cover of `F(X u Z_k) -> H`, where the `k` letters of `Z_k`
map to `1`.  So `E_(H,X,0) = E_(H,X)` is the ordinary cover.  "MF" means
embeddable in `U(prod_n M_(k_n)/(+)_n M_(k_n))` for some sequence `(k_n)`.

Say that **`H` is stably DF** if `E_(H,X,k)` is not MF for some finite
generating family `X` of `H` and some finite `k`.

## Statement

Let `G` be finitely generated and not free, and let `P: F(X) -> G` be a
generating map with `X` finite and kernel `R`, so `R != 1`.

1. **Dummies split off.**  `E_(G,X,k) = (ZG)^k x| E_(G,X)`, with `E` acting
   through `G` by left multiplication.  The relation module of `F(X u Z_k) -> G` is `M(P) (+) ZG^k`, and
   `E_(G,X)` is a retract of `E_(G,X,k)`.
2. **Tietze invariance.**  For finite generating families `X` and `Y` of `G`:
   ```text
   E_(G,X,|Y|+k) = E_(G,Y,|X|+k)   (0 <= k <= aleph_0),    E_(G,X,aleph_0) = E_(G,Y,aleph_0).
   ```
   So being stably DF does not depend on `X`.  If `E_(G,X)` is not MF for one
   `X`, then `G` is stably DF.
3. **Infinite-dummy normal form.**  Let `p: F(B) -> H` be any generating map
   of a finitely generated group `H` with `B` countably infinite.  Then `E(p) = E_(H,X,aleph_0)` for every finite generating family
   `X` of `H`.
4. **Subgroup monotonicity.**  Let `H <= G` be finitely generated, and put
   `F_H = P^(-1)(H)`.  Then `F_H/[R,R]` is a subgroup of `E_(G,X)`, and it is
   the cover of the generating map `P|: F_H -> H`.
   - If `[G:H] = infinity`, then `F_H/[R,R] = E_(H,Y,aleph_0)` for every
     finite generating family `Y` of `H`.  Hence **if `H` is stably DF, then
     `E_(G,X')` is not MF for every finite generating family `X'` of `G`**, with
     no dummies and no hypothesis on `G` or `H` beyond finite generation.
   - If `[G:H] = d < infinity`, then `F_H/[R,R]` has index `d` in `E_(G,X)`,
     and `E_(H,Y,j)` embeds in `E_(G,X,k)` whenever `dk >= j + |Y|`.  MF
     passes to finite-index overgroups.  So being stably DF is invariant under
     passing to and from finite-index subgroups: it is a commensurability
     invariant.
5. **Only free subgroups lift.**  For `H <= G`, the extension `F_H/[R,R]` of
   `H` by `M` splits if and only if `H` is free.  So `E_(G,X)` contains no
   subgroup mapping isomorphically onto a non-free subgroup of `G`.
6. **Calibration: amenable witnesses die.**  If `H` is amenable, then every
   `E_(H,X,k)` is amenable and hence MF, by Tikuisis--White--Winter
   quasidiagonality.  Free `H` also die, because there `E_(H,X,k) = Z^k wr H`
   is residually finite.  So a subgroup witness in item 4 must be
   non-amenable and non-free.

## What this does for DF and the route

- The route `property-t-free-seed-via-leavitt-abelianized-cover` accepts the
  dummy cover (see `relation-lamp-wreath-is-mf-with-nontrivial-fd-radical`).
  So what it uses from `full-mf-radical-abelianized-cover-is-not-mf` is
  exactly this: **the finitely presented full-radical cover `G~` of
  `St_20(L_(F_2)(1,2))` is stably DF.**  By item 2 this is
  presentation-free.
- By item 4 that requirement splits.  It follows from stable DF of any single
  finitely generated subgroup `H <= G~` of any index, where `H` itself need
  not have full MF radical.  If the index is infinite, it gives DF for every
  presentation of `G~` with no dummies at all.
- Contrapositive, which constrains counterexamples.  If `E_(G,X)` is MF for
  one `X`, then no finitely generated infinite-index subgroup of `G` is
  stably DF, and the cover `F_H/[R,R]` of every finite-index subgroup `H`
  is MF.  So a counterexample to DF at `G` is at the same time a
  counterexample to stable DF at every finitely generated infinite-index
  subgroup of `G`.  For example, for
  full-radical `G` the group `G x G` also has full radical and contains `G`
  with infinite index, so stable DF for `G` gives DF for every presentation
  of `G x G`.
- By item 5, an attack that "lifts a non-MF subgroup of `G` into `E`" is
  dead: the subgroup never lifts.  What does embed is its stable cover, which
  is item 4.
- Item 1 leaves open whether DF for `E_(G,X)` is equivalent to DF for
  `E_(G,X,1) = ZG x| E_(G,X)`.  In other words, it is open whether one
  dummy lamp can destroy MF.  This is the only gap between the
  presentation-free invariant and DF for a fixed presentation.

Proof route: `stable-abelianized-cover-subgroup-monotone-proof`.

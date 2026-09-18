---
rg: 2
id: bffhz-closures-cannot-create-gl-n-q
kind: claim
title: The BFFHZ free-product and mapping-torus closures cannot create GL_n(Q), and the BFFHZ actor puts SL_n(Q) in its M-Torelli kernel
distinct_from:
  mif-free-product-automorphism-ascending-hnn-is-pbh: that proves ascending HNN extensions over M * F_m lie in the permutational class; this shows those extensions contain GL_n(Q)' = SL_n(Q) only if the base group M already does.
  aut-free-groups-satisfy-permutational-boone-higman: that imports BFFHZ Theorem A and its free-product Corollary F; this shows Corollary F adds nothing for GL_n(Q) and its stepping stones.
  relative-automorphism-of-fp-simple-mif-group-has-type-a-action: that imports BFFHZ Theorem E, the type (A) action of Aut_M(M * F_m); this locates where GL_n(Q) would have to sit inside that actor.
  gl-n-q-fixes-a-vertex-in-free-splittings: that is the fixed-point lemma; this is its application to the BFFHZ constructions.
artifacts:
  - research/artifacts/gq-gq-typeA-bffhz-transfer.md
  - research/artifacts/gq-referee-c-bffhz-closures-cannot-create-gl-n-q.md
---

**ESTABLISHED** through `bffhz-closures-cannot-create-gl-n-q-proof`.
Lane-proved. Independent re-derivation by referee C: PASS
(`research/artifacts/gq-referee-c-bffhz-closures-cannot-create-gl-n-q.md`); its
four wording fixes are applied below. No second referee. No priority is claimed.

Let `M` be a finitely presented simple MIF group, `m >= 1`, and let `H` be one
of `GL_n(Q)`, `SL_n(Q)` (`n >= 2`), `Aff(Q)`, `U_3(Q)`, `(Q,+)`. Write `H'` for
its derived subgroup: `SL_n(Q)`, `SL_n(Q)`, `(Q,+)`, the centre `≅ (Q,+)`, and
for `(Q,+)` take `H' := H`.

1. **Free products (BFFHZ Corollary F).** If `H <= A * B`, then `H` lies in a
   conjugate of `A` or of `B`. So Corollary F, closure of the permutational
   class under free products, never produces `H` from factors that lack it.
2. **Mapping tori and ascending HNN extensions over `M * F_m`** (the
   construction of `mif-free-product-automorphism-ascending-hnn-is-pbh`). Let
   `β ∈ Aut(M * F_m)`, `J <= M * F_m` with `β(J) ⊆ J`. If `H <= J *_β`, then
   `H'` lies in the kernel `L` of the exponent map `J *_β -> Z`, and the image
   of `H'` under the embedding `L ↪ M * F_m` lies in a conjugate of `M`. In
   particular `M` contains a copy of `SL_n(Q)` when `H ∈ {GL_n(Q), SL_n(Q)}`,
   and of `(Q,+)` in the other three cases.
3. **The BFFHZ actor itself.** Let `K_M` be the kernel of the natural map
   `Aut_M(M * F_m) -> Aut(F_m)` induced on `(M * F_m)/<<M>> ≅ F_m`. Every
   subgroup of `Aut_M(M * F_m)` isomorphic to `GL_n(Q)` or `SL_n(Q)` has its `SL_n(Q)`
   inside `K_M`. Every copy of `U_3(Q)` or `(Q,+)` lies in `K_M`. The
   group `K_M` embeds, by restriction, in the group of automorphisms of
   `N = <<M>> = *_{w ∈ F_m} w M w^-1` that act on each free factor as
   conjugation by an element of `N`. It contains `M^m` through the right
   translations `x_i -> x_i g`.

**What survives.** Items 1–3 show that the free-group directions of the BFFHZ
machine supply no divisibility. With BFFHZ's own choice `M = V`, which contains
no `(Q,+)` (survey Theorem 4.4), items 1 and 2 exclude every one of these
groups. For GL_n(Q), the BFFHZ neighbourhood leaves three entry points:
- the M-Torelli kernel `K_M` in item 3;
- HNN extensions of type (A) actors over **nontrivial** finitely generated
  edge groups, realized by a permutation
  (`stable-permutation-hnn-of-type-a-actor-is-type-a` (b)). These can create
  divisibility, as `Z[1/2] <= BS(1,2)` does;
- outer extensions (`outer-extensions-of-fp-simple-mif-groups-satisfy-pbh`
  (S)). There, `GL_n(Q) <= Aut(S)` meets `Inn(S)` either in a subgroup that
  contains `SL_n(Q)`, which is circular, or in scalars. In the scalar case the
  image of `SL_n(Q)` in `Out(S)`, which is `SL_n(Q)` or `PSL_n(Q)` (for even `n`
  the scalar `-I` need not be inner), must lie in a finitely presented subgroup
  of `Out(S)`. That is a Problem 2.7-type input.

## Attempts

- **Open question left by item 3.** If `M` contains no `(Q,+)`, can `K_M`
  contain one? For `m = 1`, IF `K_M` consists only of the maps `x -> g x h`
  (`g, h ∈ M`), then `K_M` is a copy of `M × M` and contains `(Q,+)` only if `M`
  does, since two nonzero subgroups of `Q` meet nontrivially. That description of
  `K_M` is neither proved nor cited here. For `m = 2`, the transvections of one letter by
  `<<M>> ∩ <M, y>` give a free product of copies of `M`, and by
  `gl-n-q-fixes-a-vertex-in-free-splittings` that also contains none.
  - The general case is not proved. A likely route: relative train tracks
    (Francaviglia–Martino) force stretch factor 1 for divisible elements, and
    then one needs a polynomial-growth analysis.
  - A negative answer (no Q) would close the BFFHZ actor with `M = V` as a host
    for every group in the list.

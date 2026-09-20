---
rg: 2
id: thompson-t-witnesses-are-dense-in-simple-adjoint-groups
kind: claim
title: "T is not MF iff Gap_T(SU), Gap_T(SO) and Gap_T(Sp) hold over Z/4 * Z/3, and the triangle-cover gap (R_Delta) holds iff Gap_Delta(SU), Gap_Delta(SO) and Gap_Delta(Sp) hold over Delta(4,3,5); every small-defect witness on either level is a dense homomorphism into one simple adjoint group of unbounded dimension, and all finite-quotient, induced and fixed-group models are gapped at 1/2"
distinct_from:
  thompson-v-mf-witnesses-are-dense-in-simple-adjoint-groups: that is the trichotomy for V over S4 *_Z2 S3; this is the trichotomy for T, on two levels, over Z/4 * Z/3 and over the triangle cover Delta(4,3,5), and T <= V gives no implication between the two sets of gaps in the needed direction.
  thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes: that reduces T not MF to one uniform gap over all nontrivial exact pairs; this restricts the witness class, without loss, to exact pairs whose Ad-image on one simple ideal is dense in a classical adjoint group of growing rank.
  thompson-t-not-mf-iff-triangle-gap-and-rounding: that splits T not MF into (R_Delta) and (S_T); this splits (R_Delta) further into three classical gaps for honest Delta-representations, and gives a second splitting of T not MF that bypasses (S_T).
  thompson-t-pentagon-winding-rigidity-equals-full-radical: that shows every arc-detecting (BA)^5 invariant is equivalent to the flagship; this is a Lie-theoretic normal form for witnesses, with no K-theory.
artifacts:
  - research/thompson-t-witnesses-are-dense-in-simple-adjoint-groups-proof.md
  - research/lie-closure-trichotomy-without-finite-quotients.md
---

**ESTABLISHED** by `thompson-t-witnesses-are-dense-in-simple-adjoint-groups-proof`, a written proof
that has not been reviewed. It instantiates `lie-closure-trichotomy-without-finite-quotients` twice.

## Setting

We use the Lochak--Schneps words `r_1 = [bab, a^2 bab a^2]`, `r_2 = [bab, a^2 b^2 a^2 bab a^2 b a^2]`
and `r_P = (ba)^5`. There are two levels.

- **Level T.** `Gamma0 = Z/4 * Z/3 = <a, b | a^4, b^3>`, with `R_T = {r_1, r_2, r_P}` and
  `Q = T`. Here `delta_N` is the `delta_N` of `thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes`.
- **Level Delta.** `Gamma0 = Delta = Delta(4,3,5) = <a, b | a^4, b^3, (ba)^5>`, with
  `R_Delta = {r_1, r_2}` and `Q = T`. Here `delta_N = gamma_N` is the `gamma_N` of
  `thompson-t-not-mf-iff-triangle-gap-and-rounding`, and (R_Delta) is `inf_N gamma_N > 0`
  (`thompson-t-triangle-genuine-rep-relator-gap`).

For `X` in `{SU, SO, Sp}` and each level `L` in `{T, Delta}`, define:

```text
Gap_L(X):  exists eps > 0 such that for every k for which X(k) is simple, and every homomorphism
           tau : Gamma0 -> Inn(X(k)) with dense image,   max_(r in R_L) ||tau(r) - 1|| >= eps.
```

Here `Inn(su(k)) = PSU(k)`, `Inn(sp(k)) = Sp(k)/{+-1}`, and `Inn(so(k))` is `SO(k)` or `SO(k)/{+-1}`.
Norms are taken in the invariant inner product.

## Statement

1. **(Level T trichotomy.)** `T` is not MF iff `Gap_T(SU)`, `Gap_T(SO)` and `Gap_T(Sp)` all hold.
2. **(Level Delta trichotomy.)** (R_Delta) holds iff `Gap_Delta(SU)`, `Gap_Delta(SO)` and
   `Gap_Delta(Sp)` all hold.
3. **(Comparison.)** `Gap_T(X)` implies `Gap_Delta(X)` for each `X`, with the same `eps`. So T not MF
   implies each Delta gap, and item 2 recovers the implication "T not MF => (R_Delta)".
4. **(Normal form of witnesses.)** Let `sigma` be a nontrivial irreducible, of either level, with
   defect `D < 1/2`.
   - `[l_sigma, l_sigma]` is a nonzero orthogonal sum of `Ad(K_sigma)`-invariant simple ideals `h_a`.
   - Each `Ad(sigma)|_(h_a)` is a dense homomorphism into `Inn(h_a)`, with defect at most `2D` and
     `delta_(dim h_a) <= 2D`.
   - Along any witness sequence with `D -> 0`, `min_a dim h_a -> infinity`.
5. **(Uniform kills at 1/2, at both levels.)** In every dimension, the following models have defect
   at least the stated bound.
   - Every nontrivial irreducible whose image is finite, finite modulo scalars, or virtually abelian:
     at least `1/2`. At level Delta this covers every representation of `Delta` that factors through a
     finite quotient `Delta ->> F`, for example `PSL(2, q)` or any Hurwitz-type quotient.
   - Every representation with a nontrivial system of imprimitivity, in particular every representation
     induced from a proper finite-index subgroup, such as a surface subgroup of `Delta`: at least
     `sqrt 2`.
   - Every nontrivial `pi o phi` with `phi : Gamma0 -> M` into a fixed compact Lie group: at least
     `min(1/2, delta_(dim M)/2)`. At level Delta this covers the following: take any homomorphism
     `phi : Delta -> SO(3)`, for instance the dense one from the spherical triangle with angles
     `(3 pi/4, pi/3, 3 pi/5)` (see `thompson-t-triangle-gap-on-dense-orthogonal-adjoint-images`), and
     compose it with any
     representation of `SO(3)`, such as the whole `Sym^m` tower. These are gapped by
     `min(1/2, gamma_3/2)`, which is positive (`gamma_3 >= delta_3 > 0`), uniformly in `m`.

## What this changes

- **The flagship now has two exact splittings.**
  - `T` is not MF iff (S_T), `Gap_Delta(SU)`, `Gap_Delta(SO)` and `Gap_Delta(Sp)` all hold. This
    combines item 2 with `thompson-t-not-mf-iff-triangle-gap-and-rounding`.
  - `T` is not MF iff `Gap_T(SU)`, `Gap_T(SO)` and `Gap_T(Sp)` all hold. This is item 1, and it
    bypasses the rounding condition (S_T) entirely.

  Each of the six gaps is a single uniform statement about dense homomorphisms of a virtually free
  group or of a cocompact Fuchsian group into one classical compact adjoint family. Each can be refuted
  on its own, by an explicit sequence of dense homomorphisms whose relator images tend to `1`.
- **The "finite quotients" failure mode of (R_Delta) is dead.** `thompson-t-triangle-genuine-rep-relator-gap`
  suggested finite quotients `Delta ->> Q_j` as the natural source of a refutation. By item 5, every
  such model has defect at least `1/2`, whatever the quotient and whatever its representation. The
  same holds for induced models built from surface subgroups, and for all pullbacks from one fixed
  compact group. A refutation of (R_Delta) must use infinite images that are dense in `PSU(k)`,
  `SO(k)` or `Sp(k)/{+-1}` with `k -> infinity`.
- **Invariant and death step.** The invariant is `N_sigma = dim [l_sigma, l_sigma]`. Every bounded-`N`
  model dies at one step: the adjoint representation on `[l, l]_C` has defect at most `2D` and
  dimension `N`, and `delta_N` gaps it.

## Remarks (not claimed)

- **Level Delta is a statement about character varieties.** Honest representations `Delta -> Inn(h)`
  are points of the relative character variety with the conjugacy classes of `a`, `b` and `ba` fixed,
  of orders dividing 4, 3 and 5. For a nontrivial representation none of the three images is trivial.
  For example, `a -> 1` forces `b^3 = b^5 = 1`, so `b = 1`. As `dim h -> infinity`, the expected
  dimension of these components is about `(3/4 + 2/3 + 4/5 - 2) dim h`, which is roughly
  `0.22 dim h`. Near-vanishing of `r_1, r_2` is about `2 dim h` real conditions. This count is
  heuristic evidence for `Gap_Delta` and proves nothing.
- `T <= V`, but `Gap_T` and the V gaps `Gap(X)` are not comparable in the direction needed. A dense
  homomorphism of `G0` restricts to `T`'s generators only after passing through `V`, and there is no
  map `Z/4 * Z/3 -> G0` carrying `R_T` into `<<r5..r8>>` that we know of.

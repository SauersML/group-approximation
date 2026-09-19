---
rg: 2
id: acylindrical-hosts-break-witness-host-inner-pigeonhole-proof
kind: route
title: Restrict the geometric action of the Ollivier--Wise torus to its Kazhdan kernel, upgrade it by Osin to a cobounded model, and read off pairwise non-conjugate powers from infinite outer order
target: acylindrical-hosts-break-witness-host-inner-pigeonhole
requires:
  - ollivier-wise-z-torus-kernel-not-finitely-presented
  - osin-acylindrical-trichotomy-and-cayley-models
  - rel-hyperbolic-hosts-make-witness-powers-host-inner
---

Notation is that of the target. `G = G_OW = N ⋊_φ <t>`, with `φ(k) = t k t^(-1)`. `S` is a finite
generating set of `G`, `|·|_S` its word length and `B(r) = {g : |g|_S ≤ r}`, which is finite.
`π : G → Z` is the quotient map, with `π(t) = 1`. `S_N` is a finite generating set of `N`, which
exists because `N` is Kazhdan.

## Step 0: inputs

From `ollivier-wise-z-torus-kernel-not-finitely-presented`, items 1--5:
- `G` is finitely presented, torsion-free and word-hyperbolic;
- `N` is nontrivial, torsion-free (hence infinite) and Kazhdan;
- `[φ]` has infinite order in `Out(N)`.

Two standard facts about property (T) (Bekka--de la Harpe--Valette, *Kazhdan's Property (T)*,
Chapter 1; the section numbers are cited from memory and were not re-read):
- a Kazhdan group has finite abelianization, so `Z` is not Kazhdan. This is (B6) of
  `ollivier-wise-z-torus-kernel-not-finitely-presented-proof`;
- a finite-index subgroup of a Kazhdan group is Kazhdan. This is the finite-covolume case of
  heredity for lattices, the same fact that Corollary 1 of
  `rel-hyperbolic-hosts-make-witness-powers-host-inner-proof` uses.

So `N` is **not virtually cyclic**. `N` is infinite, so a virtually cyclic `N` would have a
finite-index subgroup `≅ Z`, which would be Kazhdan.

## Step 1: the proper model `Y_prop = Cay(G, S)`

`G` is word-hyperbolic, so `Y_prop` is a hyperbolic geodesic graph. `G` acts by left
multiplication, freely on vertices, and `N` acts by restriction.

**Acylindricity.** Let `ε > 0`, and let `x ∈ Y_prop` with `d(x, gx) ≤ ε`. Choose a vertex `v` with
`d(x, v) ≤ 1/2`. Then `d(v, gv) ≤ ε + 1`, so `v^(-1) g v ∈ B(ε + 1)`. So at most `|B(ε + 1)|`
elements `g ∈ G` move `x` by at most `ε`. With `R = 1` and `N_ε = |B(ε + 1)|`, the definition (AC)
holds for `G`, and it holds for every subgroup of `G`, in particular for `N`. The same count shows
the action is proper.

**Unbounded orbits.** The orbit `N·1` is the infinite vertex set `N`. A ball of `Y_prop` contains
only finitely many vertices.

**Not cobounded.** Suppose `N·B(r)` contained every vertex. Then `G = N B(r)`, so `[G : N] ≤ |B(r)|`.
But `G/N ≅ Z` is infinite.

**Quasi-centres drift.** Let `L = max_{s ∈ S} |π(s)|`, so `|π(g)| ≤ L|g|_S`. For `k ∈ N`,
`d(k, t^n) = |k^(-1) t^n|_S ≥ |π(k^(-1) t^n)| / L = n / L`. So the image of `t^n` in `N \ Y_prop`
is at distance at least `n/L` from the image of `1`.

## Step 2: `N` is acylindrically hyperbolic; the cobounded model `Y_cob`

By Step 1, `N` acts acylindrically on the hyperbolic space `Y_prop` with unbounded orbits. By
Osin's Theorem 1.1 (O1), exactly one of (a), (b), (c) holds:
- (a) fails, since the orbits are unbounded;
- (b) fails, since `N` is not virtually cyclic (Step 0).

So (c) holds, and by the non-elementarity sentence in (O1) the action is non-elementary. Thus (AH2)
holds, and `N` is acylindrically hyperbolic by (O2).

By (AH1), there is a generating set `X` of `N` with `Y_cob = Γ(N, X)` hyperbolic,
`|∂Y_cob| > 2`, and the action of `N` acylindrical. It is vertex-transitive, so cobounded.
- Its orbits are unbounded. Otherwise the vertex set, a single orbit, would be bounded, so
  `Y_cob` would be bounded and `∂Y_cob = ∅`.
- By (O1) again, (c) holds, so the action is non-elementary.

This proves item 1 of the theorem.

## Step 3: no power of `φ` is host-inner in `H = N`

Take `H = N` with either action, and `ψ = id_N`. By Steps 1 and 2, `ψ(N) = N` has unbounded
orbits, so it is not elliptic.

Suppose `ψ φ^m = c_h ψ` with `m ≥ 1` and `h ∈ H = N`. Then `φ^m = c_h` is inner, so `[φ]` has
finite order dividing `m` in `Out(N)`, contradicting Step 0.

Similarly, suppose `ψ φ^b = c_g ψ φ^a` with `0 ≤ a < b` and `g ∈ N`. Precomposing with `φ^(-a)`
gives `φ^(b-a) = c_g`, which is the same contradiction. So the maps `ψ φ^n` (`n ≥ 0`) are pairwise
non-conjugate in `H`, and all have image `N`. This proves item 2.

## Step 4: bounded scaling factors on `Y_prop`

Groves--Hull, arXiv:1704.03491 (verbatim, pp. 12--13, context only):

> ‖ϕi‖ = inf_{x∈Xi} max_{s∈S} di(x, ϕi(s)x).

> Definition 4.2. The sequence (ϕi) is called divergent if limω ‖ϕi‖ = ∞.

For `n ≥ 0` and `s ∈ S_N`, `ψ φ^n(s) = t^n s t^(-n)`. At the vertex `x = t^n` of `Y_prop`,

```text
d(t^n, t^n s t^(-n) · t^n) = d(t^n, t^n s) = |s|_S.
```

So `‖ψ φ^n‖ ≤ max_{s ∈ S_N} |s|_S` for every `n`. The sequence is non-divergent for every
ultrafilter, while by Step 3 it meets infinitely many conjugacy classes. The quasi-centres `t^n`
drift to infinity in `N \ Y_prop` (Step 1). This proves item 3.

## Step 5: the kernel form

`N` is acylindrically hyperbolic (Step 2) and Kazhdan. `[φ]` has infinite order, and the mapping
torus `G` is finitely presented and hyperbolic with `cd ≤ 2` (Step 0). This proves item 4.

## Step 6: where the w17 proof breaks, and the class kill

In `rel-hyperbolic-hosts-make-witness-powers-host-inner-proof`, Step 1 is the only point where the
host geometry is used. Everything after it (Step 2, Cases A and B) is formal group theory given
(HI). The inputs listed under "The class" in the target are all satisfied by
`(K, φ, H, ψ) = (N, φ, N, id)` with either action. Yet (HI) fails by Step 3.

So no argument from those inputs proves (HI). In particular it cannot prove the host-inner
dichotomy, nor its consequences:
- finite outer order for acylindrically hyperbolic kernels, which is false by Step 5;
- non-MF acylindrical hosts via Cases A and B.

The death is at the finiteness of conjugacy classes. The only finiteness that property (T) gives
for acylindrical targets is non-divergence, and Step 4 shows it is compatible with infinitely many
classes. ∎

## Rigor note

External inputs:
- the verbatim Osin imports (O1) and (O2) in `osin-acylindrical-trichotomy-and-cayley-models-citation`;
- the two textbook facts on property (T) in Step 0;
- the established node `ollivier-wise-z-torus-kernel-not-finitely-presented`.

The Groves--Hull quote only fixes the meaning of "non-divergent", and no Groves--Hull theorem is
used. Švarc--Milnor, mentioned in the target, is commentary, and no step depends on it.

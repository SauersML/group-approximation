---
rg: 2
id: brin-thompson-nv-fibre-elements-are-cubically-elliptic
kind: claim
title: "In every commensurating action of nV (n >= 2), every fibrewise element and every element of V^n is elliptic; so no cubical action is proper on T_n, and Brothier's Problem B has no cubical proof"
distinct_from:
  brin-thompson-nv-no-cubical-action-proper-mod-triangular: that uses the distorted Callard--Salo element (outside T_n) to rule out cubical properness modulo T_n, which is the transversal half R1 of the triangular split; this uses undistorted central elements inside T_n to rule out cubical properness on T_n itself, which is the fibre half R2, so both halves of the split are forced to be non-cubical
  brin-thompson-mv-contains-a-distortion-element: that gives the absence of a proper cubical action of mV through distortion; this gives it again without distortion, and shows far more elements are elliptic, including all of V^n, which Cornulier's distortion criterion cannot reach since T_n is undistorted
  cubical-coset-proper-actions-capture-distorted-elements: that makes distorted elements elliptic; here the elliptic elements are undistorted, and the invariant is a character of the centralizer rather than growth
  twisted-brin-thompson-groups-have-property-fa: that imports FW_infinity (fixed points on finite-dimensional cube complexes) for twisted Brin--Thompson groups; this covers all commensurating actions, including infinite-dimensional ones, but only elementwise and only for fibrewise elements
  cantor-integer-maps-by-v-are-not-a-t-menable: that is a negative conjecture about all cnd functions on C(C,Z) ⋊ V; this rules out only the commensurating (wall-count) cnd functions
---

**ESTABLISHED** by `brin-thompson-nv-fibre-elements-are-cubically-elliptic-proof`.

**Setting.** `C = {0,1}^ω`, and `nV` acts on `C^n = C^{n−1} × C`. A commensurating action of a
group `G` is an action on a set `X` with a commensurated `A ⊆ X`, and `ℓ(g) = |gA Δ A|`. An
element `g` is *elliptic* if `ℓ(g^N)` is bounded in `N`. Actions on CAT(0) cube complexes and
on discrete wall spaces are special cases, with `ℓ(g) = d(v, gv)`. The *fibrewise subgroup* is

```text
K_n = { (x', y) ↦ (x', F(x')(y)) : F : C^{n−1} → V locally constant } ≤ T_n ≤ nV .
```

**Statement.** Let `n ≥ 2`, and fix any commensurating action of `nV`.

1. Every element of `K_n`, of its conjugates in `nV`, and of their images under permutations
   of the coordinates is elliptic.
2. Every element of `V^n` (coordinatewise action) and of its conjugates is elliptic.
3. For every group `Γ` with an element `γ` of infinite order, in every commensurating action of
   `C(C,Γ) ⋊ V` the constant map `γ` is elliptic. More generally, for every clopen `U ⊆ C`, the
   map equal to `γ` on `U` and `1` off `U` is elliptic.
4. Consequently no commensurating action of `nV` has `ℓ` proper on any subgroup containing an
   infinite-order element from items 1 and 2. This includes `V × id^{n−1}`, `V^n`, `K_n`, `T_n`,
   and the copies of `C(C,Z) ⋊ V` and `C(C,V) ⋊ V` inside `T_n`. Also no commensurating action
   of `C(C,Γ) ⋊ V` is proper when `Γ` has an infinite-order element.

**What this kills.**
- *Fibre half of the triangular split.* A cubical or wall-space proof of
  `brin-thompson-nv-cnd-proper-on-triangular-subgroup` (R2) is impossible. Together with
  `brin-thompson-nv-no-cubical-action-proper-mod-triangular` (R1), both prerequisites of
  `brin-thompson-nv-a-t-menable-via-triangular-split` are now forced to be non-cubical.
- *Problem B.* A cubical proof of Brothier's Problem B is impossible for every `Γ` with an
  element of infinite order, in particular for `Γ = Z` (`cantor-integer-maps-by-v-have-haagerup-property`)
  and `Γ = V`. Every "decorated Farley chart", "brick chart" or other wall construction on
  `C(C,Z) ⋊ V` must fail to be proper, and it fails on the centre `⟨1_C⟩`.
- *Contrast (remark, not load-bearing).* `V` alone acts properly on a CAT(0) cube complex
  (Farley, "Proper isometric actions of Thompson's groups on Hilbert space", IMRN 2003). This
  claim shows that in every commensurating action of `nV` the restriction to `V × id` is not
  proper.

**Invariant and death step.** The invariant is a *central element of a perfect group without
finite quotients*. Every commensurating candidate dies at the one-ended orbits of the central
element. There are finitely many of them, the centralizer permutes them, and a finite-index
subgroup translates along one of them, giving a homomorphism to `Z` that is nonzero on the
central element. That is impossible in a perfect group with no finite quotients
(`commensurating-loxodromics-split-their-centralizers`).

**Not claimed.** Uniform ellipticity of the subgroups `V × id` or `K_n` (bounded `ℓ` on the whole
subgroup, as property FW would give); ellipticity of the baker's map and other non-triangular
undistorted elements; and anything about non-commensurating cnd functions.

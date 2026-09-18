---
rg: 2
id: cubical-hosts-of-thompson-f-never-have-property-a-proof
kind: route
title: A free cube-permuting action of F on a finite-dimensional CAT(0) cube complex would give a free resolution of finite length, so every proper cubical host of F is infinite-dimensional and fails property A
target: cubical-hosts-of-thompson-f-never-have-property-a
requires: [cat0-cube-complexes-with-property-a-are-finite-dimensional, thompson-f-has-infinite-cohomological-dimension]
---

**Cited facts (acyclicity).** Verbatim from I. J. Leary, *A metric Kan–Thurston theorem*, arXiv:1009.1540v3,
Appendix B. The PDF was fetched on 2026-09-18 and read through `pypdf`.

- (L1) Definition B.1: "Define a combinatorially CAT(0) cubical complex to be a simply connected cubical complex
  in which all vertex links are flag. (It will be shown in Theorem B.8 that a cubical complex is CAT(0) if and
  only if it is combinatorially CAT(0).)"
- (L2) Theorem B.4: "Every finite subcomplex of a combinatorially CAT(0) cubical complex is contained in a
  finite combinatorially convex subcomplex."
- (L3) Lemma B.10: "Any finite combinatorially convex subcomplex of a combinatorially CAT(0) cubical complex is
  contractible."

None of these assumes local finiteness or finite dimension.

**Step 0 (reduced cellular homology of `X` vanishes).** By (L1), `X` is combinatorially CAT(0).

- Let `z` be a reduced cellular `k`-cycle, meaning `k ≥ 1`, or `k = 0` with augmentation 0.
- `z` is a finite chain, so it lies in a finite subcomplex. By (L2) this subcomplex lies in a finite
  combinatorially convex subcomplex `E`. By (L3), `E` is contractible.
- So `z` is a boundary in `E`, hence in `X`.

The augmented cellular chain complex `… → C_1(X) → C_0(X) → Z → 0` is therefore exact.

**Step 1 (`F` permutes cubes freely).** Fix `F ≤ G`. `F` is torsion-free (item 1 of
`thompson-f-has-infinite-cohomological-dimension`).

- *Vertex stabilizers.* `Stab_F(v)` is a subgroup of the finite group `Stab_G(v)`, so it is finite, hence
  trivial.
- *Cube stabilizers.* Let `C` be a cube. `Stab_F(C)` permutes the finite set `C⁽⁰⁾`. The kernel of this
  permutation action fixes a vertex, so it is trivial. Hence `Stab_F(C)` embeds in a finite symmetric group, so
  it is finite, hence trivial.

So `F` acts freely on the set of `k`-cubes for every `k`. Choose one `k`-cube in each `F`-orbit and orient it.
Give each other `k`-cube `gC` the orientation transported by the unique `g` carrying `C` to it.

- Then `F` permutes the oriented basis of `C_k(X)`, so `C_k(X)` is a free `ZF`-module.
- The boundary maps are `F`-equivariant, since `F` acts by cellular automorphisms.

**Step 2 (item 1).** Suppose `dim X = d < ∞`. Then `C_k(X) = 0` for `k > d`. By Steps 0 and 1,

`0 → C_d(X) → … → C_1(X) → C_0(X) → Z → 0`

is a free resolution of the trivial `ZF`-module `Z` of length `d`. So `cd_Z F ≤ d`. This contradicts item 3 of
`thompson-f-has-infinite-cohomological-dimension`. Hence `X` is infinite-dimensional.

**Step 3 (item 2).** By the Theorem in `cat0-cube-complexes-with-property-a-are-finite-dimensional`, if `X⁽⁰⁾`
had property A then `X` would be finite-dimensional, which contradicts Step 2. ∎

**Remarks (not load-bearing).**

- *Metrically proper actions.* A metrically proper action has finite vertex stabilizers. For finitely generated
  `F` it also makes the orbit map `g ↦ g·v` a coarse embedding. A coarse embedding into a space with property A
  would give `F` property A, hence exactness. This is the route killed here, and it dies at Step 3 for every
  host.
- *The invariant.* The argument needs only a torsion-free subgroup of infinite `cd` and finite stabilizers. So
  it applies verbatim to every group containing `Z^∞ = ⊕_N Z`, and to every group containing `F`.
- *Calibration.* Nothing here says `F` is not exact. The argument sees only `cd F = ∞`, which `Z^∞` shares, and
  `Z^∞` is amenable. So a proper cubical host carries no information about exactness or amenability of an
  infinite-`cd` group, and every such host is useless for that purpose.
- *What survives.* Exactness of `F` from actions with infinite stabilizers stays open, for example through a
  finite-dimensional cubical host whose cell stabilizers are exact. Such a route needs the stabilizers to be
  known exact, and for `F` it is not known to be non-circular.

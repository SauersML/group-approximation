---
rg: 2
id: canonical-algebras-embed-in-algebraic-uniform-roe-algebras
kind: claim
title: For every finitely generated group Γ with solvable word problem, the canonical algebra R_Γ embeds unitally in a coarsely dense diagonal corner of M_n of the algebraic uniform Roe algebra C_u[F_2; F_2] of the free group (algebraic Kirchberg–Roe embedding; linear gate U with no computability)
distinct_from:
  decidable-algebras-embed-in-oracle-leavitt-crossed-products: that asks for an oracle subshift and an embedding over Z tensored with L, for every decidable algebra; this asks, for the canonical simple algebras only, for a coefficient-free embedding into the uniform Roe algebra of one tree, which by Theorem A of the required node already produces the effective oracle.
  infinite-kazhdan-group-in-wobbling-group-of-product-of-trees: that is the permutational (full-group) form of gate U over F_2 × F_2; this is the linear form over F_2 alone, where the permutational caps do not apply (non-amenable-scaffolds-absorb-the-leavitt-factor).
---

Inputs this claim recorded under the older schema (not a proof; they do not establish it): `linear-gate-u-reduces-to-algebraic-uniform-roe-embeddings`.

**OPEN.** For every finitely generated `Γ` with solvable word problem, `R_Γ = LC(2^Δ, F_2) ⋊ (Z/2 ≀ Δ)`, with
`Δ = C(Γ)`, has an `F_2`-module of bounded geometry in the sense of
`linear-gate-u-reduces-to-algebraic-uniform-roe-embeddings`. That is:
- a faithful unital module with a basis;
- a map from the basis to the free group, with fibres of size at most `n` and coarsely dense image;
- generators of finite propagation along that map.

Nothing is required to be computable.

## Why it is the linear core of gate U

- By Theorems A and B of the required node, this claim puts every decidable `Γ` into
  `GL_(3n)(LC(W, F_2) ⋊ F_2)`, with `W` effectively closed and free, injectively on every minimal subsystem.
- Over the scaffold `F_2 × Z²`, gates M1 and G2 then finish Boone–Higman through Khanh. Farrell–Jones holds
  for `F_2 × Z²`, so the K-gate is paid once.
- The weaker form with `F_2` replaced by a fixed finitely presented torsion-free Farrell–Jones group, such as
  `Z × F_2` or `F_2 × F_2`, serves the same purpose.

## Evidence and calibration

- **C*-analogue: true exactly for exact `Γ`** (Theorem C of the required node). For exact `Γ`, Kirchberg puts
  `C(2^Δ) ⋊_r (Z/2 ≀ Δ)` into `O_2 ⊆ C*_u(F_2)`. Non-exact `Γ` never embed that way, and decidable non-exact
  `Γ` exist.
  - So the claim for non-exact `Γ` holds only if the algebraic Roe algebra over `F_2` is *not* "algebraically
    exact" (Theorem D there).
  - The first place to look is `L^x ⊆ GL_1(LC(X_par) ⋊ F_2)`, whose exactness is open.
- **Free-orbit modules are not enough.** On an orbit module of `R_Γ` with trivial stabilizers, the support
  graph is a Cayley graph of `Z/2 ≀ Δ`, and the separation caps of
  `translation-like-hosts-are-capped-by-separation-profiles` apply. For `Γ = Z` the group `Δ` contains
  `Z ≀ Z`, hence undistorted `Z^n` for every `n`, so the cap excludes these modules over `F_2` and over
  `Z × F_2`. What remains open is orbits with stabilizers, and modules on which `Δ` does not act monomially.
  The model for the latter is `EL_3(F_2[t]) ⊆ GL_3(L)` on three rays.
- **Rings already inside, faithfully and with bounded geometry over `F_2`:**
  - `L` and every countable-graph Leavitt path algebra;
  - free algebras and `F_2[t]`;
  - tensor products of such rings with the monomial algebras of decidable subshifts, over `Z × F_2`
    (`subshift-languages-give-monomial-algebras-in-crossed-products`).

## Test cases, in order

1. `Γ = 1`: here `Δ = Z`, and `R_1 = LC(2^Z) ⋊ (Z/2 ≀ Z)` is the lamplighter crossed product. It passes over `F_2 × F_2`:
   - `Z/2 ≀ Z` acts freely, with bounded displacement, on every level set of `h_1 + h_2` in `T_3 × T_3` (Diestel–Leader);
   - so a direct sum of free-orbit modules is a bounded-geometry module on all of `T_3 × T_3`;
   - `T_3 × T_3` is bilipschitz to `Cay(F_2 × F_2)` (recalled).
   Over `F_2` alone no module is known.
2. `Γ = Z`. This is exact and amenable, and every free-orbit module is capped over `F_2` and over `Z × F_2`.
3. `Γ` a decidable graphical small cancellation group with embedded expanders
   (`decidable-graphical-non-exact-groups-exist`). This is the decisive case: a module there is the
   algebraic escape from exactness.

## Lesson for general BH

Once the input is simple, linear gate U over a fixed tree is a statement about one explicit algebra per input
and one classical object, the uniform Roe algebra of the free group. Neither computability nor Kazhdan-type
rigidity enters. Its C*-shadow is Kirchberg's O_2-embedding, which solves every exact input. What is left to
invent is an algebraic, finite-field version of that embedding. The deciding question is whether such an
embedding can exist at all for a non-exact input.

---
rg: 2
id: thompson-f-hyperbolic-actions-have-a-finite-boundary-orbit
kind: claim
title: "Every unbounded isometric action of Thompson's F on a Gromov-hyperbolic space has a boundary orbit of size at most 2 fixed pointwise by a subgroup of index at most 2 containing F', and F' has no loxodromic element; so hyperbolic-boundary amenable-action routes to amenability or exactness of F are root-equivalent"
distinct_from:
  stein-farley-height-fixes-a-roller-boundary-point: that finds a fixed Roller point for F's one proper cubical action; this covers every isometric action on every Gromov-hyperbolic metric space, proper or not, where the fixed point comes from the absence of free subgroups rather than from a height.
  thompson-f-has-no-cobounded-action-on-spaces-qi-to-h2: that excludes cobounded actions on spaces quasi-isometric to H^2; this allows every hyperbolic space and every unbounded action, and describes those actions instead of excluding them.
  cobounded-qi-h2-actions-without-free-groups-are-focal: that is the cobounded QI-H^2 case of the classification, with the lineal case excluded by coboundedness; here the lineal case is kept and forms the size-2 orbit.
  thompson-f-quasimorphisms-vanish-on-f-prime: that is the vanishing of homogeneous quasimorphisms on F; this reruns its swindle on an index-2 subgroup and turns it into the absence of loxodromics in F'.
---

**ESTABLISHED** by `thompson-f-hyperbolic-actions-have-a-finite-boundary-orbit-proof`, modulo the Das–Simmons–Urbański
classification. That classification is quoted verbatim from arXiv:1409.2155v7, but its proofs were not checked.
The claim has not been independently reviewed.

**Setting.** `X` is a Gromov-hyperbolic metric space in the sense of DSU (four-point inequality with one constant `δ`).
It need not be geodesic or proper. `∂X` is the sequential Gromov boundary. `F` acts on `X` by isometries, and the orbit
`F·o` is unbounded.

**Theorem.**

1. **Finite boundary orbit.** There are `ξ ∈ ∂X` and a subgroup `F_0 ≤ F` of index at most 2 such that `F_0` fixes `ξ`,
   `F·ξ` has at most 2 points, and `F_0` fixes `F·ξ` pointwise. Since `F/F_0` is abelian, `F' ≤ F_0`.
   - If the image of `F` is parabolic or focal (DSU Definitions 6.2.2 and 6.2.13), then `F_0 = F`.
   - If it is lineal, `F·ξ ⊆ {ξ, η}`, where `{ξ, η}` is the common fixed pair of the loxodromics.
   - General type is impossible.
2. **Loxodromics are read off `F_0/F'`.** There is a homomorphism `ℓ: F_0 → R` with `ℓ(F') = 0` such that `k ∈ F` acts
   loxodromically iff `k ∈ F_0` and `ℓ(k) ≠ 0`. Explicitly, `ℓ` is the Busemann pseudocharacter at `ξ`, and
   `ℓ(k) = −log_b k'(ξ)` for every `k ∈ F_0`, where `k'(ξ)` is the DSU dynamical derivative. `F_0/F'` is a subgroup
   of `F/F' ≅ Z^2`. In particular, **no element of `F'` acts loxodromically in any isometric action of `F` on any
   hyperbolic metric space.**
3. **Class killed.** Let `Z` be a compact Hausdorff `F`-space that contains a finite `F`-orbit. Examples are any
   `F`-space `Z` receiving an `F`-equivariant map (continuous or not) from `∂X`, and `∂X` or `bord X = X ∪ ∂X` itself
   whenever it is compact, for example when `X` is proper and geodesic. Then `F ↷ Z` is topologically amenable iff `F` is amenable.
   - This kills the Adams / Kaimanovich / Ozawa template "amenable action on a hyperbolic boundary", for every
     unbounded hyperbolic action of `F`, as a route to amenability of `F`. It also kills it as a route to
     **exactness of `F`**, which to our knowledge is open: any such proof proves amenability.
   - *Dying step:* average the approximately equivariant maps `m_n: Z → Prob(F)` over the finite orbit `F·ξ`.
4. **Quantitative pin.** Suppose `m: Z → Prob(F)` has `supp m(z) ⊆ B_r` for all `z` and `‖s·m(z) − m(sz)‖₁ ≤ ε` for all
   `s` in a symmetric generating set `S`. Then `ν = (1/|F·ξ|) Σ_{z∈F·ξ} m(z)` is an `ε`-Reiter measure supported in
   `B_r`. So, exactly as in item 4 of `stein-farley-height-fixes-a-roller-boundary-point`,
   `Føl_F(⌊1/(|S|ε)⌋) ≤ (2|S|+1)^r`, and Moore's tower bounds `r` from below.

**Scope: what is not killed.**
- *Bounded actions.* An action with bounded orbits can have a large boundary on which `F` acts in an arbitrary way,
  for example through a coset tree of a chain of subgroups. That is a general compact `F`-space, not hyperbolic
  geometry, and it is not covered.
- *Atomless measure classes.* Zimmer amenability of `(∂X, μ)` with `μ(F·ξ) = 0` is not covered. For example, the
  Poisson boundary of any random walk is Zimmer amenable for every group. If `μ(F·ξ) > 0`, restricting to the
  finite orbit gives the same collapse. That remark rests on the standard fact that `G ↷ G/H` is Zimmer amenable
  iff `H` is amenable, which is not proved here.
- *Horofunction compactifications.* They map onto `∂X`, not from it. The fibre over `ξ` is only an
  `F_0`-invariant compact set, which need not contain a finite orbit.

**Calibration: the invariant carries no amenability information.**
- Item 1 uses only one property of `F`: it has no non-abelian free subgroup. It therefore holds verbatim for every
  such group, and in particular for Adian's non-amenable free Burnside groups `B(m,n)` (`m ≥ 2`, `n ≥ 665` odd).
  They are torsion, so every element is elliptic and every unbounded action is parabolic and fixes a point of `∂X`.
  Adian's non-amenability theorem (1982) is cited, not checked.
- So no argument that uses only "every unbounded hyperbolic action has a finite boundary orbit" proves amenability.
  A hyperbolic-geometry proof would have to use item 2, the fact that `F'` is invisible to loxodromics. That item
  pushes all hyperbolic information about `F` into the abelianization `Z^2`, so it cannot see the amenability of
  `F'`, which is equivalent to that of `F`.
- *Non-vacuity* (remarks, not part of the established statement):
  - `χ_0: F → Z` (the log-slope at `0`), composed with translation on `R`, is lineal with `F_0 = F`.
  - The Bass–Serre tree of `F` as the ascending HNN extension of `⟨x_1, x_2, …⟩ ≅ F` by `x_0` is focal.
  - It is not known here whether `F` has a parabolic (horocyclic) unbounded action, or a lineal one with
    `F_0 ≠ F`.

**Prior art, not read.** Balasubramanya, Fournier-Facio and Genevois (property (NL); the reference was not
checked) and arXiv:2406.12982 study hyperbolic actions without loxodromics and pseudocharacters of subgroups of `PL^+(I)`.
Item 2 may be stated there, and item 1 is folklore from Gromov's classification. The new content is the class
kill in items 3 and 4, for all hyperbolic spaces at once, with the dying step made explicit.

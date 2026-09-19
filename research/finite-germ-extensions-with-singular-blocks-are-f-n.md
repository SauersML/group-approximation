---
rg: 2
id: finite-germ-extensions-with-singular-blocks-are-f-n
kind: claim
title: The Belk–Hyde–Matucci finite germ extension finiteness theorem holds verbatim with singular points replaced by pairwise disjoint closed blocks permuted by the group; but full groups with a Thompson subgroup have no nontrivial blocks, and for the coset blocks of G*Z the transport base is not finitely generated, so hyperbolic F_∞ hosts cannot come from germ extensions over coset blocks
distinct_from:
  bbmz-host-finiteness-reduces-to-the-vertex-boundary-groupoid: that observes the finite germ theorem does not apply to the BBMZ host with coset pieces; this proves the block version of the theorem and shows the obstruction is intrinsic to every block system of that shape.
  thumann-finiteness-without-finite-type: that is a global operad finiteness theorem with a connectivity condition (G); this is the germ-local theorem, and it points to (G) as the only remaining route.
---

**ESTABLISHED** (lane proof, bh-finf-hyp, 2026-09-18; not reviewed; no priority claimed).
- Item 1 transfers the proof of Belk–Hyde–Matucci (arXiv:2407.03149): Theorem
  `thm:SingFixFiniteness`, Propositions `prop:FinitnessPropertiesFiniteIndex` and
  `prop:FinitnessPropertiesNormalSubgroups`, and Corollary `cor:MainFinitenessCorollary`. It was
  read in the TeX source; the changes are listed below.
- Items 2 and 3 are elementary.

## 1. The block germ extension theorem

**Setting.**
- `X` is a compact metrizable space, and `B ≤ Γ ≤ Homeo(X)`.
- `𝒴` is a family of pairwise disjoint nonempty closed subsets (*blocks*) that `Γ` permutes.
- `γ` is *singular along* `Y ∈ 𝒴` if it agrees with no element of `B` on any neighbourhood of
  `Y`. Write `sing(γ) ⊆ 𝒴` for the set of such blocks.
- `Γ` is a *finite block-germ extension* of `B` if:
  - every `γ` is singular along finitely many blocks, and agrees locally with `B` at every point
    outside them;
  - `B = {γ : sing(γ) = ∅}`;
  - for every `γ` and `Y ∈ sing(γ)`, some `h ∈ Γ` has `sing(h) = {Y}` and agrees with `γ` near
    `Y`.
- **Germs.** `(γ)_Y` is the set of elements agreeing with `γ` on a neighbourhood of `Y`. The
  germ group along `Y` is `(Γ)_Y = Stab_Γ(Y)/RStab_Γ(Y)`, where `RStab` means "the identity on
  a neighbourhood of `Y`". `(B)_Y` is its image of `Stab_B(Y)`.
- `Fix_B(M) = {b ∈ B : bY = Y for all Y ∈ M}`.

**Theorem.** Let `n ≥ 1`, and suppose:
- (a) `B` acts on `𝒴^n` with finitely many orbits;
- (b) `Fix_B(M)` is of type F_n for every `M ⊆ 𝒴` with `|M| ≤ n`, including `B` itself;
- (c) for every `Y`, either `|(Γ)_Y : (B)_Y| < ∞`, or `(B)_Y ⊴ (Γ)_Y` and `(Γ)_Y/(B)_Y` is of
  type F_n.

Then `Γ` is of type F_n.

**Proof: what changes in the source.** Each step is used as written, with "point `p`" read as
"block `Y`":
- germs `(γ)_p` become germs along `Y`;
- `Fix` becomes setwise fixing of blocks;
- `RStab` becomes "the identity near the block".

Three facts are used.
1. **Composition.** `sing(kh) ⊆ h^{-1}sing(k) ∪ sing(h)`. If `h` agrees with `b` near `Y` and `k`
   agrees with `b'` near `hY`, then `kh` agrees with `b'b` near `Y`.
2. **Disjoint neighbourhoods.** Finitely many disjoint closed blocks have pairwise disjoint
   neighbourhoods, since `X` is normal. This is what `lem:CompatibleBGerms` needs, together with
   the localization axiom.
3. **The germ complex.**
   - It is `K = ∏'_{Y∈𝒴} T_Y`, a restricted product of star trees on the `B`-germs along `Y`,
     with the same Morse function and the same joins of discrete sets.
   - The descending links are joins, so `K_{≤n}` is `(n−1)`-connected.
   - The cell stabilizers are commensurable with `SingFix_Γ(M, M')`.

   Propositions `prop:FinitnessPropertiesFiniteIndex` and
   `prop:FinitnessPropertiesNormalSubgroups` use only the homomorphism to `∏_{Y∈M} (Γ)_Y`,
   whose kernel is `Fix_B(M')`. `∎`

## 2. Full groups with a Thompson subgroup have no nontrivial blocks

**Proposition.** Let `Γ ≤ Homeo(E)` contain `V_{Γ,E}` for a subshift of finite type with
irreducible core, and let `𝒴` be a `Γ`-permuted family of disjoint closed sets.
- Every block with at least two points is all of `E`.
- In particular, the coset pieces `Y_v ⊂ ∂_h(G*Z)` are not blocks for `[[G*Z | ∂_h]]`.

**Proof.**
- Suppose `Y` has two points `x ≠ y` and misses some `z`.
- Take disjoint cones `C_x ∋ x`, `C_y ∋ y` and `C_z ∋ z` with `C_z ∩ Y = ∅`. We may take
  `C_y` of core type.
- Choose a cone `C′ ⊆ C_z` of the same type as `C_y`. It exists because the core is irreducible.
- Let `g ∈ V_{Γ,E}` swap `C_y` and `C′` by canonical similarities and fix everything else. Then
  `g` fixes `x`.
- So `gY ∩ Y ∋ x`, which forces `gY = Y`. But `gY ∋ gy ∈ C′ ⊆ C_z`, which misses `Y`. This is a
  contradiction. `∎`

## 3. Coset blocks force an infinitely generated base

**Setting.** Let `Γ` be any group of homeomorphisms of `∂_h(G*Z)`, or of its Bowditch quotient,
with the following properties:
- `Γ` contains `H = G*Z`, with `G` infinite;
- `Γ` preserves the coset blocks `{Y_v}`, respectively the vertex points;
- `Γ` agrees locally with `H` everywhere;
- `Γ` is *block-full*: it contains every block-preserving homeomorphism that is piecewise `H` on a
  finite clopen partition.

Take as base the elements whose germ along every block is a pure transport in reduced-word
coordinates.

**Claim.** Every such base `B` is **not finitely generated**.

**Proof.**
- **Neighbourhoods of a block.** A clopen neighbourhood of `Y_v` contains all but finitely many
  branch shadows at `v`. Its complement is compact, and it is covered by finitely many shadows,
  by the decomposition of `bbmz-host-finiteness-reduces-to-the-vertex-boundary-groupoid`,
  item 1.
- **Finite letter support.** A transport germ therefore fixes all but finitely many branch letters
  at `v`. Each `b ∈ B` is piecewise `H` on finitely many clopen pieces, so it changes only a
  finite set `L(b)` of branch letters `(g, ε) ∈ G × {±}`.
- **Commutation.** It follows that `b` commutes with the letter swap `σ_{λμ}`, the coordinate
  relabeling exchanging `λ` and `μ`, for all `λ, μ ∉ L(b)` of the same sign.
- **Conclusion.** `B` contains the transpositions `τ_{λν}` of the half-trees `λ` and `ν` at the
  root, given by left multiplication by an element of `G`. They lie in `B` because their germs at the vertices they move are the transports `u_{v′}u_v^{-1}`. They satisfy
  `σ_{λμ} τ_{λν} σ_{λμ} = τ_{μν} ≠ τ_{λν}`, for letters with nontrivial `G`-entry. A finitely generated subgroup has finite total
  letter support `L`, and so it commutes with `σ_{λμ}` for `λ, μ ∉ L`. Hence it misses `τ_{λν}`
  for all such `λ`. `∎`

So hypothesis (b) of item 1 fails at `n = 1` for every block system built from the cosets of
`G`. Enlarging the base so that its germs move letters puts `G`'s germs into `(B)_Y`. Then (c)
asks for `(Γ)_Y/(B)_Y`, and (b) asks for `F_n` of a base that again contains every piecewise-`G`
move along the blocks. That is the original problem.

## Consequence for the F_∞ half of Zaremsky's question

- **Germ-local methods over coset loci cannot reach F_∞ here.** No finite germ extension argument
  whose singular loci are the coset blocks, or the vertex points, and whose base is the transport
  group, reaches F_∞ for the BBMZ host or for the free-product stabilizer engine of a hyperbolic
  group. By item 2 no other block system is available in the full group.
- **The route that is left** is a global complex with infinitely many elementary moves. Take the
  *shadow operad*:
  - colours are the atom types;
  - operations are all partitions of a model shadow into `H`-translates of shadows;
  - transformations are single `H`-maps between shadows.
- **What already holds for the shadow operad.**
  - **Square filling holds.** Every clopen partition refines into shadows of one family.
  - **Finitely many colours** hold.
  - **The transformation groups are setwise stabilizers of clopens in `H`.** They are virtually
    cyclic or finite, if no non-elementary subgroup stabilizes a proper shadow translate. This is
    expected, but not proved here.
  - **Bounded depth.** Finitely many nucleus image shapes should bound the depth of a partition
    into `k` pieces. That would give Thumann's (Cc).
- **What is open.** The very elementary degree bound (VE), and the connectivity condition (G) of
  `thumann-finiteness-without-finite-type` for large elementary partitions. The configuration
  types of `horofunction-atom-configurations-have-finitely-many-types` are the finite data that
  (G) must be checked on.

## Lesson for general BH

- **Singular sets that are not points exist in theory, but full groups forbid them.** The finite
  germ extension theorem survives the change from singular points to singular blocks. But a full
  group containing a Thompson group has no nontrivial blocks. Any block-preserving subgroup that
  contains an infinite vertex group has an infinitely generated transport base, because only the
  vertex group changes branch letters.
- **So a hard input must be absorbed by a global complex.** Germ-local finiteness theory, with
  points or blocks, handles inputs whose germs are virtually cyclic or sit in F_∞ quotients of a
  finite-type base. A hard input sitting at an infinite emitter is never such an input.
- **For hyperbolic inputs, the F_∞ gate is now one concrete connectivity statement.** It is the
  connectivity of Thumann splitting categories for large partitions of shadows into shadow
  translates, over finitely many configuration types.

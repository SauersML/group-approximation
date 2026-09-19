---
rg: 2
id: rank-one-cut-outs-kill-amenable-non-abelian-quotients
kind: claim
title: "If a witness is cut out through factors whose closed amenable subgroups are compact or virtually solvable (PGL_2 and SL_2 over local fields of every characteristic, including F_2((t))), with the host injective on each nonempty subproduct and all its virtually solvable subgroups virtually abelian (cocompact CAT(0), e.g. irreducible cocompact lattices), then every amenable quotient P is virtually abelian; so the two-sided characteristic-2 completion of Z/2 wr Z cannot come from any S-arithmetic-type rank-one lattice, and a witness needs a non-solvable amenable factor such as Aut(T)"
distinct_from:
  ascending-completions-give-only-virtually-cyclic-quotients: That kills ascending completions (one contracting letter) and leaves the two-sided case; this kills two-sided completions of rank-one type, including the model (F_2((t)) x F_2((1/t))) x| Z, whenever the host is VSA and faithful on subproducts.
  commensurated-witnesses-survive-browder-but-die-when-linear: That kills characteristic-0 p-adic cut-outs by bounding finite-subgroup ranks, which fails in characteristic p (F_2[[t]] is elementary abelian of infinite rank); this works in every characteristic, by amenability and the solvable subgroup theorem instead of ranks, but needs rank one.
  commensurated-cat0-witnesses-force-finite-rational-cd: That bounds cd_Q of P by the dimension of a CAT(0) complex, which Z/2 wr Z passes on T_3 x T_3; this excludes Z/2 wr Z and every amenable non-virtually-abelian P for rank-one factors.
  f-cores-reduce-benign-witnesses-to-normalized-ones: That kills witnesses whose F-core has finite index; the witnesses here may have infinite-index cores.
---

**ESTABLISHED (proposed, 2026-09-18; referee welcome).** Setting as in
`ascending-completions-give-only-virtually-cyclic-quotients`: `F` free and
finitely generated, `N ⊴ F`, `P = F/N`, a witness `Σ ≤ Λ` and a
homomorphism `φ : F -> Λ` with `φ^{-1}(Σ) = N`. Nothing is assumed about
torsion or finiteness type.

**Definitions.**
- A locally compact group `G_j` is **AS** if every closed amenable subgroup
  of `G_j` is compact or virtually solvable. Examples:
  - `PGL_2(k)`, `SL_2(k)` and `PSL_2(k)` for every non-archimedean local
    field `k`, of **any characteristic**, e.g. `k = F_2((t))`;
  - `PSL_2(R)` and `PSL_2(C)` (these can only sit in `G'` below, since a
    connected non-compact factor admits no compact open `K`);
  - compact groups, virtually solvable groups, and `D^×/k^×` for a
    division algebra `D`.
- A group `Λ` is **VSA** if each of its virtually solvable subgroups is
  virtually abelian. By the solvable subgroup theorem
  (Bridson–Haefliger II.7.16), every group acting properly and cocompactly
  on a CAT(0) space is VSA. This includes every cocompact lattice in a
  product of trees, buildings and rank-one symmetric spaces, and every
  hyperbolic group.

**Theorem.** Let `ρ : Λ -> G = G_1 × ... × G_s` be a homomorphism with each
`G_j` AS, and let `K ≤ G` be compact open with `Σ = ρ^{-1}(K)`. More
generally, it is enough that `Σ ∩ H = ρ^{-1}(K) ∩ H` for `H = φ(F)`.
Assume:
- `Λ` is VSA;
- `pr_I ∘ ρ` is injective on `Λ` for every nonempty `I ⊆ {1, ..., s}`.

If `P` is amenable, then `P` is **virtually abelian**. It is finite when all
the closures of `pr_j ρ(H)` are compact.

**Corollaries.**
1. **Lattice-type witnesses.** Let `Λ` be an irreducible cocompact lattice
   in `G' × G_1 × ... × G_s`, where the `G_j` are simple AS groups (for
   example `PGL_2` over local fields of characteristic 2), and let
   `Σ = Λ ∩ (G' × K)`. Then no such witness realizes `Z/2 ≀ Z`, `BS(1,n)`
   for `n ≥ 2`, Grigorchuk's group, or any amenable `P` that is not
   virtually abelian. Here `G'` is arbitrary, and `Σ` is then a cocompact
   lattice in `G' × K`.
   - This covers the arithmetic lattices of quaternion algebras over
     `F_q(t)`. These are torsion-free after finite index, since
     `1 + π O_D` is torsion-free in a division algebra, and they act on
     products of trees.
   - So the model two-sided completion
     `(F_2((t)) × F_2((t^{-1}))) ⋊ Z` of the brief, and every Borel
     subgroup of `PGL_2(F_2((t))) × PGL_2(F_2((t^{-1})))`, is never the
     completion of such a witness.
2. **Sections.** For every witness, `P = H/(H ∩ Σ)` is a section of `Λ`.
   So if `Λ` has finite Prüfer rank, `P` has finite Prüfer rank and is not
   `Z/2 ≀ Z`. This covers every soluble group of type `FP_∞` (Kropholler:
   such groups are constructible).
3. **What a witness for `Z/2 ≀ Z` now needs.** Combined with
   `ascending-completions-give-only-virtually-cyclic-quotients`, a
   commensurated witness for `Z/2 ≀ Z` whose cut-out factors through a
   product must have one of the following:
   - (a) a factor `G_j` with a closed amenable subgroup that is neither
     compact nor virtually solvable, and a non-compact projection of `Ĥ`
     into it. Examples are `Aut(T)` (end stabilizers contain huge compact
     groups), higher-rank groups, and `SO(n,1)` for `n ≥ 3`;
   - (b) or a host `Λ` that is not VSA, i.e. contains a virtually solvable
     subgroup that is not virtually abelian. Such a `Λ` is not cocompact
     CAT(0);
   - (c) or a non-injective subproduct projection, i.e. a reducible
     lattice. In the reducible case the direct factor kills it when
     `Λ ∩ (G' × 1)` is a lattice in `G'`, by Browder, since then
     `Σ ⊇ C ⊴ Λ` with `[Σ : C] < ∞`.

**Sharpness.**
- The AS hypothesis is what fails for tree groups. `Z/2 ≀ Z` is a
  discrete subgroup of `Aut(T_3) × Aut(T_3)` acting freely on the vertices
  of the Diestel–Leader graph `DL(2,2)`. So `Ĥ = Z/2 ≀ Z` with `M = 1` is a
  closed compact-by-`P` subgroup there, and its end stabilizers are
  amenable but not virtually solvable. Whether such an `Ĥ` is reached from
  a VSA host is exactly item 3(a).
- The conclusion "virtually abelian" is attained. Let `Λ` be a
  torsion-free irreducible cocompact lattice in `PGL_2(Q_p) × PGL_2(Q_q)`,
  `K` so small that `Λ ∩ K = 1`, and `H ≅ Z^2` a flat subgroup. Then
  `P = H = Z^2`.

Proof: route `rank-one-cut-outs-kill-amenable-non-abelian-quotients-proof`.

## Attempts

- 2026-09-18 (w16-117): theorem and corollaries 1–3 proved.
  Proposed-established. Open: a witness of type (3a) with an `Aut(T)`
  factor, e.g. an irreducible torsion-free lattice in a product of three
  trees whose projection to two factors has closure compact-by-`Z/2 ≀ Z`
  on a `DL(2,2)` orbit; or a proof that the `Aut(T)` end stabilizers
  cannot occur either.

---
rg: 2
id: rank-one-cut-outs-kill-amenable-non-abelian-quotients-proof
kind: route
title: "Proof: the closure of rho(H) is compact-open-normal-by-P, hence amenable when P is; its projection closures are amenable, hence compact or virtually solvable in AS factors (Adams-Ballmann on the Bruhat-Tits tree); injectivity on the non-compact subproduct makes H virtually solvable, so virtually abelian in a VSA host, and P = H/(H cap Sigma) is virtually abelian"
target: rank-one-cut-outs-kill-amenable-non-abelian-quotients
requires:
  - ascending-completions-give-only-virtually-cyclic-quotients
  - commensurated-witnesses-survive-browder-but-die-when-linear
---

Verification tier: proposed-established. The ingredients are the
compact-open-normal step of
`ascending-completions-give-only-virtually-cyclic-quotients` (reproved in
Step 1), two standard facts on amenable locally compact groups, the
Adams–Ballmann theorem and the solvable subgroup theorem.

## Step 0: reduction to H

Let `H = φ(F)`. Since `ker φ ⊆ φ^{-1}(Σ) = N`, the map `φ` induces
`P = F/N ≅ H/φ(N)`, and `φ(N) = H ∩ Σ`. This subgroup is normal in `H`
because `N ⊴ F`. By hypothesis `H ∩ Σ = H ∩ ρ^{-1}(K)`.

## Step 1: Ĥ is compact-open-normal-by-P

Put `R = ρ(H)`, `Ĥ = closure(R)` in `G` and `M = Ĥ ∩ K`.
- `M` is compact and open in `Ĥ`.
- `R ∩ K = ρ(H ∩ Σ)` is normal in `R`. For `r ∈ R`, the sets `rMr^{-1}` and
  `M` are both open in `Ĥ`. The dense subgroup `R ∩ K` of `M` (dense
  because `M` is open in `Ĥ` and `R` is dense in `Ĥ`) is carried to itself.
  So `rMr^{-1} = closure(r(R∩K)r^{-1}) = closure(R∩K) = M`.
- The normalizer of the closed subgroup `M` is closed, and it contains the
  dense subgroup `R`. So `M ⊴ Ĥ`.
- `Ĥ/M` is discrete, since `M` is open. The map `R -> Ĥ/M` is onto, since
  `R` is dense and `RM` is open, hence closed. Its kernel is `R ∩ M = R ∩ K`.
  So `Ĥ/M ≅ R/(R ∩ K) ≅ H/(H ∩ Σ) ≅ P`. The middle isomorphism holds
  because `ρ` restricted to `H` has kernel inside `H ∩ ρ^{-1}(K) = H ∩ Σ`.

## Step 2: amenability passes to the projection closures

Assume `P` is amenable.
- `Ĥ` is an extension of the compact group `M` by the discrete amenable
  group `P`. Extensions of amenable locally compact groups are amenable, so
  `Ĥ` is amenable.
- Let `X_j = closure(pr_j(Ĥ)) ≤ G_j`. If `X_j` acts continuously and
  affinely on a nonempty compact convex set, then `Ĥ` has a fixed point
  (acting through `pr_j`). The fixed set of `pr_j(Ĥ)` is closed, and so it
  is fixed by `X_j` by continuity. So `X_j` is amenable.
- Since `G_j` is AS, each `X_j` is compact or virtually solvable.

## Step 3: the dichotomy

Let `J = {j : X_j compact}`.
- **Case `J` is everything.** Then `Ĥ ≤ ∏_j X_j` is compact, so
  `P ≅ Ĥ/M` is compact and discrete, hence finite.
- **Case `I = J^c` nonempty.**
  - `pr_I(ρ(H)) ≤ ∏_{j ∈ I} X_j`, and a finite product of virtually
    solvable groups is virtually solvable. The product of finite-index
    solvable subgroups is a finite-index solvable subgroup.
  - By hypothesis `pr_I ∘ ρ` is injective on `Λ`. So `H` is isomorphic to a
    subgroup of a virtually solvable group, hence virtually solvable.
  - `H ≤ Λ` and `Λ` is VSA, so `H` is virtually abelian.
  - Then its quotient `P = H/(H ∩ Σ)` is virtually abelian.

This proves the theorem. ∎

## Step 4: the AS examples

**Trees.** Let `k` be a non-archimedean local field of any characteristic
and `T` the Bruhat–Tits tree of `PGL_2(k)`. It is locally finite, and the
action is continuous and proper, with compact open vertex and edge
stabilizers.

By Adams–Ballmann (Amenable isometry groups of Hadamard spaces, Math. Ann.
312, 1998), a closed amenable subgroup `A ≤ PGL_2(k)` does one of three
things:
- **It fixes a point of `T`.** Then `A` lies in a vertex stabilizer, or in
  the stabilizer of the midpoint of an edge. That stabilizer is compact, so
  `A` is compact.
- **It fixes an end.** The stabilizer of an end in `PGL_2(k)` is a Borel
  subgroup `B(k)`, the upper triangular matrices modulo scalars. It is
  metabelian, isomorphic to `k ⋊ k^×`. So `A` is solvable.
- **It preserves a geodesic line.** Then `A` lies in the stabilizer of a
  pair of ends, which is `N(S)` for a split torus `S`. The torus has index
  `2` in `N(S)`, so `A` is virtually abelian.

Now pass to `SL_2(k)`, which maps to `PGL_2(k)` with finite kernel.
- Preimages of compact groups are compact.
- Preimages of virtually solvable groups are virtually solvable.

So `SL_2(k)` is AS, and so is its image `PSL_2(k)`, which is closed of
finite index in `PGL_2(k)`.

**Real and complex.** For `PSL_2(R)` and `PSL_2(C)`, acting on `H^2` and
`H^3`, the same trichotomy holds. The three cases give:
- a compact point stabilizer;
- a Borel subgroup, which is solvable;
- the normalizer of a split torus.

**Trivial cases.** Compact groups and virtually solvable groups are AS
trivially. `D^×/k^×` is compact for a division algebra `D` over a local
field `k`.

## Step 5: the corollaries

**Corollary 1.** Let `Λ` be a cocompact lattice in
`G' × G_1 × ... × G_s`, and set `ρ = pr_{G_1 × ... × G_s}`. Then:
- `Σ = Λ ∩ (G' × K) = ρ^{-1}(K)`.
- `Λ` acts properly and cocompactly on the CAT(0) space `X' × ∏ T_j`,
  where `X'` is a CAT(0) model for `G'`. So `Λ` is VSA by
  Bridson–Haefliger II.7.16. This needs `G'` to act properly and
  cocompactly on some CAT(0) `X'`, as for trees, buildings and symmetric
  spaces.
- `Σ` is cocompact in `G' × K`. The subgroup `Λ(G' × K)` is open, hence
  closed, in `G`. So `(G' × K)/Σ` embeds as a closed subset of the compact
  space `G/Λ`.

**Irreducibility.** Here it means: for each nonempty `I`, the projection of
`Λ` to the complementary factor `A_I = G' × ∏_{j ∉ I} G_j` is dense.

**Injectivity.** Assume irreducibility, and that `G'` and every `G_j` have
trivial quasi-centre. This holds for `PGL_2(k)`, because the centralizer of
a nontrivial element is never open. It also holds for centre-free simple Lie
groups. Then `pr_I ∘ ρ` is injective, by the following argument.
- The kernel `D = Λ ∩ (A_I × 1)` is a discrete subgroup of `A_I`.
  Conjugation by `pr_{A_I}(Λ)` preserves it.
- The set `{a ∈ A_I : aDa^{-1} ⊆ D}` is closed, since `D` is closed. It
  contains a dense group, so it is all of `A_I`. So `D ⊴ A_I`.
- For `d ∈ D`, the map `a ↦ ada^{-1}` is continuous from `A_I` into the
  discrete set `D`. So the centralizer of `d` is open, and `d` lies in the
  quasi-centre. If the quasi-centre is trivial, `D = 1`. If it is only
  finite (central `±1` in `SL_2(k)`), then `D` is a finite subgroup of the
  torsion-free `Λ`, so again `D = 1`.

The theorem therefore applies. Every group named in the corollary is
amenable and not virtually abelian:
- `Z/2 ≀ Z`, since its base is infinite and every finite-index subgroup
  contains a non-abelian `F_2[t^{±k}] ⋊ ⟨t^k⟩`;
- `BS(1,n)` for `n ≥ 2`;
- Grigorchuk's group, which is infinite torsion and amenable. An abelian
  finite-index subgroup would be finitely generated, torsion and abelian,
  hence finite.

**Arithmetic example.** Let `D` be a quaternion algebra over `F_q(t)` that
is split at the places of `S` and ramified at some place `w ∉ S`. Then
`SL_1(D)` of the `S`-integers is a cocompact lattice in `∏_{v ∈ S} SL_2(k_v)`.
Its intersection with `1 + π_w O_{D_w}` is torsion-free, for two reasons:
- that pro-`p` group has no torsion prime to `p`;
- `x^p = 1` gives `(x - 1)^p = 0` in characteristic `p`, hence `x = 1` in the
  division algebra `D_w`.

With `|S| ≥ 2` and `G'` one of the factors, Corollary 1 applies.

**The model completion.** The model completion `(F_2((t)) × F_2((t^{-1}))) ⋊ Z`
is contained in the product of the two Borel subgroups, which are
solvable. Any witness whose cut-out factors through
`PGL_2(F_2((t))) × PGL_2(F_2((t^{-1})))` is covered, whenever the host is
VSA and injective on subproducts.

**Corollary 2.** `H` is a subgroup of `Λ` and `H ∩ Σ ⊴ H`, so
`P = H/(H∩Σ)` is a section of `Λ`. Finite Prüfer rank passes to subgroups
and quotients. `Z/2 ≀ Z` contains `(Z/2)^r` for all `r`, so its Prüfer rank
is infinite. Kropholler (1986) shows that soluble groups of type `FP_∞` are
constructible, and constructible soluble groups have finite Prüfer rank.

**Corollary 3.** This lists the negations of the hypotheses of the theorem,
restricted to amenable `P = Z/2 ≀ Z`. The reducible Browder case is item
4(d) of `f-cores-reduce-benign-witnesses-to-normalized-ones`, in its
finite-index-core form. If `C = Λ ∩ (G' × 1)` is a lattice in `G'`, then
`C ⊆ Σ` and `C ⊴ Λ`. Also `Σ/C` embeds in `K` discretely, since
`pr(Λ)` is then discrete, so `Σ/C` is finite. Hence the `F`-core has finite
index.

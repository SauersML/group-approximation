---
rg: 2
id: baumslag-gersten-group-satisfies-boone-higman
kind: claim
title: The Baumslag--Gersten group embeds in a finitely presented simple group
distinct_from:
  one-relator-groups-satisfy-boone-higman: that is Boone--Higman for the whole class of one-relator groups; this is its smallest named torsion-free test case, the Baumslag--Gersten group.
  baumslag-gersten-base-is-elliptic-in-every-tree-action: that is an obstruction to one family of hosts for this group; this is the open embedding question itself.
artifacts:
  - research/artifacts/bh-baumslag-gersten-2026-09-12.md
  - research/artifacts/one-relator-boone-higman-2026-09-12.md
  - research/artifacts/bh-bg-similarity-hosts-2026-09-12.md
---

**OPEN.** Let `BG = < a, t | b a b^-1 = a^2 >`, where `b = t a t^-1`. `BG` has
solvable word problem. It is not residually finite, contains `BS(1,2)`, and is
not hyperbolic. By the Boone--Higman theorem it embeds in a simple subgroup of a
finitely presented group. The question is whether some finitely presented simple
group contains it.

## Attempts

- **Tree hosts (dead).** In every action of `BG` on a tree, its `BS(1,2)` base
  fixes a vertex (`baumslag-gersten-base-is-elliptic-in-every-tree-action`). So
  no Bux--Llosa Isenrich--Wu host over virtually free, abelian or nilpotent
  vertex groups contains `BG`.
- **Linear and rooted-tree hosts (dead).** Every finite image of `BG` kills `a`.
  So `BG` is linear over no field and embeds in no self-similar group
  (`baumslag-gersten-group-is-neither-linear-nor-self-similar`). Neither the
  linear-group Boone--Higman classes nor finitely presented self-similar hosts
  can reach it.
- **Odometer and affine models (dead).** An equicontinuous minimal piece for
  `a`, invariant under `b`, forces fixed points, so the affine self-similar
  models of `BS(1,2)` on `Z_p` do not extend (`baumslag-gersten-odometer-pieces-force-fixed-points`).
  The projective 2-adic similarity model fails by counting fixed points. So `a`
  can never act as a fixed-point-free adding machine on the whole space, and an
  odometer piece for `a` that `b` preserves forces a fixed point of `a`
  elsewhere.
- **Röver--Nekrashevych and Higman--Thompson hosts (dead).**
  - Every homomorphism from `BG` to the almost-automorphism group of a regular
    rooted forest kills `a`
    (`baumslag-gersten-embeds-in-no-rover-nekrashevych-group`).
  - So `BG` embeds in no `V_{d,r}(G)` with `G` self-similar, and in no
    `V_{d,r}`, `V`, `T` or `F`.
  - The FW and (T) criteria cannot give this, because `BG` surjects onto `Z`.
    The obstruction is equicontinuity:
    - the image of `a` is conjugate to its square, so it is equicontinuous
      (`almost-automorphism-conjugate-to-proper-power-is-equicontinuous`);
    - an equicontinuous `a` acts trivially on any compact zero-dimensional
      space (`baumslag-gersten-equicontinuous-generator-acts-trivially`).
- **Graph path-space hosts (dead, 2026-09-13).** Every homomorphism from `BG`
  to the almost-automorphism group `A(E)` of the path space of a finite graph
  kills `a` (`baumslag-gersten-embeds-in-no-graph-almost-automorphism-group`).
  The pumping argument runs on any finite graph, so topological full groups of
  one-sided shifts of finite type with several cone types, and any group acting
  piecewise by prefix replacement followed by path isometries, are excluded.
- **Piecewise-analytic circle hosts (dead, 2026-09-13).** Every homomorphism
  from `BG` to a group of piecewise real-analytic circle homeomorphisms with
  finitely many pieces kills `a`, so its image is cyclic
  (`baumslag-gersten-embeds-in-no-piecewise-analytic-circle-group`).
  - This excludes PL circle groups and piecewise-`PSL_2(R)` groups, among them
    Thompson's `T` and Lodha's finitely presented simple group `S`.
  - For PL groups, including `T` in its PL model, this is not new: an element of
    a PL group conjugate to its square is trivial, so they contain no `BS(1,2)`
    (`bs-1-n-does-not-embed-in-pl-plus-interval` for the interval).
  - The new cases are hosts that do contain `BS(1,2)` with `a` parabolic, such
    as `PSL_2(R)` and Lodha's `S`, which contains `BB(1,2) ⊇ BS(1,2)`
    (arXiv:1710.06220v2, Corollary 5.3). There the obstruction is not
    equicontinuity.
  - Instead, `b` is conjugate to its own square, so it is tangent to the identity
    at its fixed points. But some power of `b` fixes a gap end of `a` with
    derivative `2^(-N/m)`.
  - Analysis of further non-isometric hosts:
    `research/artifacts/solve-bh-nonexpansive-hosts-2026-09-13.md`.
- **Eventually-similar hosts beyond graph path spaces (open).**
  - The obstruction above does not reach local groupoids that are not
    isometric, non-expansive groupoids, or Brin--Thompson `nV`.
  - `fw-subgroups-of-eventually-similar-groups-virtually-embed` needs FW, so
    it does not apply either.
  - In every Cantor-space host, the image of `a` must fail to be
    equicontinuous.
- **Rational similarity groups (open; constrained 2026-09-13).** BBMZ embed
  every hyperbolic group in a full, contracting RSG, through its action on the
  horofunction boundary. `BG` contains `BS(1,2)`, so it is not hyperbolic.
  - The pumping obstruction does not transfer. Local actions of RSG elements can
    change lengths non-uniformly and need not be surjective, so there is no
    locally constant exponent cocycle, and conjugation can rescale periodic
    exponents (§1 of `research/artifacts/bh-bg-rsg-nonisometric-hosts-2026-09-13.md`).
  - Germ groups at rational points are virtually infinite cyclic. So at a
    rational periodic point of `a` with finite `b`-orbit, a power of `a` is the
    identity nearby (`rsg-proper-power-conjugate-germs-torsion-at-finite-orbits`).
    The dyadic affine model of `BS(1,2)`, with `a ∈ F` not equicontinuous, dies
    this way (`dyadic-affine-bs12-model-lies-in-no-finite-nucleus-rsg`).
  - Open: `finite-nucleus-rsg-proper-power-conjugates-are-equicontinuous` would
    exclude every finite-nucleus RSG host, including the BBMZ hosts.
- **Type (A) and twisted Brin--Thompson hosts (open).** By Zaremsky's Theorem A
  (arXiv:2405.18354), `SV_G` is finitely presented exactly when `G` is finitely
  presented and acts faithfully on `S`, with finitely generated point
  stabilizers and finitely many orbits of two-element subsets. Every subgroup
  of such a `G` satisfies Boone--Higman. `BG` acts on the vertices of the
  Bass--Serre tree of its HNN structure with stabilizers conjugate to
  `BS(1,2)`. But tree distance is unbounded, so there are infinitely many
  orbits of two-element subsets. No type (A) action of `BG`, or of a finitely
  presented overgroup, was found. For Brin--Thompson `nV`, the image of `a`
  has exponent vector zero at every periodic point. But the pumping step of
  the Röver--Nekrashevych obstruction fails there, so `nV` stays open.

- **Odometer-extended Brin--Thompson hosts (constrained 2026-09-18).**
  `bg-in-isometric-brick-hosts-needs-unbounded-exponents` covers every
  group of brick maps of `C^n` with isometric sections: `nV`, the finitely presented simple
  `2V_τ` of `odometer-2v-is-fp-simple-and-contains-bs12`, and the affine `2V_{G_N}` hosts.
  - In any such host, a nontrivial image of `a` has zero periodic exponents, unbounded
    exponent sums (bounded sums would make `a` equicontinuous, hence trivial) and zero
    entropy, and so does the image of `b`.
  - So the `BS(1,2) = ⟨s, u⟩` inside `2V_τ` never extends to `BG`: `s = τ × id` has
    `δ_s ≡ 0`, and the baker conjugator `u` has entropy at least `log 2`.
  - What is left in these hosts is the renormalization regime of
    `bs12-embeds-in-brin-thompson-2v`, with a zero-entropy conjugator that is itself
    conjugate to the base. *Open.*

- **Free-product mapping tori, the relative-holomorph engine (dies, 2026-09-18).**
  This is the engine that put the Druţu--Sapir group, the power-map mapping tori and the
  ascending HNN extensions of `pbh-class-closed-under-relative-holomorphs` (T) in `B_A`.
  It cannot produce `BG` unless `M × Z` already contains it. Lane argument, elementary:
  - **Setting.** `Q = M * F` with `F` free and `M ≠ 1`, and `β ∈ Aut(Q)` with `β(M)`
    conjugate to `M`. Suppose `ψ : BG → Q ⋊_β Z` is injective. Write `N = ⟨⟨a⟩⟩ ⊴ BG`,
    `a_i = t^i a t^{-i}`, and `s = ψ(t)`.
  - **Step 1.** `ψ(a) ~ ψ(a)^2` forces `χ(ψ(a)) = 0` for `χ : Q ⋊ Z → Z`, so every `ψ(a_i)`
    lies in `Q`. The element `ψ(a_{i+1}) ∈ Q` conjugates `ψ(a_i)` to its square, so
    `ψ(a_i)` is elliptic on the Bass--Serre tree `T` of `Q`, whose edge stabilizers are
    trivial.
  - **Step 2.** A nontrivial elliptic element of `T` fixes exactly one vertex, and
    `Fix(ψ(a_i)^2) = Fix(ψ(a_i))`. So `ψ(a_{i+1})` fixes the vertex `v_i` of `ψ(a_i)`, and
    all `ψ(a_i)` fix one vertex `v`. Hence `ψ(N) ≤ Stab(v)`, a conjugate of `M`.
  - **Step 3.** Conjugation by `s` maps `Stab(v)` to another conjugate of `M`, which still
    contains `ψ(N)`, so it is `Stab(v)` again. Let `θ` be its restriction. Then
    `n t^j ↦ (ψ(n), j)` embeds `BG = N ⋊ ⟨t⟩` in `Stab(v) ⋊_θ Z ≅ M ⋊_θ Z`.
  - **Step 4.** When `β|_M` is conjugation by an element of `Q`, as in (T), `θ` is
    conjugation by an element of `Q` that normalizes `Stab(v)`. That element lies in
    `Stab(v)`, so `θ` is inner and `BG ≤ M × Z`. Every (T)-group `J*_β` lies in
    `Q ⋊_β Z`.
  - This refines part B5 of `bg-cycle-triviality-is-closed-under-the-pbh-calculus`, which
    is the corresponding statement for BG-cycle triviality, from `𝒫`-membership to
    embeddings.
- **Twisted Brin--Thompson hosts over `𝒫` actors (open, 2026-09-18).** There is no
  reduction to `bs12-embeds-in-brin-thompson-2v` through a global twist.
  - In Zaremsky's definition (arXiv:2405.18354v2, TeX Definition "Twisted Brin--Thompson
    group"), each dyadic brick is moved by a twist homeomorphism with its own `γ_i ∈ G`.
    So `SV_G` has no homomorphism onto `G`, only a locally constant twist cocycle.
  - The tempting argument "`G ∈ 𝒫` kills the `G`-part of `a`, so `⟨a, b⟩ ≤ nV`" needs
    such a homomorphism, and fails.
  - The cocycle is multiplicative only on stabilizers of points. A `BG` image with a
    common fixed point of `a` and `t` does push forward to a `BG` image in `G`.

**Literature (checked 2026-09-13).** BBMZ arXiv:2306.16356v3 (Problem 5.3, text
lines 823–849) does not name `BG`. It lies in item (9), one-relator groups
without torsion. Remark 5.4 records that Bux--Llosa Isenrich--Wu settled items (4),
all Baumslag--Solitar groups, and (8), free-by-cyclic groups; `BG` is in neither class.

See `research/artifacts/bh-baumslag-gersten-2026-09-12.md` for the host table,
and `research/artifacts/bh-bg-similarity-hosts-2026-09-12.md` for the
Thompson-like and Röver--Nekrashevych hosts.

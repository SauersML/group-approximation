---
rg: 2
id: free-by-pbh-and-surface-by-pbh-groups-lie-in-type-a-class
kind: claim
title: An extension of a group in the permutational Boone--Higman class by a finitely generated free group of rank at least two or a closed surface group of genus at least two again lies in that class; so do surface bundles over surfaces and groups with a normal series of such factors
distinct_from:
  virtually-free-extensions-lie-in-generalized-bs-classes: that puts N-by-(virtually free) groups in the generalized Baumslag--Solitar classes, where the quotient must be virtually free; this allows any quotient in B_A, e.g. Z^2, surface groups or linear groups, and the kernel must be free or a surface group.
  surface-generalized-bs-groups-satisfy-boone-higman: that gives plain Boone--Higman envelopes for surface-by-free groups among others; this gives membership in B_A, for surface-by-Q with any Q in B_A, including the surface-by-Z^2 and surface-by-surface groups that no Baumslag--Solitar class contains.
  free-by-virtually-free-groups-satisfy-boone-higman: that is free-by-(virtually free) through BLIW; this is free-by-Q for every Q in B_A.
  aut-free-groups-satisfy-permutational-boone-higman: that imports Aut(F_n) into B_A, whose Remark recovers free-by-cyclic groups by a case split on the order of the monodromy; this is the one-line embedding behind that remark, applied to all extensions at once.
  boone-higman-type-a-class-closed-under-finite-extensions: that is closure under subgroups, finite direct products and finite-index overgroups; this adds closure under extensions with free or surface kernel, using that closure.
---

**ESTABLISHED** (lane proof, elementary; not independently reviewed; no priority
claimed. The embedding in item 1 is standard. BFFHZ use its cyclic case in the
Remark after Corollary B, TeX l.535, for free-by-cyclic groups.)

Write `B_A` for the class of `boone-higman-type-a-class-closed-under-finite-extensions`:
groups that embed in a group with an action of type (A). Every member embeds in a
finitely presented simple group, and every finitely generated member has solvable word
problem.

## Statement

1. **Embedding.** Let `1 -> Γ -> H -> Q -> 1` be exact with `Γ` of trivial center.
   Then `h |-> (c_h|_Γ, hΓ)`, where `c_h(γ) = h γ h^-1`, is an injective homomorphism
   `H -> Aut(Γ) x Q`.
2. **Free and surface kernels.** Let `Γ` be a free group of finite rank `n >= 2`, or the
   fundamental group of a closed orientable surface of genus `g >= 2`. If `Q` is in
   `B_A`, then `H` is in `B_A`.
3. **Normal series.** Let `1 = N_0 <= N_1 <= ... <= N_k = H` with every `N_i` normal in
   `H`. Suppose each factor `N_i / N_(i-1)` with `i < k` is free of finite rank `>= 2` or a
   closed orientable surface group of genus `>= 2`, and the top factor `N_k / N_(k-1)` is in
   `B_A`. Then `H` is in `B_A`.
4. **Instances.**
   - Surface bundles over surfaces (Kodaira fibrations included): `pi_1(E)` with
     `1 -> pi_1(S_g) -> pi_1(E) -> pi_1(S_h) -> 1`, `g >= 2`. Linearity of these groups is
     not needed.
   - Free-by-`Z^m`, surface-by-`Z^m`, free-by-free, surface-by-free, free-by-surface, and
     free- or surface-by-(any finitely generated linear group in characteristic zero or
     `p`).
   - Free- or surface-by-(`Aut(F_m)`, punctured-surface mapping class groups, or any
     other group in `B_A`), and iterates of all of these.

## Proof

**Item 1.** Each `c_h` preserves the normal subgroup `Γ`, and `h |-> c_h|_Γ` is a
homomorphism `H -> Aut(Γ)`. Together with the quotient map this gives a homomorphism
`H -> Aut(Γ) x Q`. If `h` is in the kernel, then `h ∈ Γ` because `hΓ = 1`, and `h`
commutes with every element of `Γ`. So `h ∈ Z(Γ) = 1`.

**Item 2.** Free groups of rank at least two and closed surface groups of genus at least
two have trivial center (for the surface case, part 1 of
`based-dehn-nielsen-baer-for-closed-surfaces`).
- `Aut(F_n)` is in `B_A` by `aut-free-groups-satisfy-permutational-boone-higman`
  (BFFHZ Theorem A, in the permutational form).
- `Aut(pi_1(S_g))` is the extended mapping class group of `S_g` with one puncture,
  by part 2 of `based-dehn-nielsen-baer-for-closed-surfaces`. It is in `B_A` by
  `punctured-surface-mcgs-satisfy-permutational-boone-higman` (BFFHZ Corollary B,
  first bullet, with the PBH conclusion of their Section 4).

`B_A` is closed under finite direct products and subgroups (part 1 of
`boone-higman-type-a-class-closed-under-finite-extensions`). So `Aut(Γ) x Q` is in
`B_A`, and so is `H` by item 1.

**Item 3.** Induct on `k`. For `k = 1`, `H = N_1 / N_0` is in `B_A` by hypothesis. For
`k >= 2`, the images `N_i / N_1` (`i = 1, ..., k`) form a normal series of `H / N_1` of
length `k - 1` with the same factors `N_i / N_(i-1)`, `i >= 2`. So `H / N_1` is in `B_A` by
induction. `N_1` is free or a surface group and normal in `H`, so item 2 applies to
`1 -> N_1 -> H -> H/N_1 -> 1`.

**Item 4.** Surface groups, free groups, `Z^m` and finitely generated linear groups are
in `B_A` (`char-zero-linear-groups-satisfy-permutational-boone-higman` and
`char-p-linear-groups-satisfy-permutational-boone-higman`). `Aut(F_m)` and punctured mapping class groups are in `B_A` by the
nodes above.

## Addendum (2026-09-18): product kernels

5. **Products.** Let `Γ = Γ_1 x ... x Γ_k`, each `Γ_i` free of finite rank `>= 2` or a closed
   orientable surface group of genus `>= 2`. Then every automorphism of `Γ` permutes the
   factors, so `Π Aut(Γ_i)` has finite index in `Aut(Γ)`. Hence `Aut(Γ)` is in `B_A`, and every
   `Γ`-by-`B_A` group is in `B_A`. The same holds in item 3 with such products as factors.

*Proof.* `Γ` has trivial center. Let `α ∈ Aut(Γ)`, `N = α(Γ_1)` and `M = α(Π_{i>1} Γ_i)`. These
are commuting normal subgroups with `NM = Γ` and `N ∩ M = 1`. For each `j`, the projections
`π_j(N)` and `π_j(M)` are commuting normal subgroups generating `Γ_j`. A nontrivial normal
subgroup of `Γ_j` is not cyclic, since `Γ_j` is not virtually cyclic, and centralizers of
nontrivial elements of `Γ_j` are cyclic, so it has trivial centralizer. Hence one of the
two projections is trivial. So there is a set `J` of indices with `N <= Π_{j∈J} Γ_j` and
`M <= Π_{j∉J} Γ_j`, and `NM = Γ` forces `N = Π_{j∈J} Γ_j`. `N ≅ Γ_1` is directly
indecomposable: in a direct product of two nontrivial groups, an element of the first
factor centralizes the whole second factor, while centralizers in `Γ_1` are cyclic. So
`|J| = 1`, and `α` maps `Γ_1` onto some `Γ_j`, and likewise for every factor. So
`Aut(Γ) = (Π Aut(Γ_i)) ⋊ P`, with `P` the finite group permuting isomorphic factors. Now
`Π Aut(Γ_i)` is in `B_A` by item 2 and part 1 of
`boone-higman-type-a-class-closed-under-finite-extensions`, and so is `Aut(Γ)` by part 2.
The embedding of item 1 finishes. Instances: `(F_2 x F_2)`-by-`Z^m`, and
`(π_1 S_g x π_1 S_h)`-by-(any group in `B_A`).

6. **Virtually inner extensions.** Let `1 -> Γ -> H -> Q -> 1` with `Γ` of trivial center and in
   `B_A`, `Q` in `B_A`, and suppose the outer action `Q -> Out(Γ)` has finite image. Then `H` is
   in `B_A`. In particular this holds for every extension when `Out(Γ)` is finite.

*Proof.* Let `Ã <= Aut(Γ)` be the preimage of that finite image. By item 1, `H` embeds in
`Ã x Q`. `Ã` contains `Inn(Γ) ≅ Γ` with finite index, so it is in `B_A` by part 2 of
`boone-higman-type-a-class-closed-under-finite-extensions`, and `Ã x Q` is in `B_A` by part 1.

*Instances.*
- `Γ = pi_1(M)` for a finite-volume hyperbolic 3-manifold `M`. It is centerless, linear
  (so in `B_A` by `char-zero-linear-groups-satisfy-permutational-boone-higman`), and
  `Out(Γ)` is finite by Mostow--Prasad rigidity. So every `pi_1(M)`-by-`B_A` group is in
  `B_A`, e.g. extensions by `Z^m`, surface groups or `Aut(F_n)`.
- More generally, any centerless linear group with finite outer automorphism group
  qualifies. This includes torsion-free lattices in simple Lie groups not locally
  isomorphic to `PSL_2(R)` (strong rigidity; rigidity inputs not re-read here).
- **Hyperbolic kernels.** Every hyperbolic group is in `B_A`
  (`hyperbolic-groups-lie-in-the-permutational-class`, referees a and b PASS). So item 6
  applies to every hyperbolic `Γ` with trivial center (e.g. torsion-free non-elementary) and
  finite `Out(Γ)`. By Paulin's theorem with the Rips--Bestvina--Feighn theory of actions on
  R-trees (inputs not re-read here), `Out(Γ)` is finite when `Γ` is one-ended and does not split
  over a virtually cyclic subgroup. So every extension of a group in `B_A` by such a `Γ` is in
  `B_A`. When `Out(Γ)` is infinite, item 6 still covers extensions whose outer action has
  finite image.

## Scope

- The kernel must be finitely generated, free or a closed surface group of genus at
  least two. Other centerless kernels work whenever their automorphism group is in
  `B_A`; finite direct products of such groups are handled in item 5 below.
- This says nothing about Out(F_n) or closed-surface mapping class groups themselves:
  they are quotients of `Aut(F_n)` and `Mod(S_(g,1))`, not extensions of them.
- The open 3-manifold case `nonfibered-closed-graph-manifold-groups-satisfy-pbh` is not
  reached. By `nonfibered-graph-manifold-groups-have-no-fg-normal-subgroups`, those
  groups have no free or surface normal subgroup to use as `Γ`.
- **Infinite outer image (not treated).** In general item 1 embeds `H` in `Â x Q`, where
  `Â <= Aut(Γ)` is the extension of the outer image `Q̄` by `Inn(Γ)`. So the question is
  `Â ∈ B_A`.
  - For `Q̄ = <φ>` infinite cyclic, `Â` is a mapping torus `Γ ⋊_φ Z`.
  - For one-ended hyperbolic `Γ`, a finite power of `φ` preserves the cyclic JSJ splitting
    and is built from Dehn twists and mapping classes of its quadratically hanging pieces
    (Levitt; not re-read here).
  - When some quadratically hanging piece carries a pseudo-Anosov, `Γ ⋊ Z` is a graph of
    (surface-with-boundary)-by-`Z` groups over `Z^2` edge groups. That is the same shape
    as the graph manifold groups of `nonfibered-closed-graph-manifold-groups-satisfy-pbh`.
    So this case is expected to be as hard as the open 3-manifold case.

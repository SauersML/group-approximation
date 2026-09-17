---
rg: 2
id: finitary-permanence-closures-collapse-proof
kind: route
title: Measure the simple width of a group, bound it through extensions and finite graphs of groups, and feed the collapse a decidable simple envelope
target: finitary-permanence-closures-collapse-boone-higman-to-base
requires: [boone-higman-thompson-simple-envelope, lef-wp-groups-have-decidable-simple-kazhdan-lef-hosts, property-t-implies-property-fa]
---

Notation is as in the target. All trees are simplicial, and groups act on them
by automorphisms without inversions. An element or subgroup is *elliptic* if
it fixes a vertex. An element that is not elliptic is *hyperbolic*.

Tree facts used, all from Serre, *Trees*, Chapter I:
- **(T1)** A hyperbolic automorphism `h` has a unique axis. This is a
  bi-infinite line `ℓ_h` on which `h` acts by a nontrivial translation (§6.4).
  By uniqueness, `ℓ_{g h g^-1} = g ℓ_h`.
- **(T2)** The fixed-point set of an elliptic automorphism is a nonempty
  subtree (§6.1).
- **(T3)** A finitely generated group all of whose elements are elliptic fixes
  a vertex (§6.5, Corollaries 2 and 3, the same locator used by
  `profinite-tree-hosts-make-fa-subgroups-residually-finite`).
- **(T4)** The fundamental group `X` of a graph of groups acts without
  inversions on its Bass--Serre tree, and the vertex stabilizers are exactly
  the `X`-conjugates of the vertex groups (§4 for amalgams, §5 for graphs of
  groups; the same fact is used in `fa-subgroups-graph-towers-proof`).

Fix a nonabelian simple group `S`. For a group `X`, define its *S-width* as
`w_S(X) = sup { n >= 0 : S^n embeds in X }`, a value in `{0, 1, 2, ..., ∞}`.
Here `S^0 = 1`. Since `S^m <= S^n` for `m <= n`, the set of such `n` is an
initial segment of the natural numbers. So `w_S(X) = ∞` exactly when every
`S^n` embeds in `X`.

## Step 1: normal subgroups of a power of a nonabelian simple group

**Lemma 1.** Let `I` be any index set and `P = ⊕_{i in I} S_i` the restricted
direct product of copies `S_i` of `S`. Every normal subgroup `M` of `P` equals
`⊕_{i in J} S_i` for some `J ⊆ I`. In particular this holds for `P = S^n`.

*Proof.* Let `J` be the set of indices `i` such that some `m in M` has
`m_i != 1`, so `M <= ⊕_{i in J} S_i`. Take `i in J` and `m in M` with
`m_i != 1`. The center of `S` is trivial, because it is a normal subgroup and
`S` is nonabelian and simple. So some `s in S_i` has `s m_i != m_i s`. The
commutator `[m, s] = m s m^-1 s^-1` lies in `M`, since `M` is normal. All its
coordinates other than `i` are trivial, because `s` is supported on `S_i`, and
its `i`-th coordinate is `[m_i, s] != 1`. So `M ∩ S_i` is a nontrivial normal
subgroup of the simple group `S_i`, and hence `S_i <= M`. This gives
`⊕_{i in J} S_i <= M`. `∎`

## Step 2: extensions are subadditive

**Lemma 2.** If `N` is a normal subgroup of `X` and `Q = X/N`, then
`w_S(X) <= w_S(N) + w_S(Q)`.

*Proof.* Let `S^n <= X` with `n` finite. The intersection `S^n ∩ N` is normal
in `S^n`, so by Lemma 1 it equals `S^J` for some `J ⊆ {1, ..., n}`. Hence
`S^|J|` embeds in `N`. The composite `S^n -> X -> Q` has kernel `S^J`, so
`S^n / S^J ≅ S^(n - |J|)` embeds in `Q`. Therefore
`n = |J| + (n - |J|) <= w_S(N) + w_S(Q)`. Taking the supremum over `n` gives
the bound. `∎`

Special cases:
- `w_S(Y_1 x Y_2) <= w_S(Y_1) + w_S(Y_2)`;
- semidirect products and relative holomorphs `A ⋊ B`, and wreath products
  `Y wr_Ω Z` with `Ω` finite, whose kernel `Y^Ω` is a finite product;
- an overgroup `X` of `Y` of finite index, provided `S` is infinite. The normal
  core `N` of `Y` has finite index in `X`, and a finite group has S-width `0`.
  So `w_S(X) <= w_S(N) <= w_S(Y)`.

## Step 3: finite graphs of groups add at most one

**Lemma 3.** Let `x` and `y` be commuting elliptic automorphisms of a tree.
Then `xy` is elliptic.

*Proof.* By (T2), `F = Fix(x)` is a nonempty subtree. Because `y` commutes
with `x`, `y F = Fix(y x y^-1) = F`. Let `p` be a vertex fixed by `y`, and let
`q` be the vertex of `F` nearest to `p`. In a tree this vertex is unique. The
automorphism `y` preserves distances and preserves `F`, so `y q` is the vertex
of `F` nearest to `y p = p`. Hence `y q = q`. Since `q in F`, also `x q = q`.
So `xy` fixes `q`. `∎`

**Lemma 4.** Let `S` be a finitely generated nonabelian simple group and
`n >= 1`, and let `S^n = S_1 x ... x S_n` act on a tree.
- **(a)** If some factor `S_a` contains a hyperbolic element, then
  `R_a = ∏_{b != a} S_b ≅ S^(n-1)` fixes a vertex.
- **(b)** Otherwise `S^n` fixes a vertex.

In either case some subgroup isomorphic to `S^(n-1)` fixes a vertex.

*Proof.* **(a)** Let `h in S_a` be hyperbolic, with axis `ℓ = ℓ_h` from (T1).
Every `s in R_a` commutes with `h`, so `s ℓ = ℓ_{s h s^-1} = ℓ`. Restriction
to `ℓ` gives a homomorphism `ρ : R_a -> Aut(ℓ)`. The automorphism group of a
simplicial line is the infinite dihedral group `D_inf = Z ⋊ Z/2`, which is
solvable with derived length 2. The group `S` is perfect, since `[S, S]` is a
nontrivial normal subgroup of the nonabelian simple group `S`. So `R_a` is
perfect, and hence so is `ρ(R_a)`. A perfect subgroup of a solvable group is
trivial, because it equals each term of its own derived series, and that
series reaches `1`. So `ρ` is trivial. Then `R_a` fixes `ℓ` pointwise, and in
particular it fixes a vertex.

**(b)** Now every element of every factor is elliptic. An element of `S^n` is
a product `g_1 g_2 ... g_n` with `g_b in S_b`, and these factors commute
pairwise. By Lemma 3 and induction on `k`, the product `g_1 ... g_k` is
elliptic: it commutes with `g_(k+1)`, which is elliptic. So every element of
`S^n` is elliptic. The group `S^n` is finitely generated because `S` is. By
(T3), `S^n` fixes a vertex. `∎`

**Lemma 5.** Let `X` be the fundamental group of a graph of groups over a
**finite** graph with vertex groups `Y_v`. Then
`w_S(X) <= 1 + max_v w_S(Y_v)` for every finitely generated nonabelian simple
group `S`.

*Proof.* Let `S^n <= X` with `1 <= n < ∞`. Apply Lemma 4 to the action of `X`
on its Bass--Serre tree, which is without inversions by (T4). Some subgroup
isomorphic to `S^(n-1)` fixes a vertex, so by (T4) it lies in a conjugate
`g Y_v g^-1`. Conjugating back, `S^(n-1)` embeds in `Y_v`. So
`n - 1 <= max_v w_S(Y_v)`, and the maximum is over finitely many vertices. `∎`

Special cases include:
- amalgams `A *_C B` and HNN extensions `A *_φ`, over any edge groups;
- free products;
- trees of groups over finite trees;
- common-retract amalgams;
- stable-permutation HNN extensions;
- graph products over finite graphs. A graph product `G_Γ` is the amalgam
  `G_(Γ - v) *_(G_lk(v)) (G_v x G_lk(v))`, so by induction on the number of
  vertices, using Lemma 2 for the direct product,
  `w_S(G_Γ) <= |V(Γ)| * max_v w_S(G_v) + |V(Γ)|`.

## Step 4: finitary closures cannot create infinite S-width (part (A))

Let `C` be a class of groups. Put `Fin_0(C) = C`, closed under isomorphism.
Let `Fin_(k+1)(C)` consist of `Fin_k(C)` together with every group `X` of one of
the following kinds, where all inputs lie in `Fin_k(C)`:
- **(R1)** a subgroup of a member;
- **(R2)** a group with a normal subgroup `N` such that both `N` and `X/N` lie
  in `Fin_k(C)`;
- **(R3)** the fundamental group of a graph of groups over a finite graph whose
  vertex groups lie in `Fin_k(C)`.

Then `Fin(C) = ∪_k Fin_k(C)`.

**Proposition A.** Let `S` be a finitely generated infinite simple group.
Suppose every member of `C` has finite S-width. Then every member of `Fin(C)`
has finite S-width. Equivalently, if some `X in Fin(C)` contains a copy of
`S^n` for every `n`, then some single member of `C` contains a copy of `S^n`
for every `n`.

*Proof.* An infinite simple group is nonabelian. Induct on `k`. Members of
`Fin_0(C)` have finite width by hypothesis. A member of `Fin_(k+1)(C)` is
built from finitely many inputs of finite width:
- under (R1) its width is at most that of the input;
- under (R2) its width is at most the sum of two finite widths, by Lemma 2;
- under (R3) its width is at most one plus a maximum over finitely many finite
  widths, by Lemma 5.

In each case the width is finite. `∎`

## Step 5: a decidable group with infinite simple width over its envelope

**Lemma 6.** Let `S` be a finitely generated group with solvable word problem.
Then the restricted wreath product `H = S wr Z = (⊕_{i in Z} S) ⋊ Z` is
finitely generated, has solvable word problem, and contains `S^n` for every
`n`.

*Proof.* Let `A` be a finite generating set of `S`, and write `a^(i)` for the
copy of `a in A` in coordinate `i`. Let `t` generate `Z`, acting by
`t a^(i) t^-1 = a^(i+1)`. Then `A^(0) ∪ {t}` generates `H`.

Read a word `u` in these generators from left to right. Keep a current
position `p in Z`, starting at `0`, and for each coordinate `i` a word `u_i`
over `A`, starting empty. On reading `t^(±1)`, replace `p` by `p ± 1`. On
reading `a^(±1)` with `a in A`, append `a^(±1)` to `u_p`. This is correct
because `(f, t^p) · a^(0) = (f · a^(p), t^p)`, where `a^(p) = t^p a^(0) t^-p`.

At the end `u` represents `(f, t^p)`, where `f(i)` is the element of `S`
represented by `u_i`. Only finitely many coordinates are touched. So `u = 1`
in `H` if and only if `p = 0` and every touched `u_i` is trivial in `S`, which
is decidable. Coordinates `0, ..., n-1` give `S^n <= ⊕ S <= H`. `∎`

**Corollary A'.** Suppose `Fin(C)` hosts every finitely generated group with
solvable word problem, in the sense that each such group embeds in some member
of `Fin(C)`. Then `C` itself hosts every finitely generated group with
solvable word problem.

*Proof.* Let `G` be finitely generated with solvable word problem.
`boone-higman-thompson-simple-envelope` gives a finitely generated computably
presented simple group containing `G`. Its two recorded refinements make it
infinite (apply the theorem to `G x Z`) and give it solvable word problem
(Kuznetsov's two-enumeration argument). Call this group `S`.

By Lemma 6, `H = S wr Z` is finitely generated with solvable word problem, so
it embeds in some `X in Fin(C)`. Then `X` contains `S^n` for every `n`. By
Proposition A, some `B in C` contains `S^n` for every `n`, in particular `S`,
and therefore `G`. `∎`

## Step 6: infinitary operations reflect one simple subgroup (part (B))

**Lemma 7.** Let `S` be a finitely generated nonabelian simple group that
embeds in `X`.
- **(i)** If `X <= Y`, then `S` embeds in `Y`.
- **(ii)** If `N` is normal in `X`, then `S` embeds in `N` or in `X/N`.
- **(iii)** If `X <= ∏_{j in J} Y_j`, an unrestricted direct product over any
  index set, then `S` embeds in some `Y_j`. The same holds for restricted
  products, which are subgroups of the unrestricted ones.
- **(iv)** If `X` is the union of a directed family of subgroups `X_λ`, then
  `S` embeds in some `X_λ`.
- **(v)** If `S` has property FA and `X` is the fundamental group of a graph
  of groups over any graph, finite or not, with vertex groups `Y_v`, then `S`
  embeds in some `Y_v`.

*Proof.* Regard `S` as a subgroup of `X`.
- **(i)** This is immediate.
- **(ii)** `S ∩ N` is normal in `S`, so it is `S` or `1`. In the second case
  `S -> X/N` is injective.
- **(iii)** Let `π_j` be the coordinate projections. Each `ker(π_j) ∩ S` is
  `S` or `1`. Their intersection is `1`, and `S != 1`, so some `π_j` is
  injective on `S`.
- **(iv)** Each of the finitely many generators of `S` lies in some `X_λ`, and
  the family is directed, so a single `X_λ` contains them all.
- **(v)** `S` fixes a vertex of the Bass--Serre tree, which is without
  inversions. By (T4), `S` lies in a conjugate of some `Y_v`.

`∎`

Let `Inf(C)` be the smallest class containing `C` and closed under
isomorphism, subgroups, extensions as in (R2), arbitrary unrestricted and
restricted direct products, and directed unions. Construct it by transfinite
recursion, applying the operations to the union of the earlier stages, and
taking unions at limit stages.

A permutational wreath product `Y wr_Ω Z` over any `Z`-set `Ω` lies in
`Inf({Y, Z})`. It is an extension of the restricted product `⊕_Ω Y` by `Z`.

**Proposition B.** Let `S` be a finitely generated infinite simple group. If
`S` embeds in a member of `Inf(C)`, then `S` embeds in a member of `C`. If `S`
also has property FA, the same holds for the closure `All(C)` of `C` under the
operations of `Inf(C)` together with fundamental groups of arbitrary graphs of
groups.

*Proof.* Use transfinite induction on the stage. At a successor stage a member
is a subgroup, extension, product, directed union or graph of groups of
members of earlier stages. Lemma 7 moves `S` into one of those inputs. At a
limit stage there is nothing new to check. `∎`

**Corollary B'.** If `Inf(C)` hosts every finitely generated group with
solvable word problem, then so does `C`.

*Proof.* Take `S ⊇ G` as in Corollary A', and apply Proposition B to
`S in Inf(C)`. `∎`

## Step 7: mixed closures over locally embeddable into finite inputs (part (C))

**Corollary C'.** Suppose `All(C)` hosts every finitely generated group with
solvable word problem. Then `C` hosts every finitely generated LEF group with
solvable word problem, in particular every finitely generated residually
finite group with solvable word problem.

*Proof.* Let `G` be finitely generated and LEF with solvable word problem. By
`lef-wp-groups-have-decidable-simple-kazhdan-lef-hosts`, `G` embeds in an
infinite, finitely generated, simple Kazhdan group `K` with solvable word
problem. By `property-t-implies-property-fa`, `K` has property FA. Since `K`
is finitely generated with solvable word problem, it embeds in a member of
`All(C)`. By Proposition B, `K`, and hence `G`, embeds in a member of `C`. `∎`

**Conditional Corollary D'.** Suppose every finitely generated group with
solvable word problem embeds in a finitely generated simple group with
property FA and solvable word problem. This is
`decidable-groups-embed-in-decidable-simple-fa-groups`. Then the conclusion of
Corollary C' holds for every finitely generated group with solvable word
problem. The proof is the same, with that envelope in place of `K`.

## Step 8: where each hypothesis is sharp

- **Finiteness in (R2) and (R3) is needed for Proposition A.** From the class
  `{S, Z}`, of widths `1` and `0`, the wreath product `S wr Z` has infinite
  width. Similarly the countable restricted product of the groups `S^n`, all
  of finite width, has infinite width. So infinitary operations can create
  width, and Proposition B tracks only one copy of `S`.
- **Property FA is needed for (v).** Lemma 7(v) fails for simple groups that
  split. A Burger--Mozes simple lattice `Γ` in a product of two trees
  `T_1 x T_2` is torsion-free and acts freely and cocompactly on vertices.

  Subdivide `T_1` so that `Γ` acts on it without inversions. A vertex
  stabilizer `Γ_u` then acts on the vertices of `T_2` freely:
  - if `u` is an original vertex and `γ in Γ_u` fixes a vertex `y`, then `γ`
    fixes `(u, y)`;
  - if `u` is a midpoint, then `γ^2` fixes a vertex of `T_1 x T_2`, and `Γ` is
    torsion-free.

  So `Γ_u` is free. Therefore `Γ` is the fundamental group of a finite graph of
  free groups, and free groups contain no nontrivial simple subgroup. This is recorded as calibration only and is not
  used above. Burger--Mozes, *Lattices in product of trees*, Publ. Math. IHES
  92 (2000).
- **Quotients are not covered by anything above.** Every finitely generated
  group is a quotient of a free group, and free groups lie in every
  Boone--Higman class considered. So a reduction that allows quotients escapes
  all of Propositions A and B.

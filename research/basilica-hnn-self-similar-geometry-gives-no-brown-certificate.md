---
rg: 2
id: basilica-hnn-self-similar-geometry-gives-no-brown-certificate
kind: claim
title: The Basilica HNN extension acts faithfully on the 3-regular tree fixing an end, extending the self-similar action, but every vertex stabilizer is infinitely generated, and Nekrashevych's self-similarity graph carries no action at all, so neither hosts a Brown certificate
requires:
  - basilica-group-is-torsion-free-and-contains-every-z-n
distinct_from:
  basilica-hnn-has-no-finitely-presented-ascending-base: that excludes the Bass–Serre trees of ascending decompositions, whose stabilizers are conjugates of bases; this treats the tree coming from the self-similar action, which is not a Bass–Serre tree of any ascending decomposition, and Nekrashevych's self-similarity graph.
---

**ESTABLISHED** (lane proof below, elementary). No priority is claimed. Notation follows
`basilica-group-is-torsion-free-and-contains-every-z-n`: `B` acts on the binary rooted tree `T`,
`σ(g) = (a^(ε_a(g)), g)`, and `B~ = ⟨B, t | t^(−1) g t = σ(g)⟩`, with `χ(t) = 1` and `N = ker χ`.

## 1. Nekrashevych's self-similarity graph carries no action of `B`

`Σ(B, X)`, recalled from Nekrashevych, *Self-similar groups*, §3.7, has vertex set `X^*`, edges `v — xv`, and
edges `v — s(v)` for `s` in a finite generating set.
- `g ∈ B` sends the edge `v — s(v)` to `g(v) — (g s g^(−1))(g(v))`, which is not an edge in general.
- `g(xv) = g(x) g|_x(v)` is not of the form `y g(v)`, so the prepending edges are not preserved either.
- Each `g` moves every vertex a distance at most `|g|` along horizontal edges, so the induced map is at bounded
  distance from the identity.
- The graph is the hyperbolic model of the *shift* on the limit space `J_B` (for `B`, the Basilica Julia set). It is
  not a model of the group, so it cannot host Brown's criterion for `B` or `B~`.

## 2. The natural tree of `B~`: the 3-regular tree `T_3` fixing an end

- **Construction.** Let `T_3` be the increasing union of rooted binary trees `T = T^(0) ⊂ T^(1) ⊂ ⋯`, where `T^(n+1)`
  has a new root `r_(−n−1)` whose child `1` is the old root `r_(−n)`. So `r_0` is the root of `T` and
  `r_(−n) ⋅ 1^n = r_0`.
  - Every vertex has one parent and two children, so `T_3` is 3-regular.
  - The spine `r_0, r_(−1), …` converges to an end `ω`.
- **The action.** Let `g ∈ t^n B t^(−n)` act on `T^(n)` through the identification `T^(n) ≅ T`, `r_(−n) ↦` root, as
  the element `t^(−n) g t^n` of `B`. Let `t^(−1)` map `T^(n+1)` onto `T^(n)`, sending `r_(−k)` to `r_(−k+1)`.
  - This is consistent, and the relation `t^(−1) g t = σ(g)` holds on every `T^(n)`, because `h ∈ B` equals `t σ(h) t^(−1)`, and `σ(h) = (a^(ε_a h), h)` acts on the child-`1`
    subtree `T^(n)` exactly as `h`.
  - So `h ∈ B` acts on the sibling subtrees up the spine by the powers `a^(ε_a(σ^k h))`, `k ≥ 0`.
- **Properties.**
  - The action fixes `ω`. Each element of `t^n B t^(−n)` fixes `r_(−m)` for all `m ≥ n`, so every element of `N`
    fixes a ray toward `ω`. `N` is exactly the set of elliptic elements, `χ` is the Busemann character, and `t`
    translates the spine by one.
  - The action is faithful. `N` is faithful because each `t^n B t^(−n)` is faithful on `T^(n)`. A kernel element
    `k = n t^m` with `m ≠ 0` would translate the spine.
  - It extends the self-similar action of `B` on `T`, which is the subtree below `r_0`.
- **So `B~ ≤ Aut(T_3)_ω`.** It is not discrete there.

## 3. Every vertex and edge stabilizer is infinitely generated

- Every vertex of `T_3` is a `t`-translate of a vertex `u` of `T`. Its stabilizer lies in `N`, since elements with
  `χ ≠ 0` move the horofunction, and it equals the increasing union
  `Stab(u) = ⋃_n t^n St_B(1^n u) t^(−n)`.
- **The union is strictly increasing.** This uses item 3 of the torsion-free node, that `(x, 1) ∈ B` for
  `x ∈ B'`.
  - Under `T^(n+1) ≅ T`, the element `(x, 1)` with `1 ≠ x ∈ B'` lies in `t^(n+1) B t^(−(n+1))`. It fixes
    `u ∈ T^(n)` and acts trivially on `T^(n)`, but nontrivially on the sibling subtree of `r_(−n)`.
  - Every element of `t^n B t^(−n)` that is trivial on `T^(n)` is trivial, by faithfulness on `T^(n)`.
  - So `(x, 1) ∉ t^n B t^(−n)`.
- A finitely generated group is never a strictly increasing union of subgroups, so **`Stab(u)` is infinitely
  generated**.
- Every stabilizer contains the finitely generated but non-`FP_2` group `t^n St_B(1^n u) t^(−n)` as a subgroup. It is
  a union of such groups, not one of them.
- Edge stabilizers equal the stabilizer of the lower vertex, because the fixed end forces the upward ray to be fixed.

## 4. Consequence for `FP_3` of `B~`

- Brown's criterion needs the stabilizer of each `p`-cell to be of type `FP_(n−p)`, in the cocompact form and in the
  filtration form (Brown, JPAA 44 (1987)). That fails in degree 0 for `T_3`, and for every `B~`-complex whose cell
  stabilizers contain these vertex stabilizers with finite index.
- **The self-similar geometry of `B`, whether the tree, its end-fixing extension or the self-similarity complex,
  therefore gives no certificate.**
- Together with `basilica-hnn-has-no-finitely-presented-ascending-base`, which covers Bass–Serre trees, and with
  `basilica-fp2-covers-contain-free-subgroups`, which shows that `B` is not `FP_2`, the tree actions examined so far are closed. Since `B~` is amenable, any
  minimal tree action without a fixed vertex preserves a line or fixes an end. Those end-fixing actions are not
  classified here.
- What remains is the Thompson pattern: a **free** or nearly free action on an infinite-dimensional contractible
  complex, with a Morse filtration. Equivalently, a combinatorial certificate: a finite complete rewriting system
  (Brown's collapsing schemes), a diagram-group structure (Farley), or a direct computation of
  `H_2(B~; ∏ ZB~) = 0` through the Mayer–Vietoris condition on the crux node.

## Lesson for general BH

Self-similar dynamics produce natural trees for these extensions, but their stabilizers are directed unions of
level stabilizers, never finitely generated. So the geometry that makes branch groups tractable for BH (germ and
V-type hosts) is exactly the geometry that cannot certify their higher finiteness. Finiteness proofs for groups
built from branch groups should be sought combinatorially or in cube complexes with free actions, as for Thompson's F.

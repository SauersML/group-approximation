---
rg: 2
id: normal-germ-extensions-of-thompson-v-contain-no-sl3z-proof
kind: route
title: Fix SL_3(Z) on the germ cube complex, push it injectively into finitely many germ groups, and quotient the normalizing germs onto Thompson groups
target: normal-germ-extensions-of-thompson-v-contain-no-sl3z
requires:
  - germ-complex-and-bux-gonzalez-morse-inputs
---

Hand proof, 2026-09-17. Not independently reviewed. Notation as in the target claim.

## Inputs

- **(I1)** Belk–Hyde–Matucci, arXiv:2407.03149v1, as imported in `germ-complex-and-bux-gonzalez-morse-inputs`: the
  three finite-germ-extension conditions; the germ complex `K`, the restricted product over `p in sing(G)` of the
  stars `T_p`, with the action `(g·γ)(p) = g·γ(g^{-1}p)` and `g·(Bh)_p = (Bhg^{-1})_{g(p)}`; and **(Stab)**: "Every
  cube stabilizer in `K` has a finite-index subgroup conjugate to `SingFix_G(M,M') = {g : sing(g) ⊆ M,
  g|_{M'} = id}`".
- **(I2)** BBMZ survey, arXiv:2306.16356v3, Remark 4.12: "any action of any finite index subgroup of
  SL_n(Z) (n ≥ 3) on any CAT(0) cube complex must fix a point" (citing Cornulier, arXiv:1302.5982).
- **(I3)** Margulis's normal subgroup theorem (G. A. Margulis, *Discrete Subgroups of Semisimple Lie Groups*,
  Springer 1991, Ch. IV), in the form: "Let G be a connected, centerless semisimple Lie group of real rank at
  least 2. Let Γ be an irreducible lattice in G. Then any nontrivial normal subgroup of Γ has finite index."
  We use `G = SL_3(R)`: its centre is trivial (the only real cube root of 1 is 1), its real rank is 2, and it
  is simple, so every finite-index subgroup of `SL_3(Z)` is an irreducible lattice. A finite nontrivial normal
  subgroup would have finite index, which is impossible for an infinite group. So every nontrivial normal
  subgroup of a finite-index subgroup of `SL_3(Z)` is infinite and of finite index.
- **(I4)** Survey Theorem 4.4 (Higman 1974): "every torsion-free nilpotent group that embeds into V is free
  abelian". Survey Remark 4.2: Higman "proved that all of these groups [the `V_{d,r}`] embed into Thompson's
  group V". Survey Theorem 4.3: `V` contains "(1) Any finite group" and "(2) ⊕_ω V, and hence any countable
  direct sum of subgroups of V".
- **(I5)** Survey Theorem 4.6(3): "Any group with cyclic subgroups that are distorted, such as ... Baumslag–Solitar
  groups BS(m,n) for |m| ≠ |n|" does not embed into `V`. Used only for Lemma 5.

## Lemma 0: no finite-index subgroup of SL_3(Z) embeds in V

Let `Γ` have finite index in `SL_3(Z)`. Then `Γ ∩ U_3(Z)` has finite index in the integral Heisenberg group, so it
contains `x = e_{12}(k)` and `y = e_{23}(k)` for some `k >= 1`, and `[x,y] = e_{13}(k^2) ≠ 1`. So `Γ` contains a
torsion-free nilpotent non-abelian group, and by (I4) `Γ` does not embed in `V`. Hence it does not embed in any
`V_{d,r}`, in any finite product of subgroups of `V`, or in any group embedding in `V` (I4).

## Lemma 1: K is a CAT(0) cube complex and G acts on it by cubical automorphisms

Each `T_p` is a tree. For finite `F ⊆ sing(G)`, let `K_F` be the set of vertices of `K` whose coordinates outside
`F` are basepoints, with the cubes of `K` between them. Then `K_F = ∏_{p in F} T_p` is a finite product of trees,
so a CAT(0) cube complex with median 1-skeleton. For `F ⊆ F'`, `K_F` is the product of the `T_p` (`p in F`) with
basepoint vertices, a convex subcomplex of `K_{F'}`. `K` is the directed union of the `K_F`, and every cube of `K`
lies in some `K_F`. So the 1-skeleton of `K` is a directed union of median graphs along convex subgraphs, hence a
median graph (medians of three vertices are computed in any `K_F` containing them). The cubes of `K` are exactly the
cubes spanned by that median graph, so `K` is a CAT(0) cube complex (Chepoi, Roller). By (I1), `g` sends the
coordinate at `g^{-1}p` to the coordinate at `p` through the bijection `(Bh)_{g^{-1}p} ↦ (Bhg^{-1})_p`, which fixes
`*` and sends the basepoint `(B)_{g^{-1}p}` to `(Bg^{-1})_p`. This is a graph isomorphism `T_{g^{-1}p} -> T_p`
(an isomorphism of stars that fixes the centre), so `G` acts by cubical automorphisms.

## Lemma 2: the germs of B

Let `p in X`. A germ at `p` of an element of `B` that fixes `p` is the germ of a prefix replacement `αw ↦ βw`,
where `p = αz = βz`. If `α ≠ β`, say `|α| < |β|`, then `β = αγ` and `z = γz`, so `z = γ^∞` and `p` has an
eventually periodic address. So `(B)_p = 1` unless `p` is eventually periodic. If it is, the germs are the powers of
`δ_p`, the prefix replacement that inserts one minimal period. So `(B)_p ≅ Z`. The germ `δ_p` is a contraction:
every point of a small cone around `p` converges to `p` under `δ_p^j`, `j -> ∞`. The germ `δ_p^{-1}` does not
have this property.

## Lemma 3: the germ map on SingFix has kernel in B

Let `M ⊆ M'` be finite. Every `g in SingFix_G(M,M')` fixes each `p in M`, which gives the germ map
`φ : SingFix_G(M,M') -> ∏_{p in M} (G)_p`. If `φ(g) = 1`, then `g` agrees with the identity near each `p in M`,
so `sing(g) ⊆ M` contains no point of `M`. So `sing(g) = ∅`, and `g in B` by condition 2 of (I1).

## Proof of Theorem A

Let `Γ <= G` be isomorphic to a finite-index subgroup of `SL_3(Z)`. By Lemma 1 and (I2), `Γ` fixes a point of `K`.
That point lies in the interior of a unique cube `C`, so `Γ` stabilizes `C` and permutes its finitely many
vertices. A finite-index subgroup `Γ'` therefore fixes a vertex `v`. By (Stab), `Stab_G(v)` has a finite-index
subgroup `h SingFix_G(M,M') h^{-1}`. Put `Γ_1 = h^{-1}(Γ' ∩ h SingFix_G(M,M') h^{-1})h`, which has finite index in a
conjugate of `Γ` and lies in `SingFix_G(M,M')`. Let `N = ker(φ) ∩ Γ_1`, a normal subgroup of `Γ_1`. By Lemma 3,
`N <= B`. If `N ≠ 1`, then (I3) makes `N` a finite-index subgroup of `SL_3(Z)` inside `B = V_{d,r}`, which
Lemma 0 forbids. So `N = 1`, and `φ` is injective on `Γ_1`. ∎

## Lemma 4: the normalizing germs at a periodic point

Let `p` be eventually periodic, `δ = δ_p`, and suppose `(B)_p` is normal in `(G)_p`.

1. **Commutation.** For `g in (G)_p`, conjugation by `g` restricts to an automorphism of `(B)_p = <δ> ≅ Z`, so
   `gδg^{-1} = δ^{±1}`. A conjugate of a contraction germ at `p` is a contraction germ at `g(p) = p`. By Lemma 2,
   `gδg^{-1} = δ`.
2. **The quotient map.** Fix a cone `U_0 ∋ p` on which `δ` is the prefix replacement, with `δ(U_0) ⊊ U_0` and
   `⋂_j δ^j(U_0) = {p}`. Put `D = U_0 \ δ(U_0)`, a finite union of cones. Then `U_0 \ {p}` is the disjoint union
   of the clopen sets `δ^j(D)`, `j >= 0`.

   Given `g in (G)_p`, choose a representative `ĝ in Stab_G(p)` and a cone `U ⊆ U_0` around `p` such that:
   - `ĝδ = δĝ` on `U`;
   - `ĝ(U) ⊆ U_0`;
   - `sing(ĝ) ∩ U ⊆ {p}`.

   For `x in D` pick `j` with `δ^j x in U`. The point `ĝ(δ^j x)` lies in a unique `δ^i(D)`; set
   `ḡ(x) = δ^{-i} ĝ(δ^j x) in D`.
   - By commutation, `ḡ` does not depend on `j` or on the representative.
   - `ḡ` is a bijection of `D`: its inverse is built in the same way from `g^{-1}`.
   - `ḡ` is locally a composite of prefix replacements with a map that agrees locally with elements of `B`, since
     `ĝ` has no singular point in `U \ {p}`.

   So `ḡ` is a homeomorphism of the compact set `D` that is piecewise, on finitely many cones, a prefix
   replacement. It is therefore an element of the Higman–Thompson group `V(D)` of `D`: the elements of `V_{d,r}`
   supported in `D`, restricted to `D`. So `V(D) <= V_{d,r}`, which embeds in `V` by (I4). The map
   `ψ_p : g ↦ ḡ` is a homomorphism `(G)_p -> V(D)`.
3. **The kernel is abelian.** If `ḡ = id`, then for `x in D` and large `j`, `ĝ(δ^j x) = δ^{j+k(x)} x` for an
   integer `k(x)`. By continuity, and because the `δ^i(D)` are clopen, `k` is locally constant. The germ of `g` is
   determined by `k`, and composing such germs adds the functions. So `A_p := ker ψ_p` embeds in the abelian group
   `C(D,Z)` of locally constant integer functions on `D`.
4. **The action on the kernel.** For `h in (G)_p` and `g in A_p` with function `k`, the germ `hgh^{-1}` has function
   `k ∘ ψ_p(h)^{-1}`. This uses that `h` commutes with `δ`.

## Proof of Theorem B

Take `Γ_1` from Theorem A, embedded in `P = ∏_{p in M} (G)_p`. For each `p in M` choose an abelian normal subgroup
`A_p ⊴ (G)_p` and a homomorphism `ψ_p` from `(G)_p` into a group embedding in `V`, with kernel `A_p`:

- **(a), `p` eventually periodic.** `(G)_p` is virtually infinite cyclic, because `(B)_p ≅ Z` has finite index.
  Let `A_p` be the normal core of `(B)_p`, an abelian subgroup of finite index, and let `ψ_p` be the quotient onto
  the finite group `(G)_p/A_p`. That group embeds in `V` by (I4).
- **(a), `p` not eventually periodic.** `(B)_p = 1` by Lemma 2, so `(G)_p` is finite. Take `A_p = 1`.
- **(b).** Lemma 4.

Then `ψ = ∏ ψ_p` maps `P` into a finite product of groups embedding in `V`, hence into `V` (I4), and its kernel
`A = ∏ A_p` is abelian. The group `Γ_1 ∩ A` is an abelian normal subgroup of `Γ_1`. If it were nontrivial, it would
have finite index by (I3), and `SL_3(Z)` would be virtually abelian, which is false. So `ψ` embeds `Γ_1` in `V`,
contradicting Lemma 0. ∎

The corollaries follow from Theorem B, because each listed group contains `SL_3(Z)`. For `VA`, the elements of
`V` and of Brin's group fixing a singular point have germs commuting with `δ_p`; for `A` this is the condition
`f(2x) = 2f(x)` near `0`, and `f(2x-1) = 2f(x)-1` near `1` (Burillo–Felipe, arXiv:2605.09763v1, quoting the
definition). Germs of elements of `V` carry `δ_q` to `δ_p`. So case (b) holds at every singular point.

## Lemma 5 (the BS(1,2) remark)

Let `θ : BS(1,2) = <a,t | tat^{-1} = a^2> -> (G)_p`, with `p` in case (a) or (b). Then `θ(a)` has finite order.

- **Case (a).** The group `(G)_p` is finite or virtually `Z`. In the latter case let `Z_0 = <z>` be an infinite
  cyclic normal subgroup of finite index. If `θ(a)` had infinite order, then `θ(a)^r = z^s` with `s ≠ 0`, and
  `θ(t) z^s θ(t)^{-1} = z^{2s}`. But conjugation acts on `Z_0` by `±1`, a contradiction.
- **Case (b), first step.** Suppose `ψ_p θ(a)` had infinite order, and let `N` be the kernel of
  `ψ_p θ : BS(1,2) -> V(D)`. The normal closure of `a` is `Z[1/2] = ⋃_j t^{-j}<a>t^j`. A nontrivial element
  `t^{-j}a^k t^j` of `N ∩ Z[1/2]` would give `a^k in N`, so `N ∩ Z[1/2] = 1`. Then `[N, Z[1/2]] = 1`, so `N` lies in
  the centralizer of `Z[1/2]`, which is `Z[1/2]` itself, because `ct^e` with `e ≠ 0` moves `a` to `a^{2^e}`. So
  `N = 1`, and `BS(1,2)` embeds in `V(D) <= V`, contradicting (I5). Hence `ψ_p θ(a)^m = 1` for some `m >= 1`.
- **Case (b), second step.** Now `θ(a^m) in A_p`, with function `k in C(D,Z)`. The relation
  `θ(t)θ(a^m)θ(t)^{-1} = θ(a^{2m})` reads `k ∘ ψ_pθ(t)^{-1} = 2k`, by Lemma 4.4. Now `k` is bounded, since it is
  locally constant on a compact set, and precomposition preserves `max|k|`. So `max|k| = 2 max|k|`, which forces
  `k = 0` and `θ(a^m) = 1`.

For a finite product of such germ groups, `θ(a)` has finite order in every coordinate, hence finite order. ∎

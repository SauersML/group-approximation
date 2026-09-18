---
rg: 2
id: fpbs-fiid-spines-lift-via-infinite-conjugate-intersection-proof
kind: route
title: Put an FIID spine of H in every left coset, and link neighbouring coset spines along the infinite contact set xK_s, where Bernoulli mixing of K_s forces a link
target: fpbs-fiid-spines-lift-via-infinite-conjugate-intersection
requires:
  - fpbs-central-z2-groups-have-fiid-sparse-spines
---

Conventions are those of the target. `Cay(Gamma,S)` has vertex set `Gamma`
and undirected edges `{y, ys}`, with `s ∈ S`, `s ≠ e`. `Gamma` acts on the
left. `omega = (U_v, U_e)` is the iid uniform field on `V ⊔ E`.

## Lemma A (transfer between generating sets)

*If `Cay(Gamma,T)` has an FIID connected infinite subgraph of density
`theta`, and `S` is another finite symmetric generating set, then
`Cay(Gamma,S)` has one of density at most `C theta`. Here
`C = Σ_{t∈T} (|w_t| + 1)`, where `w_t` is a fixed `S`-word for `t`.*

This is the argument of part (ii) of
`fpbs-fiid-soft-collapse-iff-fiid-sparse-spines`, reproduced here so that
this route does not depend on that node.

*Proof.*
1. Fix `S`-words `w_t` with `w_{t^-1} = w_t^-1`.
2. Run the given FIID map on an iid field on `V ⊔ E(Cay(Gamma,T))`. That
   field is an equivariant function of the vertex labels of `Cay(Gamma,S)`.
   Split each vertex label `U_h` into independent uniforms `U_h^0` and
   `U_h^(t)`, for `t ∈ T`. Give `h` the label `U_h^0`. Give the edge
   `{h, ht}` the fractional part of `U_h^(t) + U_{ht}^(t^-1)`. That expression
   is symmetric under the relabelling `{h,ht} = {ht, (ht)t^-1}`. Each
   sublabel is used by exactly one edge, so the resulting labels are iid
   uniform.
3. Replace each edge `{h, ht}` of the resulting subgraph `L_T` by the
   `S`-path `h, h w_t[1], ..., ht` that reads `w_t` from `h`.
4. The union `L_S` is connected and infinite, and it is an equivariant
   measurable function of `omega`.
5. Every vertex of `L_S` has the form `hu`, with `h ∈ V(L_T)` and `u` a
   prefix of some `w_t`. So
   `P(o ∈ V(L_S)) <= Σ_t Σ_u P(u^-1 ∈ V(L_T)) = C theta`, by invariance.
∎

So "has FIID sparse spines" can be checked on one generating set.

## Lemma B (mixing on free-orbit index sets)

*Let `K` be an infinite countable group acting on a countable set `I` with
finite stabilisers, and let `mu` be the product measure `lambda^I`. Then
every `K`-invariant event has probability `0` or `1`.*

*Proof.*
1. Take a finite `F ⊆ I`. For each pair `i, j ∈ F`, the set
   `{k : ki = j}` is empty or a coset of a finite stabiliser.
2. So `{k : kF ∩ F ≠ ∅}` is finite, and since `K` is infinite some `k` has
   `kF ∩ F = ∅`.
3. Let `E` be invariant, and let `A` be an event depending only on `F` with
   `mu(E Δ A) < delta`. Take `k` with `kF ∩ F = ∅`. Then `A` and `kA` are
   independent, and `mu(E Δ kA) = mu(kE Δ kA) < delta`.
4. So `mu(E) = mu(E ∩ E)`, which is within `2 delta` of
   `mu(A ∩ kA) = mu(A)^2`, which is within `2 delta` of `mu(E)^2`.
5. As `delta -> 0`, `mu(E) = mu(E)^2`.
∎

## Proof of Theorem 1

**Setup.**
1. Let `Φ` be an FIID map on `Cay(H, S_H)` producing an a.s. connected
   infinite subgraph of density `theta`, for a fixed finite symmetric
   generating set `S_H` of `H`. `H` has FIID sparse spines, so `theta` can be
   taken arbitrarily small (Lemma A).
2. `Σ_H` is symmetric, since `H ∩ g^-1Hg = g^-1(gHg^-1 ∩ H)g`. It contains
   `H` when `H` is infinite. (If `H` is finite it has no spines, so `H` is
   infinite.)
3. `Gamma` is finitely generated and `Σ_H` generates it, so there is a finite
   symmetric `S_1 ⊆ Σ_H \ H` with `<S_H ∪ S_1> = Gamma`. Elements of `Σ_H`
   lying in `H` are words in `S_H`, so they can be dropped.
4. Put `S = S_H ∪ S_1`, `G = Cay(Gamma,S)`. By Lemma A it suffices to build
   spines on `G`.
5. Call an edge `{y, ys}` an `H`-edge if `s ∈ S_H` and a link edge if
   `s ∈ S_1`. `H`-edges join points of the same left coset `yH`. Link edges
   join different cosets, since `s ∉ H`.
6. For a coset `C = xH`, the map `h -> xh` is an isomorphism from
   `Cay(H,S_H)` onto `C` with its `H`-edges.

**Coset spines.**
- For `C = xH` let `omega^x` be the field on `Cay(H,S_H)` given by
  `omega^x(h) = omega(xh)`, and similarly on edges. Put
  `Sp(C) = x · Φ(omega^x)`.
- Replacing `x` by `xh'` changes `omega^x` to `h'^-1 · omega^x`. Since `Φ` is
  `H`-equivariant, `Sp(C)` is unchanged, so it is well defined.
- For `gamma ∈ Gamma`, `Sp(gamma C)` computed from `gamma · omega` equals
  `gamma · Sp(C)`.
- `Sp(C)` depends only on labels of vertices of `C` and of `H`-edges inside
  `C`. So spines of distinct cosets are independent, and each is a copy of
  `Φ`.

**The subgraph.** Fix `a ∈ (0,1]`. Let `L` be the union of all `Sp(C)`,
together with every link edge `e = {u, v}` such that:
- `u ∈ Sp(uH)`,
- `v ∈ Sp(vH)`, and
- `U_e < a`.

The rule is symmetric in `u` and `v`. `L` is an equivariant measurable function
of `omega`, so it is FIID. Link edges only join spine vertices, so
`V(L) = ∪ V(Sp(C))` and `P(o ∈ V(L)) = P(o ∈ V(Sp(H))) = theta`.

**Contact sets.** Fix `C = xH` and `s ∈ S_1`. The link edges of type `s`
leaving `C` are `{xh, xhs}` with `h ∈ H`, and `xhsH = xh'sH` iff
`h^-1 h' ∈ K_s := H ∩ sHs^-1`. So for a target coset `C' = xh_0 sH`, the
edges from `C` to `C'` of this type are `{xh_0 k, xh_0 k s}` with
`k ∈ K_s`. There are infinitely many, since `s ∈ Σ_H`.

**Linking lemma.** *A.s., for every `C`, `s`, `C'` as above, `L` contains a
link edge between `Sp(C)` and `Sp(C')`.*

There are countably many triples, so it suffices to fix one. By invariance,
translate by `(xh_0)^-1` so that `C = H` and `C' = sH`. The event is
`E = ∪_{k ∈ K_s} {k ∈ Sp(H), ks ∈ Sp(sH), U_{k,ks} < a}`.

1. Let `k' ∈ K_s`. Then `k'H = H`, and `k'sH = s(s^-1 k' s)H = sH`, because
   `s^-1 k' s ∈ H`. Also `k'{k, ks} = {k'k, k'ks}`.
2. So `k'` permutes the index set
   `I = H ⊔ sH ⊔ E_H(H) ⊔ E_H(sH) ⊔ {{k, ks} : k ∈ K_s}`. Since
   `Sp(k'C) = k' Sp(C)`, the event `E` is `K_s`-invariant.
3. `K_s` acts on `H ⊔ sH` by left multiplication, which is free. An element
   fixing an edge setwise either fixes both endpoints, and so is `e`, or swaps
   them, and then its square is `e`. So stabilisers on `I` have order at most
   `2`.
4. `K_s` is infinite and `E` depends only on `omega|_I`. By Lemma B,
   `P(E) ∈ {0,1}`.
5. The three events for `k = e` are independent. They depend on disjoint
   coordinates: `omega|_H`, `omega|_{sH}` with its `H`-edges, and `U_{e,s}`.
   So `P(E) >= P(e ∈ Sp(H)) P(s ∈ Sp(sH)) a = theta^2 a > 0`.
6. Hence `P(E) = 1`.
∎

**Connectivity.**
1. The coset graph has vertex set `Gamma/H`, with `C ~ C'` when some link
   edge joins them. It is connected, because `G` is connected and `H`-edges
   stay inside cosets.
2. On the a.s. event of the linking lemma, adjacent cosets have spines
   joined by an edge of `L`.
3. Each `Sp(C)` is connected and infinite.
4. So `L` is a.s. connected and infinite, with density `theta`.

Letting `theta -> 0` and applying Lemma A for other generating sets proves
Theorem 1. ∎

## Base case and corollaries

**Base.** For `m >= 2`, `Z^m` is in class `Z` (`t = e_1` central,
`g = e_2`, `<g> ∩ <t> = 1`). So `fpbs-central-z2-groups-have-fiid-sparse-spines`
gives FIID sparse spines on every Cayley graph of `Z^m`, and likewise on every
class-`Z` group.

**Corollary 2.** Induct along the chain. `H_{i+1}` is finitely generated and
generated by elements of `Σ_{H_i}` computed inside `H_{i+1}`, so Theorem 1
applies with `Gamma = H_{i+1}`.

**Corollary 3(a).** Let `g_i ∈ Gamma_i` have infinite order and
`H = <g_1> x <g_2> ≅ Z^2`.
- For `s = (c, e)`, `sHs^-1 = <c g_1 c^-1> x <g_2>`, which contains
  `{e} x <g_2>`, and so does `H`.
- Symmetrically for `s = (e, c)`.

These elements generate `Gamma_1 x Gamma_2`, so Theorem 1 applies. `F_2` and
nonelementary hyperbolic groups contain elements of infinite order.

**Corollary 3(b).** Let `n >= 3`.
- *Step 1.* `P = Stab(e_1) = {[[1, *],[0, A]] : A ∈ SL_{n-1}(Z)} ≅ Z^{n-1} ⋊ SL_{n-1}(Z)`
  is finitely generated.
- *Step 2.* It contains the normal subgroup `U = {I + e_1 φ : φ ∈ (Z^n)^*, φ(e_1) = 0} ≅ Z^{n-1}`.
  This is abelian, because `(I + e_1φ)(I + e_1ψ) = I + e_1(φ+ψ)` when
  `φ(e_1) = 0`, and it is the kernel of `P -> SL_{n-1}(Z)`.
- *Step 3.* `n - 1 >= 2`, so `U` has FIID sparse spines (Base), and
  `Σ_U ⊇ P` by normality. Theorem 1 gives FIID sparse spines on `P`.
- *Step 4.* For `g ∈ SL_n(Z)`, `P ∩ gPg^-1 = Stab(e_1) ∩ Stab(ge_1)`. The
  annihilator of `span(e_1, ge_1)` in `(Z^n)^*` has rank `>= n - 2 >= 1`. Pick
  a nonzero `φ` in it, and a nonzero integral `w` with `φ(w) = 0` (possible
  since `n >= 2`).
- *Step 5.* Then `I + j wφ`, for `j ∈ Z`, are distinct elements of `SL_n(Z)`:
  the determinant is `1 + j φ(w) = 1`. Each fixes `e_1` and `ge_1`. So
  `|P ∩ gPg^-1| = ∞` for every `g`, `Σ_P = SL_n(Z)`, and Theorem 1 applies.

**Corollary 3(c).** If `H` is normal and infinite, then
`H ∩ gHg^-1 = H` is infinite for every `g`, so `Σ_H = Gamma`.

**Status.** The only imported input is the established class-`Z` theorem,
used for `Z^m`. Lemmas A and B are proved above. Agent-verified, not refereed.

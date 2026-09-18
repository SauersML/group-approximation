---
rg: 2
id: v-cone-sliding-localizes-disjoint-support-relations
kind: claim
title: In full groups of V times an ample groupoid, cone-localized global bisections slide conditions, so every commutation relation between elements with disjoint V-supports follows from relations of bounded diameter
distinct_from:
  fp-v-times-subshift-full-groups-force-quantum-rigidity: that shows one relation between conditioned 3-cycles with OVERLAPPING V-supports forces quantum rigidity; this shows relations between elements with DISJOINT V-supports never force anything, because they reduce to bounded diameter, so the necessity theorem's relation type is the only one that can carry an obstruction.
  v-times-minimal-free-sft-alternating-full-groups-are-fp: that is the finite presentation assertion P2 (refuted in general by the golden-silver product); this is a partial presentation tool for its group side, localizing where any finiteness proof must do work.
  finite-index-in-a-full-group-is-local-fullness-at-one-cone: that localizes finite index to one cone; this localizes relations to one cone, by a different mechanism (conjugation by cone-localized translations).
---

**ESTABLISHED (lane proof, unreviewed; elementary).** No priority claimed. bh-invent-01, 2026-09-18.

## Setting

- `C = {0,1}^N` with Thompson's `V`. `[u]` is the cone of the finite word `u`. `G_V` is the groupoid of germs of `V`.
- `H` is an ample groupoid with compact unit space `X`, and `T = G_V × H` acts on `C × X`. `F(·)` denotes topological full groups.
- **Conditioned elements.** For `g ∈ V` and clopen `U ⊆ X`, `c_U(g)` acts by `(c, x) ↦ (g c, x)` if `x ∈ U` and trivially otherwise. It lies in `F(T)`.
- **Cone-localized global bisections.** For `φ ∈ F(H)` (a homeomorphism of `X` given by a compact open bisection with full source and range) and a word `u`, `τ_u(φ)` acts by `(u c', x) ↦ (u c', φ x)` on `[u] × X` and trivially elsewhere. It lies in `F(T)`, since it is a union of the bisection `[u] × φ` and the unit bisection over the complement.
- For `H = Λ ⋉ X`, `X ⊆ A^Λ` a subshift, and `λ ∈ Λ`, write `τ_u(λ)` for `τ_u` of the translation `x ↦ λ·x`. A cylinder `Z(F, α) = {x : x|_F = α}` has **window** `F ⊂ Λ`. Translation moves windows: `λ·Z(F, α) = Z(λF, α∘λ^{-1})`.

## Theorem (cone sliding)

Let `u` be a word and `φ, ψ ∈ F(H)`.
1. `τ_u : F(H) → F(T)` is an injective homomorphism.
2. `τ_u(φ)` commutes with every element of `F(T)` supported in `(C ∖ [u]) × X`.
3. If `g ∈ V` is supported in `[u]`, then `τ_u(φ) c_U(g) τ_u(φ)^{-1} = c_{φ(U)}(g)`.
4. **Sliding.** Let `x = c_U(g)` and `y` be any element supported in `(C ∖ [u]) × X`, with `supp g ⊆ [u]`. Then `[x, y] = τ_u(φ)^{-1} [c_{φ(U)}(g), y] τ_u(φ)`.

**Corollary (bounded diameter).** Take `H = Λ ⋉ X` with `Λ = ⟨S⟩` and word metric `d`. Let `x = c_U(g)` and `y = c_W(g')`, with `g, g'` supported in disjoint cones and windows `F, F'`, at any distance. Then the relation `[x, y] = 1` is a consequence of relators of these three kinds, each of Λ-diameter at most `diam F + diam F' + 1`:
- (a) `τ_u(s) τ_u(s') = τ_u(s s')` and `τ_u(s)^{-1} = τ_u(s^{-1})`, which have diameter 0;
- (b) the single-step slides `τ_u(s) c_{U'}(g) τ_u(s)^{-1} = c_{sU'}(g)` for `s ∈ S`, which have diameter `diam F + 1`;
- (c) one commutator `[c_{λU}(g), c_W(g')] = 1` with `λF` at distance at most 1 from `F'`, together with `[τ_u(s), c_W(g')] = 1`.

For **site conditions**, `U = Z({p}, a)` and `W = Z({q}, b)`, every such commutator follows from relators of diameter at most 1, however far apart `p` and `q` are.

## Proof

1. On `[u] × X` the map is `φ` in the second coordinate and the identity in the first. Composition is composition in `F(H)`, and `τ_u(φ) = 1` forces `φ = 1` on `X`.
2. The two elements have disjoint supports in `C × X`, so they commute.
3. Take `(c, x)`. If `c ∉ [u]`, all three maps fix `(c, x)`, because `g` is supported in `[u]`.
   - If `c = u c'`, then `τ_u(φ)^{-1}` sends it to `(u c', φ^{-1} x)`.
   - Then `c_U(g)` applies `g` exactly when `φ^{-1} x ∈ U`, that is, when `x ∈ φ(U)`. `g` preserves `[u]`, so the result is `(g(u c'), φ^{-1} x)`, still over `[u]`.
   - Then `τ_u(φ)` gives `(g(u c'), x)`. So the conjugate is `c_{φ(U)}(g)`.
4. By item 2, `τ_u(φ)` commutes with `y`. So `τ_u(φ) [x, y] τ_u(φ)^{-1} = [τ_u(φ) x τ_u(φ)^{-1}, y]`, which is `[c_{φ(U)}(g), y]` by item 3.
5. **Corollary.** Pick `λ = s_1 ⋯ s_n` with `λF` at distance at most 1 from `F'`. Item 1 gives `τ_u(λ) = τ_u(s_1) ⋯ τ_u(s_n)`, using relators (a).
   - Item 3 applied `n` times turns `τ_u(λ) x τ_u(λ)^{-1}` into `c_{λU}(g)`. Each step is a relator (b) whose windows are `F_i` and `s F_i`, translates of `F`.
   - Item 2 for each `τ_u(s_i)` and `y` is a relator (c) with window `F'`.
   - By item 4, `[x, y]` is conjugate to `[c_{λU}(g), y]`, which is relator (c). Diameters are bounded as stated, since translating a window preserves its diameter. ∎

## Consequences and scope

- **Where distance can matter.** Every relation of `F(T)` between elements with disjoint `V`-supports is a consequence of finitely many relator shapes, for each bound on window size.
  - Unbounded-diameter relations that a finite presentation must still derive therefore involve elements whose `V`-supports overlap.
  - Those are exactly the fibrewise relations, such as `[c_{Z(p,a)}(h), c_{Z(q,b)}(h)] = 1` for one 3-cycle `h`, that `fp-v-times-subshift-full-groups-force-quantum-rigidity` linearizes into quantum families.
- **Not claimed.** This does not show that `F(T)` is presented by bounded relators plus commutators, and it does not settle P2 or P2'. The overlapping, fibrewise relations are untouched.
- **Where the cone-localized elements come from.** `τ_u(φ)` exists in `F(G_V × H)` for every global bisection `φ` of `H`, because `G_V` supplies the cone `[u]` and its complement as disjoint clopen pieces. Without the `V` factor (in `F(Λ ⋉ X)` alone) such partial translations need not exist. That is one precise sense in which the `V` factor makes presentations local.

## Lesson for general BH

The `V` factor turns distance in the acting group into a local operation. Cone-localized translations move a condition's window anywhere while commuting with everything supported on other cones. So far-apart sites never obstruct finite presentation through elements with disjoint `V`-supports.

For every full-group host of the form `G_V × H`, the finiteness problem therefore lives entirely in the fibre: in the relations among conditioned copies of one element of `V`. That is the non-commutative Boolean algebra of conditions that quantum rigidity controls.

A finite-presentation certificate for non-deterministic codings (gates P2', G3g) needs only a fibrewise statement: that commutation of conditioned copies of one fixed `V`-element at distance follows from bounded relators. Everything else is free.

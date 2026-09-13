# Păunescu's class 𝒮 is closed under extensions with amenable quotient

Lane `ex-nonsofic-action-entropy`, 2026-09-12. Handwritten proofs, nothing run.
Supports `paunescu-class-closed-under-amenable-extensions` and
`hyperbolic-3-manifold-groups-in-paunescu-class`. Status: proved here, unreviewed.

**Bounded novelty check.** Not stated in Păunescu (arXiv:1002.0605v5, Section 3: amenable
groups, free groups, amalgams over amenable subgroups, treeable groups), Alpeev
(arXiv:1706.01864, Section 5: treeable groups, subgroups), Cordeiro (arXiv:1608.05608,
relations) or Bowen--Burton (arXiv:2106.09118). Web search was exhausted before a wider
check; the statement may be folklore. The group-level analogue is
`sofic-kernel-amenable-quotient-permanence` (Elek--Szabó).

## 1. The theorem

**Theorem 1.1.** Let `N ◁ G` be countable groups with `Q = G/N` amenable, and let
`G ↷ (X, μ)` be a p.m.p. action. If the restricted action `N ↷ X` is sofic (Păunescu
Definition 1.4), then `G ↷ X` is sofic. In particular, if `N ∈ 𝒮` then `G ∈ 𝒮`.

*Notation.* `α_g(f) = f∘g^{-1}` on `L^∞(X)`, so `u_g f u_g^* = α_g(f)` in `L^∞(X) ⋊ G`,
with trace `τ(f u_g) = δ_(g,1) ∫ f dμ`. Choose a section `s : Q → G` with `s(1) = 1`, and put

```text
h(g, q) = s(gq)^{-1} g s(q) ∈ N        (g ∈ G, q ∈ Q),
```

where `gq` is the left action of `G` on `Q` through the quotient map. Then
`h(gg', q) = h(g, g'q) h(g', q)` and `h(g^{-1}, gq) = h(g, q)^{-1}`.

**Step 1 (induction over a finite window).** For finite `F ⊆ Q` define, on the algebraic crossed
product `𝒜 = L^∞(X) ⋊_alg G`, with values in `M_F(C) ⊗ (L^∞(X) ⋊ N)`:

```text
ψ_F(f)   = Σ_(q ∈ F)           e_(q,q)  ⊗ α_(s(q)^{-1})(f),
ψ_F(u_g) = Σ_(q ∈ F ∩ g^{-1}F) e_(gq,q) ⊗ u_(h(g,q)),
ψ_F(f u_g) = ψ_F(f) ψ_F(u_g),   extended linearly.
```

1. *Adjoints.* `ψ_F(u_g)^* = ψ_F(u_(g^{-1}))`, by `h(g^{-1}, gq) = h(g,q)^{-1}` and the bijection
   `q ↦ gq` from `F ∩ g^{-1}F` to `gF ∩ F`.
2. *Base.* `ψ_F(f)ψ_F(f') = ψ_F(ff')` and `ψ_F(f)^* = ψ_F(f^*)`.
3. *Covariance, exactly.* `ψ_F(u_g) ψ_F(f) = ψ_F(α_g(f)) ψ_F(u_g)`: the `(gq, q)` entry of the
   left side is `u_(h(g,q)) α_(s(q)^{-1})(f) = α_(h(g,q)s(q)^{-1})(f) u_(h(g,q))`, and
   `h(g,q) s(q)^{-1} = s(gq)^{-1} g`.
4. *Group law, approximately.* `ψ_F(u_g)ψ_F(u_(g')) − ψ_F(u_(gg'))` is minus the sum of
   `e_(gg'q, q) ⊗ u_(h(gg',q))` over `q ∈ F ∩ (gg')^{-1}F` with `g'q ∉ F`, a partial isometry
   whose support has normalized trace at most `|F ∖ g'^{-1}F| / |F|`.
5. *Trace, exactly.* `(tr_F ⊗ τ)(ψ_F(f)ψ_F(u_g)) = |F|^{-1} Σ_(q ∈ F, gq = q) τ(α_(s(q)^{-1})(f) u_(h(g,q)))`.
   Since `Q` acts freely on itself, `gq = q` forces `g ∈ N`, and then `h(g, q) = s(q)^{-1} g s(q)`
   is `1` exactly when `g = 1`. So the value is `δ_(g,1) τ(f)`.

**Step 2 (permutations).** Let `Θ_N : L^∞(X) ⋊ N → Π_(k→𝒰) M_(n_k)(C)` be a sofic embedding.
`(id ⊗ Θ_N)ψ_F` sends `f` to diagonal matrices and `u_g` to a block partial permutation with
permutation blocks, missing `|F ∖ g^{-1}F|` blocks. Completing it by any bijection between the
missing rows and columns gives a permutation `P_F(g)` with
`‖P_F(g) − (id ⊗ Θ_N)ψ_F(u_g)‖_2^2 <= 2|F ∖ g^{-1}F| / |F|`, and the completion changes the
fixed-point fraction by at most `|F ∖ g^{-1}F| / |F|`.

**Step 3 (limit).** `Q` is amenable, so there are finite `F_m` with `|gF_m Δ F_m| / |F_m| → 0` for
every `g`. Enumerate `G` and a countable weakly dense set of `f`'s. For each `m` choose a finite
stage `k_m` of `Θ_N` that is `1/m`-accurate, in trace and multiplicativity, on the finitely many
elements `α_(s(q)^{-1})(f_i)` and `u_(h(g_j,q))` with `i, j <= m`, `q ∈ F_m`. The resulting maps
into `M_(|F_m| n_(k_m))` send each `f` to a diagonal matrix and each `u_g` to a permutation, and by
Steps 1 and 2 they are asymptotically multiplicative and asymptotically trace preserving on `𝒜`.
In the ultraproduct over `m` they define a trace-preserving ∗-homomorphism on `𝒜` with
`L^∞(X)` in the diagonal and `u_g` in the permutations. It extends to the von Neumann crossed
product. ∎

## 2. Consequences

**Corollary 2.1.** 𝒮 contains `N ⋊ Z^d`, `N × A` and every extension of `N` by an amenable group,
whenever `N ∈ 𝒮`. Instances: free-by-cyclic groups `F_n ⋊_φ Z`; surface-by-cyclic groups.

*Surface groups are in 𝒮.* A closed orientable surface of genus `g >= 2` cut along a separating
curve gives `π_1(Σ_g) = F_(2h) *_Z F_(2(g−h))`, an amalgam of free groups over `Z`, which lies in 𝒮
by Păunescu Theorem 3.9 and Corollary 3.7. Punctured surface groups are free.

**Corollary 2.2.** The fundamental group of every closed hyperbolic 3-manifold lies in 𝒮. So does
every group commensurable with one, in particular every cocompact lattice of `PSL_2(C)` (Selberg:
torsion-free finite-index subgroups exist), and every group measure equivalent to one
(`paunescu-class-is-measure-equivalence-invariant`), which by 4.1 of the measure-equivalence
artifact includes the non-cocompact lattices of `PSL_2(C)` as well.

*Proof.* By virtual fibering (Agol, arXiv:1204.2810, imported in
`fpbs-fibered-3-manifold-cost-inputs`) a closed hyperbolic 3-manifold `M` has a finite cover `M'`
fibering over the circle with fiber a closed surface of genus at least two, so
`π_1(M') = π_1(S_g) ⋊ Z`. Surface groups lie in 𝒮, so `π_1(M') ∈ 𝒮` by Theorem 1.1, and 𝒮 passes
to finite-index overgroups (`sofic-action-class-closed-under-commensurability`). Lattices of one
lcsc group are measure equivalent, so the non-cocompact lattices follow. ∎

So every p.m.p. action of a lattice of `PSL_2(C)` is sofic, and its crossed product embeds in
`R^ω`. These groups have cost `1` (infimal) and are not treeable, and a closed hyperbolic 3-manifold
group does not split over an amenable subgroup, so none of the earlier permanence results reached
them. The cusped case can also be read off directly from virtual fibering of cusped manifolds
(Wise), which is not imported here and is not needed.

**Remark 2.3 (no Kazhdan groups).** An amenable quotient of a group with property (T) is finite, so
Theorem 1.1 produces no infinite Kazhdan group in 𝒮 beyond finite extensions of Kazhdan groups
already there. Every group known to lie in 𝒮 has the Haagerup property.

**Remark 2.4 (what this says about the roots).** The mixing root and the `SL_3(Z)` root need groups
outside 𝒮. Theorem 1.1 shows nonsoficity of actions cannot be created by amenable extensions:
if `G ∉ 𝒮` and `G/N` is amenable, then already `N ∉ 𝒮`.

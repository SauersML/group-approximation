---
rg: 2
id: rover-nekrashevych-groups-have-full-bns-invariant-proof
kind: route
title: Realize each character on small disjoint cones that commute with cone-fixing generators of V_d
target: rover-nekrashevych-groups-have-full-bns-invariant
requires:
  - commuting-living-generators-give-sigma-one
  - rover-nekrashevych-characters-are-sum-invariant
---

Notation as in `rover-nekrashevych-characters-are-sum-invariant`: `C = X^N`, cones `uC`, and `g_(u)` for `g in G`.
Let `μ` be the uniform Bernoulli measure on `C`.

**Step 1 (cone-fixing generators of `V_d`).** Let `T ⊆ V_d` be the set of elements that fix some cone pointwise.
Take `f in V_d`, `f != 1`, and a point `p` with `f(p) != p`.

- A table of `f` shows that `μ(f(c)) <= K μ(c)` for every cone `c` inside a piece, with `K = max_i d^{|u_i| - |v_i|}`.
- By continuity and Hausdorffness, choose a cone `c ∋ p` with `c ∩ f(c) = ∅` and `(1 + K) μ(c) < 1`.
  Then `C \ (c ∪ f(c))` is a nonempty clopen set, so it contains a cone.
- Define `t = f` on `c`, `t = f^{-1}` on `f(c)`, and `t = id` elsewhere. Then `t in V_d`, it fixes a cone
  pointwise, and `t^2 = 1`. For `y in c`, `t(f(y)) = f^{-1}(f(y)) = y`, so `tf` fixes `c` pointwise.
- Hence `f = t · (tf)` with `t, tf in T`.

So `T` generates `V_d`. `V_d` is finitely generated (Higman 1974). Writing each of finitely many generators
as a product of two elements of `T` gives a finite generating set `S_V ⊆ T`, and `S_V != ∅`.

**Step 2 (generation of `V_d(G)`).** Let `S_G` generate `G`, and choose any nonempty words `w_s` for `s in S_G`.

- By step (d) of `rover-nekrashevych-characters-are-sum-invariant-proof`, every element is `s ∘ Π_i (g_i)_(u_i)`
  with `s in V_d` and nonempty `u_i`.
- By step (b), `(g)_(u)` is `V_d`-conjugate to `g_(w)` for any nonempty `u, w`, and `g -> g_(w)` is a homomorphism.
- Hence `V_d(G) = <S_V ∪ {s_(w_s) : s in S_G}>`, and `V_d(G)` is finitely generated.

**Step 3 (a good generating set).** Let `Φ: V_d(G) -> R` be nonzero. By the claim, `Φ = Φ_χ` for a nonzero `χ` with
`ψχ = χ`. Moreover `Φ(V_d) = 0` and `Φ(g_(u)) = χ(g)` for every nonempty `u`. Since `S_G` generates `G`, pick
`g_0 in S_G` with `χ(g_0) != 0`.

- For `u in S_V` choose a cone `c_u` that `u` fixes pointwise.
- Choose pairwise distinct points `p_s` (`s in S_G`) and `q_u in c_u` (`u in S_V`).
- Choose pairwise disjoint cones `w_s ∋ p_s` and `e_u ∋ q_u` with `e_u ⊆ c_u`.
- Put `S = S_V ∪ {s_(w_s) : s in S_G} ∪ {(g_0)_(e_u) : u in S_V}`. By Step 2, `S` generates `V_d(G)`.

**Step 4 (hypotheses of the criterion).** An element `g_(w)` preserves `wC` and is the identity off `wC`.
Two elements supported in disjoint clopen sets commute.

- The living generators are every `(g_0)_(e_u)` (value `χ(g_0)`) and those `s_(w_s)` with `χ(s) != 0`.
  They are supported in pairwise disjoint cones, so they pairwise commute.
- Take `u in S_V` (dead). Then `u` commutes with `(g_0)_(e_u)`.
  - For `y in c_u`: `u y = y`, and `(g_0)_(e_u)` maps `c_u` into itself, so both products give `(g_0)_(e_u) y`.
  - For `y ∉ c_u`: `(g_0)_(e_u) y = y`, and `u y ∉ c_u` because `u` is a bijection fixing `c_u` pointwise.
    So both products give `u y`.
- A dead `s_(w_s)` commutes with every `(g_0)_(e_u)`, since the cones are disjoint.

By `commuting-living-generators-give-sigma-one`, `[Φ] in Σ^1(V_d(G))`. Since `Φ` was arbitrary,
`Σ^1(V_d(G)) = S(V_d(G))`. ∎

**Step 5 (corollary).** Bieri–Neumann–Strebel, *A geometric invariant of discrete groups*, Invent. Math. 90 (1987):
for `N ⊴ Γ` with `Γ/N` abelian and `Γ` finitely generated, `N` is finitely generated iff every character vanishing on
`N` lies in `Σ^1(Γ)`. The theorem number was not re-read here. With `Σ^1 = S` every such `N` is finitely generated.

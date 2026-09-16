---
rg: 2
id: covering-lift-copies-no-marked-lift-proof
kind: route
title: Correct each covering representative along the track of an isotopy to the marked class, then extend from the finite-index subgroup and contradict Birman non-splitting
target: covering-lift-copies-of-closed-mcgs-have-no-marked-lift
requires:
  - outer-covering-lifts-are-virtual-sections
  - based-dehn-nielsen-baer-for-closed-surfaces
  - birman-exact-sequence-does-not-virtually-split
  - birman-sequence-genus-three-does-not-virtually-split
  - closed-mcg-finite-index-injections-are-conjugations
---

Paths are composed left to right, `γ̄` is the reverse of `γ`, and `[·]` is a
homotopy class rel endpoints. `Mod` means orientation-preserving classes.

**Standard facts used (covering theory and basepoint change; not re-read).**
- A covering map induces an injection on `π_1`, whose image has index equal to
  the degree.
- An isotopy rel `∗` induces the identity on `π_1(·, ∗)`.
- For a homeomorphism `f′` and a path `δ` from `x` to `f′(x)`, the map
  `[a] ↦ [δ·(f′∘a)·δ̄]` is an automorphism of `π_1(Σ, x)`.

**Proof of (a).** Suppose `ρ_1` exists. Put `x := π(∗)`, `G := π_1(Σ, x)` and
`H := π_*(π_1(Σ̃, ∗))`. So `H` has finite index in `G`.

1. **A homomorphism to `Aut(H)`.**
   - For `f ∈ L`, choose a representative `R_f` of `ρ_1(f)` fixing `∗`. The
     automorphism `R_(f*)` of `π_1(Σ̃, ∗)` depends only on the class rel `∗`, and
     `(R_f R_(f′))_* = R_(f*) R_(f′*)`.
   - So `λ(f) := π_* ∘ R_(f*) ∘ π_*^-1` is a homomorphism `λ: L → Aut(H)`.
2. **Track of an isotopy.** Fix `f ∈ L`. By hypothesis, some `F` representing
   `p(ρ_1(f))` covers a representative `f′` of `f`.
   - `R_f` and `F` represent the same class of `Mod(Σ̃)`, so there is an isotopy
     `(H_t)` with `H_0 = R_f` and `H_1 = F`.
   - Put `γ(t) := H_t(∗)`, a path from `∗` to `F(∗)`.
   - Put `δ := π∘γ`. It runs from `x` to `π(F(∗)) = f′(π(∗)) = f′(x)`.
   - For a loop `α` at `∗`, the map `(s, t) ↦ H_t(α(s))` on the unit square has
     `R_f∘α` on its bottom edge, `F∘α` on its top edge, and `γ` on both vertical
     edges. So `[R_f∘α] = [γ·(F∘α)·γ̄]`.
3. **An automorphism of `G`.** Define `β_f ∈ Aut(G)` by
   `β_f[a] := [δ·(f′∘a)·δ̄]`.
4. **`β_f` restricts to `λ(f)`.** For a loop `α` at `∗`, use `π∘F = f′∘π`:

       β_f(π_*[α]) = [(π∘γ)·(f′∘π∘α)·(π∘γ̄)] = π_*[γ·(F∘α)·γ̄] = π_*[R_f∘α] = λ(f)(π_*[α]).

   So `β_f|_H = λ(f)`. Since `λ(f)` is an automorphism of `H`, `β_f(H) = H`.
5. **`β_f` represents `f`.**
   - Isotope `f′` to a homeomorphism `f″` fixing `x`, by an isotopy `(J_t)` with
     `J_0 = f″` and `J_1 = f′`.
   - Its track `ε(t) := J_t(x)` runs from `x` to `f′(x)`. The square argument of
     step 2 gives `[f″∘a] = [ε·(f′∘a)·ε̄]`.
   - So `β_f = c_u ∘ f″_*`, with `u := [δ·ε̄] ∈ G` and `c_u` conjugation by `u`.
   - By `based-dehn-nielsen-baer-for-closed-surfaces`, `D: Mod^±(Σ, x) → Aut(G)`,
     `[k] ↦ k_*`, is an isomorphism and `G` has trivial centre.
   - The forgetful map `Mod^±(Σ, x) → Mod^±(Σ)` is surjective, and its kernel,
     the point-pushing subgroup, corresponds under `D` to `Inn(G)` (standard). So
     `D` descends to an isomorphism `D̄: Mod^±(Σ) → Out(G)`.
   - `β_f ≡ D([f″])` modulo `Inn(G)`, and `[f″]` forgets to `f`. So `β_f`
     represents `D̄(f)`.
6. **Form (i).** Apply part (i) of `outer-covering-lifts-are-virtual-sections`
   with `N := G`, the finite-index subgroup `H`, the subgroup `D̄(L) ≤ Out(G)`,
   and `λ∘D̄^-1`.
   - `G` has unique roots, as recorded there for closed surface groups of genus
     `≥ 2`.
   - For each `f` the automorphism `β_f` represents `D̄(f)`, preserves `H` and
     restricts to `λ(f)`.

   So `σ(f) := β_f` defines a homomorphism `σ: L → Aut(G)` lifting `D̄|_L`.
7. **A section.** Put `s := D^-1∘σ: L → Mod^±(Σ, x)`.
   - `s(f)` forgets to `D̄^-1(β_f Inn(G)) = f`.
   - The orientation character of `Mod^±(Σ, x)` factors through forgetting `x`,
     and `f` preserves orientation. So `s(f) ∈ Mod(Σ, x)`.
   - So `s` splits `1 → π_1(Σ, x) → Mod(Σ, x) → Mod(Σ) → 1` over the finite-index
     subgroup `L`.
8. **Contradiction.**
   - For `g ≥ 4` this contradicts `birman-exact-sequence-does-not-virtually-split`
     (Chen--Salter, Theorem A).
   - For `g = 3` it contradicts `birman-sequence-genus-three-does-not-virtually-split`.

Injectivity of `ρ_1` was not used.

**Proof of (b).** Suppose `ρ_0` is injective and `ρ_1` lifts it.
1. `L` has finite index in `Mod^±(S_g)`. By
   `closed-mcg-finite-index-injections-are-conjugations` there is
   `φ ∈ Mod^±(S_g)` with `ρ_0(f) = φ f φ^-1` for all `f ∈ L`. Let `Φ` be a
   homeomorphism representing `φ`.
2. Take `Σ := S_g`, `Σ̃ := S_g` and `π := Φ^-1`, a covering of degree one.
3. For `f ∈ L` with representative `f′`, the homeomorphism `F := Φ∘f′∘Φ^-1`
   represents `ρ_0(f) = p(ρ_1(f))`. It satisfies
   `π∘F = Φ^-1∘Φ∘f′∘Φ^-1 = f′∘π`.
4. So `ρ_1` satisfies the hypothesis of (a), which is impossible.

**Conjugated covering lifts.** The computation in the target statement is
step 3 of (b) with `Φ: Σ̂ → Σ̃`. `∎`

# Gottschalk through Rokhlin entropy (part 2): weakly Bernoulli liftable finite extensions are sofic

Lane `gk3-rokhlin-tester`, 2026-09-14. Handwritten proofs, nothing computed. Unreviewed. Part 1 is
`research/artifacts/gk3-rokhlin-tester-2026-09-14.md`. This part proves Theorem T, the soficity transfer used for
operation (O6) of Theorem K in its full landed generality: any finite normal kernel, and no finite presentation.

## 2.1 Conventions

- **Sofic approximation.** Let `Q` be countable. A sofic approximation is a sequence `σ_n : Q -> Sym(V_n)` such that,
  over uniform `v ∈ V_n`, `σ_n(g)σ_n(h)v = σ_n(gh)v` with probability tending to `1` for all `g, h`, and `σ_n(g)v != v`
  with probability tending to `1` for `g != 1`. If `Q` is infinite, then `|V_n| -> ∞`.
- **Pattern law.** For a p.m.p. action `Q ↷ (Y, μ)`, a finite partition `p : Y -> L` and a finite `F ∋ 1`, the
  F-pattern law of `p` is the law of `(p(gy))_(g∈F)` on `L^F`.
- **Weak containment.** `Y ≺ X` when for every `p`, `F` and `ε` there is `p' : X -> L` whose F-pattern law is within `ε`
  of that of `p` in total variation.
  - Kechris's form asks only `|μ(gA_i ∩ A_j) - ν(gB_i ∩ B_j)| < ε`, and it implies the pattern form.
  - Apply it with `F ∪ {1}` to the atoms `R_ω = {y : p(gy) = ω(g) for g ∈ F}`, adjust the resulting sets `B_ω` to a
    partition at small cost, and put `p'(x) = ω(1)` on `B_ω`.
  - When `ω'(1) != ω(g)`, `μ(R_ω ∩ g^-1 R_ω') = 0`, so `ν(B_ω ∩ g^-1 B_ω') < ε`. So outside a set of measure at most
    `|F| |L|^(2|F|) ε`, the `p'`-pattern at `x ∈ B_ω` is `ω`.
- **Microstate.** A microstate for `(p, F, ε)` over `σ_n` is a map `ℓ : V_n -> L` whose empirical F-pattern law,
  the law of `(ℓ(σ_n(g)v))_(g∈F)` over uniform `v`, is within `ε` of the F-pattern law of `p`.

## 2.2 Microstates

**Lemma T1 (Bernoulli microstates).** Let `Q` be infinite and sofic with approximation `σ_n`. For every finite
partition `p'` of `[0,1]^Q`, every finite `F ∋ 1` and every `ε > 0`, a microstate for `(p', F, ε)` exists for all
large `n`.

*Proof.*
1. **Shift.** Use the shift `(gx)(h) = x(hg)`, a left action isomorphic to the usual one through `x ↦ x∘inv`.
2. **Cylinder approximation.** Approximate `p'` within measure `η` by `φ((x(k))_(k∈K))` for a finite `K` and measurable
   `φ`. The F-pattern law moves by at most `|F| η`.
3. **Random labels.** Choose `u : V_n -> [0,1]` iid uniform, and put `ℓ(v) = φ((u(σ_n(k)v))_(k∈K))`.
4. **Good points.** Call `v` good when `σ_n(k)σ_n(g)v = σ_n(kg)v` for all `k ∈ K`, `g ∈ F`, and the points `σ_n(c)v`,
   `c ∈ KF`, are distinct. The bad fraction `δ_n` tends to `0`. At a good `v`,
   `(ℓ(σ_n(g)v))_g = (φ((u(σ_n(kg)v))_k))_g` is `φ` applied to iid uniform values indexed by `KF`. That is exactly the
   F-pattern law of `φ`, so the expected empirical law is within `δ_n` of it.
5. **Concentration.** The pattern at `v` depends only on `u` on `σ_n(KF)v`. For fixed `v`, at most `|KF|^2` points `v'`
   have `σ_n(KF)v' ∩ σ_n(KF)v != ∅`. So each coordinate of the empirical law has variance at most `|KF|^2 / |V_n|`, and
   Chebyshev gives a microstate with probability tending to `1`. QED

**Lemma T2 (transfer along weak containment).** If `Y ≺ [0,1]^Q`, then `Y` has a microstate for every `(p, F, ε)` over
every sofic approximation of `Q`, for all large `n`.

*Proof.* Take `p'` with the same alphabet and F-pattern law within `ε/2`. A microstate for `(p', F, ε/2)` from Lemma
T1 is a microstate for `(p, F, ε)`. QED

## 2.3 Theorem T

**Theorem T.** Let `Q` be sofic, `N ◁ W` finite with `W/N = Q` and quotient map `π`. Suppose some p.m.p. `Q`-action
`Y_0 = X_0/N` is weakly contained in `[0,1]^Q`, where `X_0` is a free p.m.p. `W`-action. Then `W` is sofic.

*Proof.* If `Q` is finite, `W` is finite. Assume `Q` is infinite.
1. **Cocycle.** `N` acts freely on `X_0`, so a Borel transversal gives a Borel section `s : Y_0 -> X_0`. Define
   `ν(w, y) ∈ N` by `w s(y) = ν(w, y) s(π(w)y)`, and put `c_w(m) = w m w^-1`. Then:
   - `ν(ww', y) = c_w(ν(w', y)) ν(w, π(w')y)`, since
     `ww' s(y) = w ν(w', y) s(π(w')y) = c_w(ν(w', y)) ν(w, π(w')y) s(π(ww')y)`;
   - `ν(m, y) = m` for `m ∈ N`.
2. **Labels.** Fix a finite `T ∋ 1` in `W`, and put `T_2 = T ∪ TT` and `F = π(T) ∪ {1}`. Let
   `p(y) = (ν(w, y))_(w ∈ T_2)`, a finite partition with alphabet `L = N^(T_2)`. By Lemma T2, choose a microstate `ℓ`
   for `(p, F, ε)` for large `n`.
3. **Models.** On `N × V_n` put `τ_n(w)(m, v) = (c_w(m) ℓ(v)_w, σ_n(π(w))v)` for `w ∈ T_2`. For each `v` this is a
   bijection in `m`, so `τ_n(w)` is a permutation.
4. **Almost multiplicative.** Since `c_(ww') = c_w c_(w')`, for `w, w' ∈ T` we have
   `τ_n(w)τ_n(w')(m, v) = τ_n(ww')(m, v)` whenever
   - (a) `σ_n(π(w))σ_n(π(w'))v = σ_n(π(ww'))v`, and
   - (b) `ℓ(v)_(ww') = c_w(ℓ(v)_(w')) ℓ(σ_n(π(w'))v)_w`.

   Condition (b) is a condition on the F-pattern of `ℓ` at `v`. The same condition on the F-pattern of `p` holds for
   a.e. `y` by item 1, so (b) fails at a fraction at most `ε`. Condition (a) fails at a fraction tending to `0`.
5. **Almost free.** Let `w ∈ T \ {1}`.
   - If `π(w) != 1`, a fixed point needs `σ_n(π(w))v = v`, which has vanishing fraction.
   - If `w ∈ N`, then `p(y)_w = w` for every `y`. So `ℓ(v)_w = w` outside a fraction `ε`, and `σ_n(1)v = v` outside a
     vanishing fraction. At such `v`, `τ_n(w)(m, v) = (w m, v) != (m, v)`.
6. **Conclusion.** Letting `ε -> 0` and `T` increase, a diagonal sequence is a sofic approximation of `W`. QED

**Corollary T3 (operation O6).** Cases (i) and (ii) of `finite-kernel-rokhlin-ascent-from-weakly-minimal-lift` give
sofic extensions of sofic quotients.
- In case (i), `Y_0` is weakly contained in every free p.m.p. `Q`-action, in particular in `[0,1]^Q`.
- In case (ii), `Y_0` is a Bernoulli shift with base `L_0`. It is a factor of `[0,1]^Q` through a measurable map
  `[0,1] -> L_0`, and factors are weakly contained.

**Relation to main.** For central `N` over a finitely presented `Q`, this is
`weakly-bernoulli-liftable-action-makes-extension-sofic`, which builds torsor models from a presentation. Theorem T
needs neither centrality nor a presentation, because the microstates carry the cocycle directly. It is a standard
microstate argument, and no novelty is claimed.

## 2.4 Model tests

- **Hypothesis side (split).** `W = N ⋊ Q` acts on `N × [0,1]^Q` by `(m, q)(n, x) = (m c_q(n), qx)`. This is a free
  action, `N` acts by left translation on the first factor, and `Y_0 = [0,1]^Q`. The theorem says `W` is sofic, which
  is true, since `Q` has finite index `|N|` in `W`.
- **Conclusion side.** Over the Gohla–Thom lattices no such `Y_0` exists
  (`gohla-thom-lattices-no-weakly-bernoulli-liftable-action`), consistent with their conditional nonsoficity.
- **Each hypothesis is consumed.**
  - soficity of `Q`, in Lemma T1;
  - weak containment, in Lemma T2;
  - finiteness of `N`, in the finite partition `p`;
  - freeness of `X_0`, in the section and in item 5.

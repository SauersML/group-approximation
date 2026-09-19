---
rg: 2
id: strong-t-orbits-never-inject-into-subexp-times-tree-proof
kind: route
title: Weight the A-coordinate by e^{-2ε|a|}, turn half-tree walls into small-growth cocycles, let strong (T) trivialize them, and contradict with a finite-mass Følner ray or with exponential growth
target: strong-t-orbits-never-inject-into-subexp-times-tree
requires:
  - dense-finite-free-orbits-force-finite-kazhdan-subgroups
  - tree-times-zk-images-have-polynomial-ball-separators
---

Notation is as in the target. Write `f(x) = (π(x), q(x))` with `π(x) ∈ A` and `q(x) ∈ V(T)`. Both
coordinates are `L`-Lipschitz. Put `C_ε = Σ_{a∈A} e^{-2ε|a|}`, which is finite for every `ε > 0`
because `A` has subexponential growth. Put `β = |B_T(L)|`, the maximal size of an `L`-ball in `T`.

**Step 0 (Cheeger bound and growth).** Strong (T) implies (T): apply it to unitary representations,
where `C = 1`. So `K` has a Kazhdan pair `(S, κ)`. `ℓ²(O)` has no nonzero invariant vector, since `O`
is infinite and transitive. For finite `B ⊆ O` some `s ∈ S` has `|sB Δ B| = ‖λ(s)1_B − 1_B‖² ≥ κ²|B|`,
so `|sB ∖ B| ≥ κ²|B|/2`. Hence `|B_O(x₀, r)| ≥ (1+h)^r` with `h = κ²/2`.

**Fix ε.** Choose `ε > 0` with `2εL ≤ s` and `2εL < log(1+h)`, where `s` is the strong-(T) exponent
for the word length.

**Step 1 (the weighted space).**
- Let `μ(x) = e^{-2ε|π(x)|}`, `H = ℓ²(O, μ)`, and `(λ(k)F)(x) = F(k⁻¹x)`.
- Then `‖λ(k)F‖² = Σ_y |F(y)|² μ(ky)`, and `μ(ky)/μ(y) ≤ e^{2εL|k|}` because `|π(ky)| ≥ |π(y)| − L|k|`.
- So `‖λ(k)‖ ≤ e^{εL|k|}`.
- *Mass over tree sets.* For `U ⊆ V(T)`,
  `μ(q⁻¹(U)) ≤ m·|U|·C_ε`, since `f` maps `q⁻¹(v)` at most `m`-to-one into `A × {v}`.

**Step 2 (walls are coboundaries).**
- Let `e = {u, v}` be an edge of `T`. Let `T_u ∋ u` and `T_v ∋ v` be the components of `T ∖ e`, and put
  `W = q⁻¹(T_u)`. Then `O ∖ W = q⁻¹(T_v)`.
- Define `b(k) = 1_{kW} − 1_W`, so that `b(k) = λ(k)1_W − 1_W` pointwise.
- *`b(k) ∈ H`.* Suppose `x ∈ kW Δ W`. Walk from `k⁻¹x` to `x` along a word for `k`. Each step moves
  `q` by at most `L`, and somewhere the walk crosses from one side of `e` to the other. So `q(x)` lies
  within `L|k|` of an endpoint of `e`. Step 1 then gives `‖b(k)‖² ≤ 2m·|B_T(L|k|)|·C_ε < ∞`.
- *Cocycle.* `b(k₁k₂) = λ(k₁)b(k₂) + b(k₁)`. So
  `‖b(k)‖ ≤ Σ_{i<|k|} e^{εL i}·max_{t∈S}‖b(t)‖ ≤ |k| e^{εL|k|} b₁`.
- *Affine representation.* On `H ⊕ C` let `π̃(k)(F, t) = (λ(k)F + t·b(k), t)`. The cocycle identity makes
  this a representation, and `‖π̃(k)‖ ≤ C' e^{2εL|k|} ≤ C' e^{s|k|}` for a constant `C'`.
- *Strong (T).* `π̃(m_n)(0,1) = (Σ_k m_n(k) b(k), 1)` has second coordinate `1` for every `n`, so its
  norm limit is `(F₀, 1)`, a `π̃`-invariant vector. Invariance reads `b(k) = F₀ − λ(k)F₀`.
- *Conclusion.* The function `G = 1_W + F₀` satisfies `λ(k)G = G` pointwise, so `G` is constant on the
  transitive set `O`, say `G ≡ c`. Hence `1_W − c = −F₀ ∈ H`.

**Step 3 (case μ(O) < ∞).**
- Then `|B_O(x₀, r)| ≤ e^{2ε(|π(x₀)| + Lr)}·μ(O)`, because `|π(y)| ≤ |π(x₀)| + Lr` on that ball.
- This contradicts Step 0, since `2εL < log(1+h)`.
- (Step 2 is not needed in this case.)

**Step 4 (case μ(O) = ∞: orientation).**
- By Step 2, `(1 − c)²μ(W) + c²μ(O ∖ W) < ∞`. Both masses cannot be infinite, since that would need both
  `c = 1` and `c = 0`. Both cannot be finite, since `μ(O) = ∞`. So exactly one of `q⁻¹(T_u)` and
  `q⁻¹(T_v)` has finite mass. Orient `e` toward the side of infinite mass.
- *No sink.* Suppose every edge at a vertex `v` points toward `v`. Let `u₁, …, u_r` be the neighbours of
  `v`, with `r` bounded. Each `q⁻¹(T_{u_i})` has finite mass (take the component of `T ∖ {v,u_i}` that
  contains `u_i`). So `μ(O) ≤ μ(q⁻¹(v)) + Σ_i μ(q⁻¹(T_{u_i})) < ∞` by Step 1, which is a contradiction.
- *At most one outgoing edge.* Suppose edges `{v,u₁}` and `{v,u₂}` both point away from `v`. Then the
  complements of `q⁻¹(T_{u₁})` and `q⁻¹(T_{u₂})` have finite mass. The sets `T_{u₁}` and `T_{u₂}` are
  disjoint, so these two complements cover `O`, and `μ(O) < ∞`, which is a contradiction.
- *The ray.* Every vertex has exactly one outgoing edge. Following outgoing edges from `v₀` gives
  `v₀, v₁, …`. It never backtracks, because the edge `{v_j, v_(j+1)}` is incoming at `v_(j+1)`. In a
  tree it is therefore a geodesic ray.
- *The sets `D_j`.* Let `D_j = q⁻¹(side of {v_j, v_(j+1)} containing v_j)`. Each has finite mass. They
  increase in `j`, and they exhaust `O`: if the geodesic from `q(x)` meets the ray first at `v_i`, then
  `x ∈ D_j` for all `j ≥ i`. So `μ(D_j) → ∞`.

**Step 5 (the Følner contradiction).**
- Set `ξ_j = 1_{D_j}/μ(D_j)^{1/2}`, a unit vector in `H`.
- For fixed `k`, the Step 2 estimate applied to the wall `D_j` gives
  `‖λ(k)ξ_j − ξ_j‖² ≤ 2m|B_T(L|k|)|C_ε/μ(D_j)`, which tends to `0` as `j → ∞`.
- The `λ`-invariant vectors are the constants, because `O` is transitive. Constants are not in `H`,
  because `μ(O) = ∞`. So `P_λ = 0`, and strong (T) with `C = 1` gives `‖λ(m_n)‖ → 0`.
- Fix `n` with `‖λ(m_n)‖ < 1/2`. Since `m_n` is finitely supported,
  `‖λ(m_n)ξ_j − ξ_j‖ ≤ Σ_k m_n(k)‖λ(k)ξ_j − ξ_j‖ → 0`. Hence `‖λ(m_n)ξ_j‖ → 1`, which contradicts
  `‖λ(m_n)‖ < 1/2`.
- Steps 3 to 5 exclude both cases, so no `f` exists. ∎

**Consequence 1.** This is item 2 of `tree-times-zk-images-have-polynomial-ball-separators`, with
`m = 1`, `A = Z^2` and `T = T_{2d}`. The case `d ≤ 1` is subsumed by embedding `F_d` in `F_2`.

**Consequence 2.**
- Let `K` be a strong-(T) subgroup of `[[(Z^2×F_d) ⋉ (Ω×∂F_d)]]`.
- The corollary of `dense-finite-free-orbits-force-finite-kazhdan-subgroups` sends an infinite orbit
  through a free point to an injective bounded-left-displacement map into `Z^2×F_d`. Consequence 1
  forbids this, so every orbit through a free point is finite.
- That corollary, with dense `X_free`, then makes `K` finite.
- `SL_3(Z)` is infinite, has strong (T) by de la Salle, and is finitely presented with solvable word
  problem. So it does not embed.

**Where the method stops.**
- *Step 2 needs strong (T).* The representation `λ` has exponential norm growth `e^{εL|k|}`, and
  ordinary (T) says nothing about it. Infinite hyperbolic groups lack strong (T) (Lafforgue), so
  hyperbolic Kazhdan groups are not covered.
- *Step 1 needs `C_ε < ∞` for every small `ε`.* If `A` has exponential growth, the fibre masses
  `μ(q⁻¹(v))` can be infinite and the wall cocycle can fail to lie in `H`.
- *Steps 4 and 5 need a tree.* Over `T×T` there are two independent families of infinite-mass walls,
  and no orientation argument applies. This matches the existence of Kazhdan subgroups over
  product-of-trees and Ã₂ scaffolds.

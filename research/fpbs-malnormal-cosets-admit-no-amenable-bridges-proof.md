---
rg: 2
id: fpbs-malnormal-cosets-admit-no-amenable-bridges-proof
kind: route
title: An invariant field of boundary measures must sit on the limit set of each infinite coset piece by mass transport, and malnormal cosets have disjoint limit sets
target: fpbs-malnormal-cosets-admit-no-amenable-bridges
requires: []
---

Complete proof. Notation of the target: `L` free on a finite basis `S`,
`K ≤ L` finitely generated, `a` a free p.m.p. action on `(X, μ)`,
`R_L`, `R_K`, `E ⊆ R_L` amenable, `Y` the union of the infinite
`E ∩ R_K`-classes. Malnormality is used only in Step 4.

**Imports.**
- (Z) Zimmer amenability. If `E` is an amenable countable Borel p.m.p.
  relation, `Z` a compact metrizable space and `α : E → Homeo(Z)` a Borel
  cocycle, then there is a Borel map `x ↦ ν_x ∈ Prob(Z)` and an `E`-invariant
  conull set `X_0` with `α(y, x)_* ν_x = ν_y` for all `(x, y) ∈ E|_{X_0}`.
  Zimmer, J. Funct. Anal. 27 (1978); Connes--Feldman--Weiss, Ergodic Theory
  Dynam. Systems 1 (1981), amenable = hyperfinite; this is the property used
  by Adams, "Trees and amenable equivalence relations" (1990). For hyperfinite
  `E = ∪ E_n` it follows directly: average `α(x, y)_* δ_{z_0}` over
  `[x]_{E_n}`, take a weak* limit point in `L^1(X; C(Z))^*`, note that
  `E_n`-invariance is weak* closed, and disintegrate.
- (M) Mass transport. For Borel `f : R_L → [0, ∞]`,
  `∫ Σ_{y ∈ [x]} f(x, y) dμ(x) = ∫ Σ_{x ∈ [y]} f(x, y) dμ(y)`
  (invariance of the counting measure on a p.m.p. relation, Feldman--Moore).
- (S) Stallings. A finitely generated `K ≤ L` has a finite based core graph.

**Step 0 (orbit trees).** Let `Cay` be the Cayley tree of `L` with edges
`{γ, γs}`, `s ∈ S`, and `∂L` its end space, a Cantor set. For `x ∈ X` put
`Φ_x : [x]_{R_L} → L`, `γx ↦ γ^{-1}`. It is a bijection by freeness. Declare
`y, sy` adjacent (`s ∈ S`); then `Φ_x` is a graph isomorphism from this orbit
graph `T_x` onto `Cay`, since `Φ_x(sγx) = γ^{-1}s^{-1}`. The graph `T_x` and
its end space `∂T_x` depend only on the class `[x]_{R_L}`.
- For `y = γx`, `Φ_y ∘ Φ_x^{-1}` is left multiplication by `γ` on `Cay`.
  Indeed the vertex `δx = (δγ^{-1})y` goes to `δ^{-1}` and to `γδ^{-1}`. So
  the coordinate change is the Borel cocycle `c(y, x) = γ`, acting on `∂L`
  by homeomorphisms.
- The `R_K`-class of `y = γx` is `C(y) = Kγx`, and
  `Φ_x(C(y)) = γ^{-1}K`. In particular `Φ_x(C(x)) = K` for every `x`.

**Step 1 (hulls and limit sets in `Cay`).** Let `H = hull(K)` be the union
of the geodesics `[k, k']`, `k, k' ∈ K`, a subtree containing `1`. Let
`Λ(K) ⊆ ∂L` be the set of limits of sequences in `K`.
- (a) By (S), `H` is the lift of the finite based core graph of `K`, so
  every vertex of `H` is within some `R < ∞` of `K`. Hence `∂H = Λ(K)`:
  an end of `H` is approached by points of `K` at distance at most `R` from
  its ray, and conversely the geodesics `[1, k_n]` lie in `H` and converge to
  the ray to `lim k_n`. `Λ(K)` is closed.
- (b) For `ξ ∈ ∂L \ Λ(K)`, the ray from any vertex of `H` to `ξ` leaves the
  subtree `H` at a last vertex `π(ξ)`, independent of the starting vertex.
  The map `π : ∂L \ Λ(K) → V(H)` is locally constant on this open set.
- (c) **Disjointness.** If `g ∈ L` and `Λ(K) ∩ gΛ(K) ≠ ∅`, then
  `K ∩ gKg^{-1} ≠ 1`. Proof. Let `ξ` be in both. The ray `r_0 = 1, r_1, ...`
  to `ξ` lies in `H` (as `1 ∈ H` and `ξ ∈ ∂H`), and it eventually lies in
  `gH = hull(gK)` (the ray from `g` to `ξ` lies in `gH` and two rays to one
  end eventually coincide). So for all large `n` there are `k_n, k'_n ∈ K`
  with `d(r_n, k_n) ≤ R` and `d(r_n, g k'_n) ≤ R`. The elements
  `c_n = k_n^{-1} g k'_n` have length at most `2R`, so take finitely many
  values, while `|k_n| ≥ n − R` gives infinitely many distinct `k_n`. Choose
  `n ≠ m` with `c_n = c_m` and `k_n ≠ k_m`. Then
  `1 ≠ k_m k_n^{-1} = g (k'_m k'_n^{-1}) g^{-1} ∈ K ∩ gKg^{-1}`. ∎
- (d) If `K` is malnormal and `g ∉ K`, then `Λ(K) ∩ gΛ(K) = ∅`, by (c).
- Transported by `Φ_x`: `hull(C(x))` in `T_x` has end set
  `Λ(C(x)) = Φ_x^{-1}(Λ(K))`, and a nearest-point projection
  `π_x = Φ_x^{-1} ∘ π ∘ Φ_x` from `∂T_x \ Λ(C(x))` to the vertices of
  `hull(C(x))`, which are orbit points. For `y = γx`,
  `Λ(C(x)) ∩ Λ(C(y)) = Φ_x^{-1}(Λ(K) ∩ γ^{-1}Λ(K))`.

**Step 2 (invariant boundary measures).** Apply (Z) to `E` and the cocycle
`c|_E` acting on `Z = ∂L`. This gives `ν_x` and `X_0`. Put
`ν̃_x = (Φ_x^{-1})_* ν_x ∈ Prob(∂T_x)`. For `(x, y) ∈ E|_{X_0}`,
`ν̃_y = (Φ_y^{-1})_* (Φ_y Φ_x^{-1})_* ν_x = ν̃_x`. So on `X_0` the measure
`ν̃_x` on the common end space `∂T_x = ∂T_y` is constant along `E`-classes.

**Step 3 (mass transport: infinite pieces carry no mass off the limit set).**
For `x ∈ X_0` let `m_x = (π_x)_* ( ν̃_x restricted to ∂T_x \ Λ(C(x)) )`,
a measure of total mass at most `1` on the vertices of `hull(C(x))`.
- **Borel.** In coordinates `Φ_x(m_x) = π_*(ν_x restricted to ∂L \ Λ(K))`,
  a measure on the fixed countable set `V(H)`, and `x ↦ ν_x` is Borel.
- **Piece-constant.** If `(x, y) ∈ E ∩ R_K` with `x, y ∈ X_0`, then
  `ν̃_x = ν̃_y` (Step 2) and `C(x) = C(y)`, so `m_x = m_y` as measures on
  orbit points.
- Let `B = { x ∈ Y ∩ X_0 : m_x ≠ 0 }`. It is Borel and
  `E ∩ R_K`-invariant. For `x ∈ B` let `M_x` be the set of vertices where
  `m_x` attains its maximum. It is finite and nonempty, since the total mass
  is finite and positive, and `M_x = M_y` on each piece.
- Put `f(x, y) = 1/|M_x|` if `x ∈ B` and `y ∈ M_x`, and `f = 0` otherwise.
  This is Borel on `R_L`, as `M_x` is Borel in coordinates.
- Left side of (M): `Σ_y f(x, y) = 1_B(x)`, integral `μ(B)`.
- Right side: `g(y) = Σ_x f(x, y)`. If `f(x, y) > 0`, then every `x'` in
  the infinite piece `[x]_{E ∩ R_K} ∩ X_0` has `f(x', y) = 1/|M_x| > 0`, so
  `g(y) = ∞`. (`X_0` is `E`-invariant, so the piece lies in `X_0`.) Thus
  `g` takes only the values `0` and `∞`, and `∫ g = μ(B) ≤ 1` forces `g = 0`
  a.e. Hence `μ(B) = 0`.
- **Conclusion.** For almost every `x ∈ Y`,
  `ν̃_x(∂T_x \ Λ(C(x))) = m_x(total) = 0`, that is, `ν̃_x` is carried by
  `Λ(C(x))`.

**Step 4 (one coset per class).** Let `N` be the union of `X \ X_0` and the
null set where the conclusion of Step 3 fails, and `N'` its
`R_L`-saturation. `N'` is null, as `R_L` is a countable p.m.p. relation.
Let `x, y ∈ Y \ N'` with `x ~_E y`, and write `y = γx`. By Steps 2 and 3,
the probability measure `ν̃_x = ν̃_y` is carried by
`Λ(C(x)) ∩ Λ(C(y)) = Φ_x^{-1}(Λ(K) ∩ γ^{-1}Λ(K))`. So this set is
nonempty, and Step 1(c) gives `K ∩ γ^{-1}Kγ ≠ 1`. That set is infinite,
since nontrivial elements of `L` have infinite order. This is **item 4**. If
`K` is malnormal, Step 1(d) gives `γ^{-1} ∈ K`, so `y ∈ Kx = C(x)`. This is
**item 1**.

**Items 2 and 3.**
- If `E ∩ R_K` is aperiodic on the `E`-invariant set `Z`, then `Z ⊆ Y`, so
  `E|_Z ⊆ E|_Y ⊆ R_K` a.e.
- If `E ⊇ F` with `F ⊆ R_K` aperiodic, then `E ∩ R_K ⊇ F` is aperiodic
  everywhere, so `E ⊆ R_K`. For `1 ≠ k ∈ K`, `R_{<k>}` is aperiodic, since
  `k` has infinite order and the action is free.
- For item 3: then `E ⊆ R_K`, so `R_K ∨ E = R_K`. If `g ∈ L \ K`, then
  `(x, gx) ∉ R_K` for every `x` by freeness, so `R_K ≠ R_L`. ∎

**What is not proved.** Nothing here concerns amenable `E` whose trace
`E ∩ R_K` has finite classes on a positive set. Those are exactly the
approximate bridges, whose relative cost can be small but positive. The
argument gives no quantitative bound for them, because the transport in
Step 3 yields a contradiction only through infinite pieces.

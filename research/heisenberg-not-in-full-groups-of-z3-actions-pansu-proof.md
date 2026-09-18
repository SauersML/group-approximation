---
rg: 2
id: heisenberg-not-in-full-groups-of-z3-actions-pansu-proof
kind: route
title: Short period vectors give quadratic orbit growth; otherwise the displacement map H → Z^3 blows down to a Lipschitz map that Pansu's theorem flattens onto a plane
target: heisenberg-not-in-full-groups-of-z3-actions
requires:
  - heisenberg-not-in-wobbling-groups-of-quadratic-growth-graphs
  - pansu-differentiability-of-lipschitz-carnot-maps
---

Norms on `Z^3` and `R^3` are `ℓ^1` unless marked; constants `C_i, c_i > 0`
depend only on the fixed geometry of `H` unless a dependence is stated.
`|·|_w` and `d_w` are the word length and the left-invariant word metric of
`H` for `{a^{±1}, b^{±1}}`. Commutators are `[x,y] = xyx^{-1}y^{-1}`.

## 0. Set-up

Let `ρ : H → [[Z^3 ↷ X]]` be a homomorphism. For `s ∈ {a^{±1}, b^{±1}}`
choose cocycles `v_s : X → Z^3` with `ρ(s)y = T^{v_s(y)} y` and
`|v_s(y)| ≤ K` for all `y`. Then each `Z^3`-orbit `O` is `ρ(H)`-invariant.

For `v ∈ X` let `S_v ≤ H` be its stabilizer. Since `Z(H) = ⟨c⟩`, there is a
unique `m_v ≥ 1` or `m_v = ∞` with `S_v ∩ ⟨c⟩ = ⟨c^{m_v}⟩`. It is the size of
the `⟨ρ(c)⟩`-orbit of `v`.

**Reduction.** Suppose `ρ(c)` has infinite order. Then
`sup_v m_v = ∞`: if every `m_v ≤ B` then `ρ(c)^{B!}` fixes every point.
Everything below allows `m_v = ∞`, read with `1/∞ = 0`. We derive a
contradiction.

Let `Λ ≤ Z^3` be the `Z^3`-stabilizer of `v`. It is the same for every point
of `O = Z^3 v`, because `Z^3` is abelian.

## 1. Orbits with a short period vector

Suppose `Λ` contains `λ ≠ 0` with `|λ| ≤ 10K`. Let `Γ_O` be the graph on `O`
with edges `y — T^{±e_i} y`, which is the Schreier graph of `Z^3/Λ`.

**Growth.** Take `r ≥ 1`. Each point `p` of the ball `B_{Γ_O}(y, r)` has
`p = T^q y` with `|q| ≤ r`. The vectors `q + kλ` with `|k| ≤ r/|λ|` are
distinct, lie in `B_{Z^3}(2r)`, and are disjoint for distinct `p`. Since
`2⌊r/|λ|⌋ + 1 ≥ r/|λ|` and `|B_{Z^3}(2r)| ≤ (4r+1)^3 ≤ 125 r^3`,
`|B_{Γ_O}(y, r)| ≤ 125 |λ| r^2 ≤ 1250 K r^2`.

**Displacement.** `ρ(a)`, `ρ(b)` move each `y ∈ O` by at most `K` in `Γ_O`.
The restriction of `ρ` to `O` is a homomorphism `H → W(Γ_O)`. By item 1 of
`heisenberg-not-in-wobbling-groups-of-quadratic-growth-graphs`, with
`C = 1250K`, every `⟨ρ(c)⟩`-orbit in `O` has at most
`M_0 = ⌈169·1250 K^3⌉^2` points. So `m_v ≤ M_0`.

**Conclusion.** Every `v` with `m_v > M_0` has no nonzero period vector of
norm `≤ 10K`.

## 2. Orbits without a short period vector: the displacement map

Suppose `Λ` has no nonzero vector of norm `≤ 10K`. For a word
`w = s_n ⋯ s_1` put `y_0 = v`, `y_i = ρ(s_i) y_{i-1}` and
`D(w) = Σ_i v_{s_i}(y_{i-1})`. Then `T^{D(w)} v = ρ(w) v`, and
`D(w'w) = D(w) + D_{ρ(w)v}(w')`, where `D_y` uses base point `y`.

- **Backtracks.** `v_s(y) + v_{s^{-1}}(ρ(s)y)` lies in `Λ` and has norm
  `≤ 2K`, so it is `0`.
- **Relators.** Both relators and their inverses have length 10. The
  displacement of a relator loop at any `y ∈ O` lies in `Λ` and has norm
  `≤ 10K`, so it is `0`.

Two words equal in `H` are related by inserting and deleting `ss^{-1}` and
relators `r^{±1}`. Each move inserts or deletes a closed loop of displacement
`0` and leaves the rest of the path unchanged, so `D` is preserved. Hence
`F(h) = D(w)` for any word `w` representing `h` is well defined, and
`F(e) = 0`, `T^{F(h)} v = ρ(h) v`, `F(sh) = F(h) + v_s(ρ(h)v)`.

Put `f(g) = F(g^{-1})`. Then `|f(gs) − f(g)| ≤ K`, so
`f : (H, d_w) → Z^3` is `K`-Lipschitz.

**Fibres.** If `f(g) = f(g')`, then `ρ(g^{-1})v = ρ(g'^{-1})v`, so
`g'g^{-1} ∈ S_v` and `g^{-1}g' ∈ S^g := g^{-1} S_v g`. Moreover
`S^g ∩ ⟨c⟩ = ⟨c^{m_v}⟩`, because `c` is central.

## 3. Counting a subgroup in a word ball

**Lemma.** Let `S' ≤ H` with `S' ∩ ⟨c⟩ = ⟨c^m⟩` (`1 ≤ m ≤ ∞`) and let
`ρ_w ≥ 1`. Then
`|S' ∩ B_w(ρ_w)| ≤ (4ρ_w^2/m + 4ρ_w + 1)(8ρ_w^2/m + 1)`. If `m ≥ ρ_w^2` this
is `≤ 81 ρ_w`.

*Proof.* Let `π : H → Z^2` be abelianization and `P = π(S')`.

- **Central length.** Push a word of length `L` into the normal form
  `a^x b^y c^s`. Each letter `a^{±1}` passes at most `L` letters `b^{±1}` and
  creates at most `L` central letters. So `|s| ≤ L^2`, and
  `|c^n|_w ≥ √|n|`.
- **Fibres of `π`.** Two elements of `S' ∩ B_w(ρ_w)` with the same image
  differ by `c^{km}` with `|c^{km}|_w ≤ 2ρ_w`. So `|km| ≤ 4ρ_w^2`, and a fibre
  has at most `8ρ_w^2/m + 1` points.
- **The image.** `π(B_w(ρ_w))` lies in the `ℓ^1` ball of radius `ρ_w`.
  - If `P` has rank `≤ 1`, the count is `≤ 2ρ_w + 1`.
  - If `P` has rank 2, it has a Hermite basis `(k,0)`, `(j,l)` with
    `k, l ≥ 1`. Lifts `s_1, s_2 ∈ S'` satisfy `[s_1,s_2] = c^{±kl} ∈ S'`, so
    `m` divides `kl` (and `m < ∞`). Counting rows `y ∈ lZ` and then a coset
    of `kZ` in each row gives
    `≤ (2ρ_w/l + 1)(2ρ_w/k + 1) ≤ 4ρ_w^2/(kl) + 4ρ_w + 1 ≤ 4ρ_w^2/m + 4ρ_w + 1`.

Multiplying the two counts gives the bound. If `m ≥ ρ_w^2`, it is
`≤ (4ρ_w + 5)·9 ≤ 81ρ_w`. ∎

**Corollary.** In the setting of §2, let `A ⊆ H` have `d_w`-diameter
`≤ ρ_w`, with `ρ_w ≥ 1` and `m_v ≥ ρ_w^2`. By §2, each fibre of `f` in `A`
containing `g` lies in `g(S^g ∩ B_w(ρ_w))`. So `|f(A)| ≥ |A| / (81 ρ_w)`.

## 4. H as a lattice in the Carnot group G = H_3(R)

Let `g = span(X, Y, T)` with `[X,Y] = T`, stratified by `V_1 = span(X,Y)`
and `V_2 = RT`. `G = exp g` has CC distance `d` (with `X, Y` orthonormal),
dilations `δ_λ(x,y,t) = (λx, λy, λ^2 t)` in exponential coordinates, and
`d(h) = d(e,h)`.

By BCH, `a = exp X`, `b = exp Y`, `c = exp T` satisfy the relations of `H`,
and `a^x b^y c^s = (x, y, xy/2 + s)`. So `H ≅ Γ = {(x,y,t) : x,y ∈ Z,
t − xy/2 ∈ Z}`, a discrete subgroup.

- **(G1)** `d(g,g') ≤ C_1 d_w(g,g')` on `Γ`, with
  `C_1 = max(d(a), d(b))`. This is left invariance.
- **(G2)** `d_w(g,g') ≤ C_2 d(g,g') + C_2` on `Γ`. By left invariance take
  `g = e`, `g' = (x,y,t)`, and write `g' = a^x b^y c^s` with
  `s = t − xy/2`. Using `c^{p^2} = [a^p, b^p]` and `c^r = [a^r, b]`,
  `|c^s|_w ≤ 8√|s| + 2`, so `|g'|_w ≤ |x| + |y| + 8√(|t| + |xy|/2) + 2`. The
  homogeneous norm `‖·‖` of (2.4) is comparable to
  `|(x,y)| + √|t|`, being a homogeneous norm. Then (2.5) gives (G2), and we take `C_2 ≥ 1`.
- **(G3)** `μ := min{d(h) : h ∈ Γ∖{e}} > 0`, since `Γ` is discrete and
  closed CC balls are compact.
- **(G4)** `|x| + |y| ≤ 2 d(h)` for `h = (x,y,t)`. The projection to `V_1`
  maps horizontal curves to plane curves of the same length.
- **(G5)** `D = {a^x b^y c^s : x, y, s ∈ [0,1)}` (real exponents, meaning
  `(x, y, xy/2 + s)`) is a fundamental domain for left multiplication by
  `Γ`. Left multiplication by `a^p b^q c^n` sends the coordinates `(x,y,s)`
  to `(x+p, y+q, s+n−qx)`, which is uniquely normalised into `[0,1)^3`. It
  contains `e`, has compact closure of diameter `δ_D < ∞`, and has positive
  finite Lebesgue measure `|D|`.
- **(G6)** Haar measure is Lebesgue measure and `δ_λ` scales it by `λ^4`. So
  `|B(z,R)| = β R^4` with `β = |B(e,1)| > 0`. For `R ≥ 2δ_D`, every
  `γ ∈ Γ` with `γD ∩ B(z, R − δ_D) ≠ ∅` has `γ ∈ γD ⊆ B(z,R)`, and these
  translates cover `B(z, R − δ_D)`. Hence
  `|Γ ∩ B(z,R)| ≥ β(R − δ_D)^4/|D| ≥ c_6 R^4`, with `c_6 = β/(16|D|)`.

## 5. Blow-down

By the reduction and §1, for each integer `j > M_0^{1/3}` choose `v_j ∈ X`
with `m_j := m_{v_j} ≥ j^3`. Each `v_j` has no short period vector, so §2
gives a `K`-Lipschitz `f_j : H → Z^3` whose fibres obey the Corollary of §3.
Identify `H = Γ`.

**Rescaled maps.** On `δ_{1/j}Γ` put `φ_j(δ_{1/j}g) = (f_j(g) − f_j(e))/j`.
For `g ≠ g'`, (G2) and (G3) give
`|f_j(g) − f_j(g')| ≤ K C_2 (1 + 1/μ) d(g,g')`. Dilations scale `d` by `1/j`,
so `φ_j` is `K_1`-Lipschitz from `(δ_{1/j}Γ, d)` to `(R^3, |·|_2)`, with
`K_1 = √3 K C_2 (1 + 1/μ)`. Extend each coordinate by McShane's formula. This
gives `u_j : G → R^3`, `K_2`-Lipschitz with `K_2 = 3K_1`, and `u_j(e) = 0`.

**Limit.** `(G, d)` is proper. By Arzelà–Ascoli a subsequence (still indexed
by `j`) converges uniformly on compact sets to a `K_2`-Lipschitz
`u : G → R^3`.

**Differential.** By `pansu-differentiability-of-lipschitz-carnot-maps`
(target `R^3`), `u` is Pansu differentiable at some `x_0`, with group linear
`L : G → R^3`.

- `L` is a homomorphism to an abelian group, so it kills commutators. Every
  central element `exp(tT)` is the commutator `[exp(±√|t| X), exp(√|t| Y)]`,
  so `L` kills the centre.
- `exp(xX) exp(yY) = exp(xX + yY)·(central)`, so
  `L(x,y,t) = L(exp xX) + L(exp yY)`.
- Dilation equivariance and `L(h^{-1}) = −L(h)` give `L(exp xX) = x L(a)` for
  every real `x`, and similarly for `Y`.
- So `L(x,y,t) = x v_1 + y v_2` with `v_1 = L(a)`, `v_2 = L(b)`.
- The limit formula gives `|L(h)|_2 ≤ K_2 d(h)`, so `|v_i|_2 ≤ K_2 C_1`, and
  by (G4) `|L(h)|_2 ≤ 2 K_2 C_1 d(h)`.
- The image of `L` lies in a plane `P ⊆ R^3`.

**Constants.** Put `C_3 = 2K_2 C_1` and
`C_5 = 2π(C_3 + 3)^2`. Put `c_7 = c_6/(243 C_2)`. Choose, in this order:

1. `ε ∈ (0,1)` with `2 C_5 ε ≤ c_7/2`;
2. `r > 0` with `|u(x_0 h) − u(x_0) − L(h)|_2 ≤ ε d(h)` whenever `d(h) ≤ r`,
   by Pansu differentiability at `x_0`;
3. `j` in the subsequence so large that all of the following hold:
   - `sup_{B̄(x_0,r)} |u_j − u|_2 ≤ εr`;
   - `rj ≥ max(1, 2δ_D)`;
   - `j ≥ 9 C_2^2 r^2`;
   - `c_7 rj/2 > C_5`.

**Upper count.** Let `A_j = Γ ∩ B(δ_j x_0, rj)`. For `g ∈ A_j` put
`y = δ_{1/j} g ∈ B(x_0, r)` and `h = x_0^{-1} y`, so `d(h) ≤ r`. Then
`f_j(g) = f_j(e) + j u_j(y)` and
`|u_j(y) − u(x_0) − L(h)|_2 ≤ 2εr`.

So `f_j(A_j)` lies within Euclidean distance `η = 2εrj` of the planar disc
`f_j(e) + j u(x_0) + {p ∈ P : |p|_2 ≤ C_3 rj}`. The disjoint unit cubes
centred at these lattice points lie in a cylinder of radius
`C_3 rj + η + 1` and height `2(η + 1)`. Since `rj ≥ 1` and `ε < 1`,
`|f_j(A_j)| ≤ 2π(C_3 rj + η + 1)^2 (η + 1) ≤ C_5 (rj)^2 (2εrj + 1)`.

**Lower count.** By (G6) and `rj ≥ 2δ_D`, `|A_j| ≥ c_6 (rj)^4`. `A_j` has
`d`-diameter `≤ 2rj`, so by (G2) its `d_w`-diameter is at most
`ρ_w := 3C_2 rj ≥ 1`. Also `m_j ≥ j^3 ≥ 9C_2^2 r^2 j^2 = ρ_w^2`. The
Corollary of §3 gives
`|f_j(A_j)| ≥ c_6 (rj)^4 / (81 · 3C_2 rj) = c_7 (rj)^3`.

**Contradiction.** Combining the two counts,
`c_7 rj ≤ 2C_5 ε rj + C_5 ≤ (c_7/2) rj + C_5`, i.e. `c_7 rj/2 ≤ C_5`. This
contradicts the choice of `j`. So `ρ(c)` has finite order. ∎

## 6. Trust surface

- **Imported on this graph.**
  - Item 1 of `heisenberg-not-in-wobbling-groups-of-quadratic-growth-graphs`
    (ESTABLISHED, unreviewed), used only in §1.
  - Pansu's theorem with target `R^3`, verbatim from Pinamonti–Speight,
    including (2.5) and Haar = Lebesgue.
- **Standard, not imported.**
  - McShane extension of real Lipschitz functions.
  - Arzelà–Ascoli on a proper metric space.
  - Properness of `(G,d)`: CC balls are compact because `d` induces the
    Euclidean topology and (2.5) bounds balls.
  - Hermite normal form for subgroups of `Z^2`.
  - Presentations: equal words are related by free moves and relator
    insertions.
  - The BCH formula in step 2 and the formulas for `X`, `Y` in exponential
    coordinates.
- **What fails in dimension ≥ 4.** Everything through the Pansu step works
  for `Z^N`, but the upper count does not. In `R^N` an `η`-neighbourhood of a
  planar disc of radius `~rj` holds `~(rj)^2 η^{N−2} ~ ε^{N−2}(rj)^N` lattice
  points. For `N ≥ 4` this exceeds the lower count `~(rj)^3`. The failure is
  genuine for large `N`: `heisenberg-group-embeds-in-wobbling-group-of-some-zn`
  gives `H ≤ W(Z^N)`. `N = 4` is open.

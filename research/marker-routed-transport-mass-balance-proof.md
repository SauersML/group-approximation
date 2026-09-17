---
rg: 2
id: marker-routed-transport-mass-balance-proof
kind: route
title: Count incoming routes at the identity under an invariant measure, then localize collisions to finite windows
target: marker-routed-paradoxical-transport-must-collide
requires: []
artifacts:
  - experiments/paradoxical-transport-2026-09-17/marker_routing_sat.py
---

Notation as in the target. Throughout, `(h·x)(g) = x(h^(-1) g)`, so `(g^(-1)·x)(k) = x(g k)`, and
`E(x) = {g : g^(-1)·x ∈ E}`. Equivariance: `p_i(h·x, h g) = h g · s_i(g^(-1) h^(-1) h·x) = h · p_i(x, g)`.

## 1. Balance

A pair `(g, i)` contributes to `N(x)` exactly when `g ∈ M(x)` and `g s_i(g^(-1)·x) = 1`, that is `g = d^(-1)` with
`d = s_i(g^(-1)·x) ∈ S`. Writing `g = d^(-1)`, `g^(-1)·x = d·x`, so

    N(x) = Σ_(i=1..m) Σ_(d ∈ S) 1[ d·x ∈ M  and  s_i(d·x) = d ].

Each summand is the indicator of a Borel set (clopen when `s_i` is continuous), and the sum is finite. For a
`G`-invariant probability `μ`, `μ{x : d·x ∈ E} = μ(E)`, hence

    E_μ N = Σ_i Σ_d μ{ x ∈ M : s_i(x) = d } = Σ_i μ(M) = m μ(M),

because the events `{s_i = d}`, `d ∈ S`, partition `M`. Only invariance and Borel measurability were used.

Pointwise, `N <= 1_T + (N-1)_+ 1_T + N 1_(X∖T)`: if `1 ∈ T(x)`, `N <= 1 + (N-1)_+`; otherwise `N = N 1_(X∖T)`. Taking
expectations: `m μ(M) <= μ(T) + E_μ[(N-1)_+] + E_μ[N 1_(X∖T)]`, which is item 1.

## 2. Collision-free routings are invisible to invariant measures

If the routing is collision-free into `T` on the closed invariant set `Y`, then for `x ∈ Y` the translate `x` itself is
in `Y`, and injectivity with image in `T(x)` gives `N(x) <= 1` and `N(x) = 0` when `1 ∉ T(x)`: `N <= 1_T` on `Y`. For an
invariant probability `μ` on `Y` (extended by zero to `X`), item 1 gives `m μ(M ∩ Y) = E_μ N <= μ(T ∩ Y)`. If `m >= 2`
and `T ⊆ M`, then `2 μ(M) <= m μ(M) <= μ(M)`, so `μ(M) = 0`.

## 3. Full shifts and automaton images

Let `Ψ : C^G → B^G` be a cellular automaton, `X = Ψ(C^G)`, `β` the uniform product measure on `C^G`, `ν = Ψ_* β`.
Since `Ψ` is continuous and equivariant and `β` invariant, `ν` is an invariant probability on `X`. If `U ⊆ X` is open
and nonempty, `Ψ^(-1)(U)` is open and nonempty in `C^G`, so it contains a cylinder and `ν(U) = β(Ψ^(-1) U) > 0`. Thus
a nonempty clopen `M ⊆ X` has `ν(M) > 0`, and item 2 (with `Y = X`) excludes a collision-free routing when `m >= 2`,
`T ⊆ M`. Item 1 gives the quantitative bound
`E_ν[(N-1)_+] + E_ν[N 1_(X∖M)] >= m ν(M) - ν(M) = (m-1) ν(M)`.

*Finite witness.* Let `W` be a finite window with `M`, `T` and every `s_i` determined by `x|_W` (continuity and
compactness give such `W`). Then `N(x)` and `1_T(x)` are determined by `x` on `F = ∪_(d ∈ S) d^(-1) W ∪ W`
(indeed `(d·x)(k) = x(d^(-1) k)`). So the defect event `{N >= 2} ∪ {N >= 1, 1 ∉ T}` is a finite union of cylinders on
`F`; it has positive `ν`-measure, so it is nonempty, and any of its patterns on `F` exhibits a collision or an
escape. For `X = A^G` and `M = [x|_K = P]`, `β(M) = |A|^(-|K|)`, giving the stated density.

## 4. Localization to a measure-free subshift of finite type

Let the routing be collision-free into `T ⊆ M` on the closed invariant `Y ⊆ B^G`, with `M`, `T`, `s_i` given on all of
`B^G` by patterns on `W`, and `F` as in item 3. Choose `R` with `F ⊆ B_R`. Put
`Y_R = {x ∈ B^G : for every g there is y ∈ Y with (g^(-1)·x)|_(B_R) = y|_(B_R)}`, a subshift of finite type containing
`Y`. For `x ∈ Y_R` and any `g`, the local defect data at site `g` — the indegree `N(g^(-1)·x)` and whether
`g ∈ T(x)` — are read from `(g^(-1)·x)|_F`, which equals `y|_F` for some `y ∈ Y`, where there is no defect. Hence
`N <= 1_T` on every translate of every `x ∈ Y_R`, i.e. the routing is collision-free into `T` on `Y_R`. Item 2 gives
`μ(M ∩ Y_R) = 0` for every invariant `μ` on `Y_R`.

Bernoulli: if `β(Y_R) > 0`, then `μ = β(· ∩ Y_R) / β(Y_R)` is an invariant probability on `Y_R` (as `Y_R` is invariant),
so `β(M ∩ Y_R) = 0`; if `β(Y_R) = 0` the same conclusion is trivial.

## 5. Sharpness

*End-pointer SFT over `F_2`.* Alphabet `L = {a, a^(-1), b, b^(-1)}`; `Y` is defined by the edge rules in the target.
Every vertex of the Cayley tree has one outgoing pointer, and each edge `{g, gc}` is oriented exactly one way (if
`x(g) = c` then `gc` does not point back; otherwise `gc` points to `g`). *Nonempty:* fix an end `ξ` and let `x(g)` be
the direction of the neighbour of `g` towards `ξ`; each edge then points towards `ξ` in exactly one direction, and the
rules hold. *Routing:* `M = T = Y`, radius 0, `s_1(x), s_2(x)` the first two letters of `L ∖ {x(1)}` in the order
`a, a^(-1), b, b^(-1)`. For `x ∈ Y` and a letter `c ≠ x(g)`, the site `gc` satisfies `x(gc) = c^(-1)`, so `g` is the
unique neighbour `gc` points to. If `g s_i = h s_j` with `(g, i) ≠ (h, j)`: when `g = h` the letters differ; when
`g ≠ h`, the vertex `k = g s_i = h s_j` points to both `g` and `h`, which is impossible. So the routing is
collision-free, `m = 2`, and by item 2 `Y` has no invariant probability measure. The script checks this rule on
random end-pointer configurations of the radius-7 ball and solves the corresponding SAT instance (SAT).

*Unimodularity.* On the 3-regular tree with a fixed end `ξ` and `Γ = Aut(T, ξ)` (target of
`end-fixing-tree-symmetries-carry-strict-automata`), the children relation is a `Γ`-equivariant collision-free
2-to-1 compression of all vertices into all vertices. Item 1 fails there. Its double count is the discrete
mass-transport principle: the sources of the identity are indexed by `d ∈ S` and moved to the identity by the group
element `d`, and `μ{d·x ∈ E} = μ(E)`. On the vertex set of the non-unimodular `Γ` the corresponding principle holds
only with the modular weight, and the weight is exactly the ratio `2` of children to parents.

*The end-pointer SFT is the tree calibration inside `F_2`.* Remark (not used above): on `Y × A^(F_2)` the map
`(y, x) ↦ (y, x ∘ parent_y)` is a continuous equivariant injective non-surjective map, the end-fixing-tree strict
automaton transplanted to a group. It lives on a measure-free SFT fibre. On a full certificate shift the
corresponding rules are not strict (`certificate-controlled-routing-is-surjunctive`), and item 3 shows the
compression it needs collides.

## 6. Scope

The theorem is about **site** transport: each source is routed to target sites injectively. It does not restrict
maps where one output site combines several input values (for example the Ornstein–Weiss map
`x ↦ (x(g) + x(ga), x(g) + x(gb))` from `{0,1}^(F_2)` onto `({0,1}^2)^(F_2)`, whose only non-injectivity is the constant
fibre). No surjunctivity statement for any class of automata is asserted beyond the routing consequences stated.
The mass-transport principle is standard; compare the discrete instance in `certificate-routing-bernoulli-balance-proof`
and Murphy, *Point-shifts of Point Processes on Topological Groups*, Proposition 2.2(j), arXiv:1704.08333, cited there.
The proof above is self-contained.

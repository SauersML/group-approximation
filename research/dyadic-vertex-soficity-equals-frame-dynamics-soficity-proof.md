---
rg: 2
id: dyadic-vertex-soficity-equals-frame-dynamics-soficity-proof
kind: route
title: Gauge the chart labels or the marks into regular congruence targets, then correct a free product of finite groups over a regular target
target: dyadic-vertex-soficity-equals-frame-dynamics-soficity
requires:
  - twin-deep-vertex-models-give-homogeneous-microstates
  - homogeneous-quotient-soficity-gives-vertex-soficity
  - uniquely-ergodic-action-sofic-iff-topological-microstates
---

Notation: `C_0 = C = <a, y | a^2 = y^3 = 1>` with `a = [[0,-1],[1,0]]` and `y = [[0,-1],[1,1]]`.
`g = diag(1,2)`, `C_1 = gC_0g^(-1) = <a', y'>`, where `a' = [[0,-1/2],[2,0]]` and
`y' = [[0,-1/2],[2,1]]` both lie in `A`. `K`, `K_1` are the stabilizers of the adjacent vertices
`v_0`, `v_1`.

**Correction Lemma.** Let `G = Z/2 * Z/3 = <a,y>`, let `Q` be a finite disjoint union of regular
`G`-sets of a finite quotient group on which `a` and `y` act without fixed points, and let `D` be
the maximal diameter of a piece. Let `G` act exactly on a finite set `V`, and let `ψ : V → Q`
satisfy `ψ(sv) = sψ(v)` for `s ∈ {a, y}` outside `η|V|` points. Then there are a finite
`V' ⊇ V` with `|V' \ V| <= c η|V|`, an exact `G`-action on `V'` that agrees with the old one
outside `c η|V|` points of `V`, and an exactly equivariant `ψ' : V' → Q` extending `ψ` off those
points, where `c = c(|Q|, D)`.

*Proof.* Call `v` *a-good* if `ψ(av) = āψ(v)`. Since `a^2 = 1`, the a-good set is `a`-invariant.
Call `v` *y-good* if its `y`-orbit is a free `3`-cycle along which `ψ` is equivariant. The y-good set
is `y`-invariant. Put `n_q = |ψ^(-1)(q)|`. Good arrows map a fibre injectively into the adjacent
fibre, so adjacent fibres differ by at most the number of bad points in them. Hence within one
piece `n_q` varies by at most `D η|V|`. Pad each piece by new points so that all its fibres have the
common maximum size. This costs at most `|Q| D η|V|` points. In each pair of fibres `q`, `āq`, the
leftover a-bad points and padding points are now equinumerous: match them by an involution. In each
triple `q`, `ȳq`, `ȳ^2q`, match the leftovers by `3`-cycles. ∎

**Relabelling a free torsor (gauge).** If a finite group `Q` acts freely on a set `Λ`, choose one
point in each orbit. Then `Φ(q·λ_orbit rep) = q` defines a `Q`-equivariant map `Λ → Q`.

**1 ⇒ 2.** Fix `R >= 4` and `ε > 0`. Let `E` be the set of type-zero vertices of
`B_(R+1)(v_0) ∪ B_(R+1)(v_1)`, and let `F` contain `a, y, a', y'`, their inverses, and all prefixes
of fixed words expressing a generating set of `Δ_(R−2)` in `(a,y)` and in `(a',y')`. Take a unital
`(F,η)`-multiplicative orbit approximation `(V, σ, π)` with `η` small. Here `π` is the chart map
`v ↦ (π_v : E ↪ ℕ)` of GKP Definition 2.1(3).
* *Exact vertex actions.* The points with `σ(a)^2 v = v` form a `σ(a)`-invariant set; redefine
  `σ(a)` as an involution on the rest. Do the same for `y` with cubes, and for `a'`, `y'`. Call the
  results `ρ_0`, `ρ_1`. They change `O(η)|V|` points. By multiplicativity, the `(a,y)`-word and the
  `(a',y')`-word of each generator of `Δ_(R−2)` agree outside `O_R(η)|V|` points.
* *Gauge.* Let `E_0` be the set of type-zero vertices of `B_R(v_0)` and `Q_0` the image of `K` in
  `Sym(E_0)`. `Q_0` acts freely on injective maps `E_0 → ℕ` by `(qλ)(x) = λ(q^(-1)x)`, so a gauge
  `Φ_0` exists. Put `ψ_0(v) = Φ_0(π_v|E_0)`. `E_0` is `C_0`-invariant. Chart covariance
  `π_(σ(c)v)(x) = π_v(c^(-1)x)` gives `π_(σ(c)v)|E_0 = c̄ · π_v|E_0` on good `v`, so `ψ_0` is almost
  `C_0`-equivariant. `C_0` is dense in `K`, so `Q_0` is a regular `C_0`-set, and `ā`, `ȳ` move
  vertices at distance two, so they are fixed-point free. Symmetrically, `ψ_1` is built from
  `B_R(v_1)`.
* *Correction.* Apply the Correction Lemma to `ρ_0, ψ_0` and to `ρ_1, ψ_1`. Choose the padding
  points with prescribed pairs `(ψ_0, ψ_1)` values, which is possible because both fibre systems have
  the same total size `|Q_0| = |Q_1|` (Atkin--Lehner symmetry). Now `ψ_i` is exactly equivariant,
  so every `ρ_0`-stabilizer lies in `C_0 ∩ Fix_K(E_0)`.
* *Depth.* An element of `K` fixing `E_0` fixes `B_(R−1)(v_0)`. In `SL_2(Z_2)` it is then congruent
  to `λI` modulo `2^(R−1)` with `λ^2 ≡ 1`, so `λ ≡ ±1` modulo `2^(R−2)`, and it lies in
  `Γ(2^(R−2))` in `PSL_2`. Likewise `ρ_1`-stabilizers lie in `Γ_1(2^(R−2))`.
* *Gluing.* It persists up to `O_R(η)` after the changes.

This gives `(TD_(R−2, O_R(η)))`. Letting `η → 0` proves item 2 for every `R >= 2`.

**3 ⇒ 2.** Let `(V, σ, y)` be microstates for `A ↷ L/Λ`. Each `K`-orbit in `L/Λ` is a free
`K`-torsor, because `Λ` is torsion free. Choose base points `y_u`. Then
`ψ_0(v) = (u, kK(2^R))` for `y(v) = k y_u` is a map to `⊔_u K/K(2^R)`, whose left `K(2^R)`-cells are
open. Below their Lebesgue number, `ψ_0(σ(c)v) = c̄ψ_0(v)` for good `v` and `c ∈ {a, y}`. Build
`ψ_1` from `K_1`-orbits in the same way. The correction and depth steps are as above, with
`Γ(2^R)`. The gluing over `B` comes from multiplicativity of `σ`.

**Unique ergodicity.** The equivalence of microstates with p.m.p. soficity in items 3 and 4 is
`uniquely-ergodic-action-sofic-iff-topological-microstates` applied to the dense action. Density is
checked in `homogeneous-quotient-soficity-gives-vertex-soficity-proof`. ∎

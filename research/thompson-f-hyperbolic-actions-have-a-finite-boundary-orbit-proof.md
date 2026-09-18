---
rg: 2
id: thompson-f-hyperbolic-actions-have-a-finite-boundary-orbit-proof
kind: route
title: The DSU classification without free subgroups leaves a boundary orbit of size at most 2, the Busemann pseudocharacter at it dies on F' by a squared swindle, and averaging over the orbit turns boundary amenability into Reiter measures
target: thompson-f-hyperbolic-actions-have-a-finite-boundary-orbit
requires:
  - thompson-f-has-no-free-subgroups
  - thompson-f-quasimorphisms-vanish-on-f-prime
  - busemann-null-isometries-have-no-boundary-contraction
---

**Imported statements.**
- **(DSU)** The statements (D0)–(D11) quoted verbatim from Das–Simmons–Urbański, arXiv:1409.2155v7, in the route
  `cobounded-qi-h2-focal-via-dsu-classification`. They were fetched there on 2026-09-16 and are not re-quoted here.
  Only these are used:
  - (D0): no properness or geodesicity is assumed;
  - (D4): the definitions of `∂X`, `⟨·|·⟩` and `B_ξ`;
  - (D5): the extension of isometries to `bord X`;
  - (D6): `B_ξ(x, g^{-n}x) ≍ n log_b g'(ξ)` for `ξ ∈ Fix(g)`;
  - (D7)–(D10): the classification of isometries and semigroups;
  - (D11): ping-pong for general type.
- **Elementary consequences proved there, in general.** Steps 1, 2 and 4 of that route use only the four-point
  inequality and (D0)–(D7). They do not use the hypothesis "quasi-isometric to `H^2`" or coboundedness, and are
  reused here verbatim:
  - (E'): `|B_ξ(y,w)| ≤ d(y,w) + δ`, and `B_{z_i}(y,w) → B_ξ(y,w)` up to `δ` for `z_i → ξ`;
  - DSU's boundary action agrees with the sequential one;
  - Step 4: if `ξ ∈ Fix(g)` and `L = log_b g'(ξ)`, then `|B_ξ(o, g^n o) + nL| ≤ C_g` for all `n ∈ Z`.
- **(NF)** `thompson-f-has-no-free-subgroups`.
- **(QM)** `thompson-f-quasimorphisms-vanish-on-f-prime`: `F'` is perfect, and the swindle of its route.
- **(BP)** `busemann-null-isometries-have-no-boundary-contraction`(i): for any group `G` of isometries fixing `ξ`,
  `p(k) = lim q(k^n)/n` is a homogeneous quasimorphism, with `q(k) = limsup_i (d(o,z_i) − d(ko,z_i))`.

Let `G ≤ Isom(X)` be the image of `F`, and `π: F → G` the action map. `G` has no non-abelian free subgroup: lift two
free generators, as in the setting paragraph of the DSU route.

**Step 1: the orbit.** `G` is not elliptic, since `F·o` is unbounded.
- **Parabolic.** (D9) gives `ξ ∈ Fix(G)`, and `ξ ∉ X`, since otherwise `d(go, o) ≤ 2d(o, ξ)` for all `g`. Take
  `F_0 = F`.
- **Loxodromic.** By (D10), `G` is lineal, focal or of general type.
  - *General type* gives `Z ∗ Z ≤ G` by (D11) and Step 4, exactly as in Step 7 of the DSU route. This contradicts (NF).
  - *Focal:* `Fix(G) = {ξ}`, and `ξ ∈ ∂X` because `G` contains a loxodromic, which fixes no point of `X` (Step 4).
    Take `F_0 = F`.
  - *Lineal:* let `g ∈ G` be loxodromic with `Fix(g) = {ξ, η} ⊆ ∂X`. For `k ∈ G`, `kgk^{-1}` is loxodromic with
    fixed set `{kξ, kη}`, by the argument in Step 7 of the DSU route (it uses (D7), (D8) and Step 4 only). Lineality
    gives `k{ξ,η} = {ξ,η}`. Put `F_0 := {f ∈ F : π(f)ξ = ξ}`. It is the kernel of the action on the 2-element set
    `{ξ, η}`, so it has index at most 2 and fixes `η` too.
- In every case `F_0 ⊴ F` has index at most 2, `F/F_0` is abelian, and so `F' ≤ F_0`. Also `F·ξ ⊆ {ξ, η}` (or `{ξ}`)
  is fixed pointwise by `F_0`. This is item 1.

(The derivation in Step 4 of the DSU route uses only (D6), the exact antisymmetry `B_ξ(y,z) = −B_ξ(z,y)` of (3.4.7),
and `ξ ∈ Fix(g)`. It does not use that `ξ` is attracting, so it applies to every fixed point.)

**Step 2: the pseudocharacter equals the log-derivative.** Fix `z_i → ξ` and let `p` be as in (BP) for the group
`π(F_0)`, which fixes `ξ`. Put `ℓ := p ∘ π: F_0 → R`, a homogeneous quasimorphism of `F_0`. Let `k ∈ F_0` and
`L_k := log_b π(k)'(ξ)`.
- By definition `q(k^m) = limsup_i (−B_{z_i}(k^m o, o))`, and by (E') this is within `δ` of
  `−B_ξ(k^m o, o) = B_ξ(o, k^m o)`.
- By Step 4, `|B_ξ(o, k^m o) + m L_k| ≤ C_k`. So `|q(k^m) + m L_k| ≤ C_k + δ` for all `m`, and `ℓ(k) = −L_k`.

**Step 3: types inside `F_0`.** For `k ∈ F_0`, `π(k)` is loxodromic iff `L_k ≠ 0`.
- (⇒) `ξ ∈ Fix(π(k))`, and a loxodromic's two fixed points are attracting or repelling by (D7). So `π(k)'(ξ) ≠ 1`.
- (⇐) If `π(k)` were elliptic, `d(o, k^m o)` would be bounded, hence by (E') so would `B_ξ(o, k^m o)`, forcing
  `L_k = 0` by Step 4. If it were parabolic, its unique fixed point in `∂X` would be `ξ` and neutral by (D7), so
  `L_k = 0`. By (D8) it is loxodromic.
- **Elements outside `F_0`** (lineal case only) are never loxodromic: every loxodromic of `G` has fixed set `{ξ, η}`
  by lineality, so it fixes `ξ` and lies in `π(F_0)`. Its preimages lie in `F_0` by the definition of `F_0`.

**Step 4: the squared swindle, `ℓ(F') = 0`.** This is Step 4 of the route of (QM) with `F` replaced by `F_0` and the
pushing element `h` replaced by `h^2`. Let `D` be the defect of `ℓ`.
- `h^2 ∈ F_0`, because `F/F_0` has exponent at most 2. Also `h^2(t) > t` on `(0,1)`, since `h(t) > t` there and `h`
  is increasing. So `h^{2n}(s) → 1` for every `s ∈ (0,1)`.
- (Q1)–(Q4) of that route hold for any homogeneous quasimorphism on any group, in particular for `ℓ` on `F_0`.
- Let `g ∈ F'`. By (QM), `F'` is perfect, so `g = Π_{i=1}^m [x_i, y_i]` with `x_i, y_i ∈ F'`. Every element of `F'`
  has compact support in `(0,1)` (Step 1 of that route), so all supports lie in some `U = [u_0, u_1] ⊂ (0,1)`.
- Choose `M` with `h^{2M}(u_0) > u_1`, and put `τ_j(f) = h^{2Mj} f h^{−2Mj}`. As there, the intervals `h^{2Mj}(U)`
  are pairwise disjoint.
- The elements `τ_j(x_i)`, `τ_j(y_i)` and `τ_j(g)` lie in `F'`, since `F' ⊴ F`, hence in `F_0`. For different `j`
  they have disjoint supports, so they commute.
- So `P_n = τ_0(g) ⋯ τ_{n−1}(g) = Π_i [Π_j τ_j(x_i), Π_j τ_j(y_i)]` is a product of `m` commutators of elements of
  `F_0`.
- Each `τ_j(g)` is conjugate to `g` by `h^{2Mj} ∈ F_0`, so (Q1) inside `F_0` gives `ℓ(τ_j(g)) = ℓ(g)`. Then (Q2)
  gives `ℓ(P_n) = nℓ(g)`, while (Q3) and (Q4) give `|ℓ(P_n)| ≤ (2m−1)D`. Hence `ℓ(g) = 0`.
- `ℓ` is a homomorphism on `F_0`. The "Consequence" paragraph of that route applies verbatim with `F_0` in place of
  `F`: `F' ⊴ F_0` and `F_0/F'` is abelian. So `ℓ` factors through `F_0/F' ≤ Z^2`.

Steps 2–4 give item 2. In particular `k ∈ F'` has `ℓ(k) = 0`, so it is not loxodromic by Step 3.

**Step 5: the collapse (items 3 and 4).** Let `Z` be a compact Hausdorff `F`-space with a finite orbit `O`.
- *Examples.* If `ι: ∂X → Z` is `F`-equivariant, then `O = ι(F·ξ)` has at most 2 points by Step 1. If `∂X` or
  `bord X` is compact, take `ι` to be the identity or the inclusion. No continuity of `ι` is used.
- *Definition used.* `F ↷ Z` is topologically amenable if there are weak*-continuous maps `m_n: Z → Prob(F)` with
  `sup_{z∈Z} ‖g·m_n(z) − m_n(gz)‖₁ → 0` for every `g ∈ F`. Only the values on `O` are used below. So neither
  continuity nor uniformity off `O` is used.
- *(⇐)* If `F` is amenable, take `m_n` constant, equal to a Reiter sequence.
- *(⇒)* Put `ν_n := |O|^{-1} Σ_{z∈O} m_n(z)`. Each `g ∈ F` permutes `O`, so
  `g·ν_n − ν_n = |O|^{-1} Σ_{z∈O} (g·m_n(z) − m_n(gz))` and `‖g·ν_n − ν_n‖₁ ≤ sup_z ‖g·m_n(z) − m_n(gz)‖₁ → 0`.
  So `(ν_n)` is a Reiter sequence, and `F` is amenable by Reiter's criterion.
- *Quantitative form (item 4).* The same identity with a single `m` makes `ν` an `ε`-Reiter measure for `S`,
  supported in `B_r`. From an `ε`-Reiter measure in `B_r`, item 4 of `stein-farley-height-fixes-a-roller-boundary-point`
  proceeds by Namioka's level-set argument and then Moore's tower. ∎

**Where the class dies.** The class consists of every argument that proves amenability or exactness of `F` from an
amenable action on a boundary attached to an unbounded isometric action of `F` on a hyperbolic space. The action may
be topologically amenable, or Zimmer amenable with an atom on `O`. Every member dies at the averaging in Step 5. The
invariant forcing this is the orbit `F·ξ` of size at most 2, which exists by (NF) alone, through (D10)–(D11).

**Remarks.**
1. *Why an orbit and not a fixed point.* In the lineal case `F` may swap `ξ` and `η`. Averaging over the orbit
   replaces the coset push. It gives Reiter measures for `F` itself, with no loss in `ε` or `r`.
2. *Loxodromy factors through `Z^2`.* By Step 3, the set of loxodromic elements of any unbounded action is
   `F_0 \ ker ℓ`, which is a union of cosets of `F'`. So hyperbolic actions of `F` see only the image in `F/F' ≅ Z^2`
   when deciding loxodromy. Every quantitative Følner content of a hyperbolic witness therefore sits in the maps
   `m_n`, not in the loxodromic geometry of `X`.
3. *Where a hyperbolic route could still live.* Only in actions with bounded orbits, or in atomless measure classes on
   `∂X`, as listed in the claim's scope. The latter is automatic for Poisson boundaries and carries no information.

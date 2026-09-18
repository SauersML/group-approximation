---
rg: 2
id: abels-quotient-product-form-model-with-one-singular-point
kind: claim
title: Abels' non-residually-finite quotient A_p/C acts faithfully on the one-point compactification of Q_p^2 x Q_p/Z_p by products of p-adic affine maps off one fixed point, so it is its own germ group there; Hall's B/C sits inside through one coordinate, and neither lies in a rational germ group of V
distinct_from:
  hall-quotient-avoids-v-circle-groups-and-periodic-ends: that excludes V, circle groups and eventually periodic ends for B/C; this constructs a model that survives those exclusions, with the whole centre carried at one point at infinity, and extends it to the finitely presented overgroup A_p/C.
  compact-skew-products-cannot-carry-divisible-fiber-subgroups: that proves no compact base with locally constant cocycles works; this shows a non-compact p-adic base works, and that compactifying it costs exactly one singular point.
  rational-germ-groups-of-germ-extensions-of-v-embed-in-2v: that classifies normal rational germ groups over V as spiral groups; this applies it to show that groups with a torsion monolith, such as B/C and A_p/C, are never among them or their subgroups.
  abels-prufer-quotient-is-fp-sofic-with-fd-invisible-center: that uses the same group A_p/C as a soficity calibration; this gives it a geometric action and a germ model.
artifacts:
  - research/artifacts/gq-bh-bh-solvable-status.md
---

**ESTABLISHED** (lane `bh-solvable`, lane proof, elementary; not independently reviewed; no
priority claimed). Item 5 uses `rational-germ-groups-of-germ-extensions-of-v-embed-in-2v`
(lane proof) and Higman's theorem as quoted in
`hall-quotient-avoids-v-circle-groups-and-periodic-ends`.

## Setting

- `p` is a prime and `R = Z[1/p]`. `A_p` is Abels' group of upper triangular `4×4` matrices
  `g` over `R` with diagonal `(1, p^a, p^b, 1)`, `a, b ∈ Z`. `C = e_14(Z)` is central, and
  `Γ_p = A_p/C` is finitely presented (Abels, as recorded in
  `abels-prufer-quotient-is-fp-sofic-with-fd-invisible-center`, where `Γ_p = A_p/<z(1)>`).
- `E = B/C` is Hall's quotient. It embeds in `Γ_p` through rows and columns `{1,2,4}`:
  `[[1,α,γ],[0,p^k,β],[0,0,1]]` goes to `g` with `g_12 = α`, `g_22 = p^k`, `g_24 = β`,
  `g_14 = γ`, `g_33 = 1`, and the other off-diagonal entries `0`
  (`fg-soluble-minimax-groups-satisfy-boone-higman`, Attempt 2).
- `Y = Q_p × Q_p × (Q_p/Z_p)`, with `Q_p/Z_p` discrete. `Y` is locally compact, second
  countable, totally disconnected, non-compact and has no isolated points. So its one-point
  compactification `X = Y ∪ {∞}` is a Cantor set.

## Statement

1. **The action.** For `g ∈ A_p` and `(x_1, x_2, z) ∈ Y` put

       g·(x_1, x_2, z) = ( (x_1 + g_12)/g_22 ,  g_33 x_2 + g_34 ,
                           z + g_14 + g_13 x_2 − (x_1 + g_12)(g_23 x_2 + g_24)/g_22 ).

   This is an action of `A_p` on `Y` by homeomorphisms, and its kernel is exactly `C`. So
   `Γ_p` acts faithfully on `Y`, and on `X` fixing `∞`.
2. **Product form off ∞.** Every `y ∈ Y` has a compact open neighbourhood
   `B_1 × B_2 × {z_0}` on which `g` acts as `(x_1, x_2, z_0) ↦ (u_1x_1 + v_1, u_2x_2 + v_2, z_0 + r)`,
   with `u_i ∈ p^Z`, `v_i ∈ R` and `r ∈ Q_p/Z_p` constant. The two `p`-adic coordinates are
   transformed independently: no shear between them occurs.
3. **One singular point, and Γ_p is its own germ group.** Every element fixes `∞`, and the germ
   map from `Γ_p` to germs at `∞` is injective. So the germ group at `∞` of `Γ_p ↷ X` is `Γ_p`,
   a finitely presented group. The centre `e_14(R)/C ≅ C_(p^∞)` acts by `z ↦ z + γ`: freely on
   `Y`, and nontrivially near `∞`.
4. **Hall's quotient through one coordinate.** On `E` the action ignores `x_2`:
   `a(α): x_1 ↦ x_1 + α`, `b(β): z ↦ z − βx_1`, `c(γ): z ↦ z + γ`, `t: x_1 ↦ x_1/p`.
5. **Not in rational V-germ groups.** Let `H` be a group in which every nontrivial normal
   subgroup contains a nontrivial element of finite order. Then `H` embeds in the spiral group
   `W = C(C_2, Z) ⋊ V` if and only if it embeds in `V`. `E` satisfies the hypothesis (its monolith
   `<c(1/p)>` has order `p`) and does not embed in `V`. So neither `E` nor `Γ_p ⊇ E` is a subgroup of a germ group at an eventually periodic
   point of a finite germ extension of `V` at which the finite-index or the normal alternative
   of Belk–Hyde–Matucci's germ condition holds.

## Proof

1. **Coset model.** Let `Â` be the matrices of the same shape over `Q_p`, and let
   `K = {k ∈ Â : k_12 = k_34 = 0, k_14 ∈ Z_p}`.
   - `K` is a subgroup: `(kk')_12 = k'_12 + k_12k'_22 = 0`, `(kk')_34 = k_34 + k_33k'_34 = 0`,
     `(kk')_14 = k'_14 + k_12k'_24 + k_13k'_34 + k_14 = k_14 + k'_14`, and the inverse has
     `(1,4)` entry `−k_14`.
   - `gK ↦ (g_12/g_22, g_34, g_14 − g_12g_24/g_22 mod Z_p)` is well defined. For `k ∈ K`, the
     product `gk` has `(1,2)`, `(2,2)`, `(3,4)`, `(1,4)`, `(2,4)` entries
     `g_12k_22`, `g_22k_22`, `g_34`, `g_14 + g_12k_24 + k_14`, `g_22k_24 + g_24`, and the third
     coordinate changes by `k_14 ∈ Z_p`.
   - It is a bijection `Â/K → Y`. With `r = e_12(x_1)e_34(x_2)e_14(z)` one computes that
     `r^{-1}g ∈ K` exactly when `(x_1, x_2, z)` are the coordinates of `gK`.
   - Left multiplication of `h` on `rK` gives the entries `(hr)_12 = x_1 + h_12`,
     `(hr)_22 = h_22`, `(hr)_34 = h_33x_2 + h_34`, `(hr)_14 = z + h_13x_2 + h_14` and
     `(hr)_24 = h_23x_2 + h_24`, hence the formula. So it is an action.
   - The formula is continuous, with continuous inverse given by `h^{-1}`. A homeomorphism of
     a locally compact Hausdorff space extends to its one-point compactification fixing `∞`.
   - **Kernel.** `h` acts trivially iff `h_22 = h_33 = 1`, `h_12 = h_34 = 0`, and
     `h_14 + h_13x_2 − x_1(h_23x_2 + h_24) ∈ Z_p` for all `x_1, x_2 ∈ Q_p`. Setting
     `x_1 = 0` or `x_2 = 0`, and then using both, gives `h_13 = h_24 = h_23 = 0` and
     `h_14 ∈ R ∩ Z_p = Z`. So the kernel is `C`.
2. The shift `s_g(x_1, x_2)` in the third coordinate is a continuous map `Q_p^2 → Q_p`, so its
   class mod `Z_p` is locally constant. On a box where it is constant, take
   `u_1 = 1/g_22`, `v_1 = g_12/g_22`, `u_2 = g_33`, `v_2 = g_34`.
3. **Germ injectivity.**
   - Suppose `g` is the identity off a compact `L ⊆ Y`. The projection of `L` to the discrete
     coordinate is a finite set `F`, so `g` fixes every point with `z ∉ F`.
   - Neither the `x`-coordinates nor the shift depend on `z`. So `g` fixes all `(x_1, x_2)`,
     and `s_g ∈ Z_p` everywhere. As in item 1, `g ∈ C`.
4. Substitute the entries of the embedded matrices into item 1. As a check,
   `a(α)b(β)a(α)^{-1}` sends `z` to `z − βx_1 + αβ`, so `[a(α), b(β)] = c(αβ)`.
5. **Monolith of E.** Let `M = H(R)/C` be the Heisenberg part, and let `1 ≠ N ⊴ E`.
   - If `N ∩ M = 1`, then `[N, M] = 1`. But an element `mt^k` with `k ≠ 0` acts on
     `M/Z(M) ≅ R^2` by `(p^{-k}, p^k) ≠ id`, since `ta(α)t^{-1} = a(α/p)` and
     `tb(β)t^{-1} = b(pβ)`. So `C_E(M) ≤ M`, hence `N ≤ M` and `N = 1`, a contradiction.
   - So `N ∩ M` is a nontrivial normal subgroup of the nilpotent group `M`, and it meets
     `Z(M) = c(R)/C ≅ C_(p^∞)`. Hence it contains the unique subgroup of order `p` of
     `C_(p^∞)`, which is `<c(1/p)>`.

   **The spiral group.** For `H ≤ W`, the subgroup `H ∩ C(C_2, Z)` is normal in `H` and
   torsion-free, so it is trivial, and `H` embeds in `W/C(C_2, Z) = V`.
   - `E` does not embed in `V`, since it contains `a(R) ≅ R`, a non-cyclic subgroup of `Q`
     (Higman). The same holds for `Γ_p ⊇ E`.
   - By item 4 of `rational-germ-groups-of-germ-extensions-of-v-embed-in-2v`, such a germ
     group is virtually cyclic or a subgroup of `W`, and `E` is neither. ∎

## Remarks

- **The shear was an artifact of the linear model.** On row vectors `(1, y_1, y_2, z)` the
  entry `g_23` shears `y_2` by `y_1`, which suggested that `A_p/C` needs a host with sheared
  coordinates (Attempt 2 of the target node, "a connected circle coordinate sheared against
  the base"). In the coset model the shear becomes the bilinear term `−g_23 x_1x_2/g_22` of a
  locally constant cocycle in a discrete fiber. The same construction works when `U` has an
  abelian normal subgroup `H` with `U/H` abelian and the torus acting diagonally on `U/H` with
  one-dimensional weight spaces (here `H = {g_12 = g_34 = 0}`). Take `K` to be `H` with only its
  central coordinate restricted to `Z_p`, times the torus. Then the coset space fibres over
  `(U/H)(Q_p)` with coordinatewise affine base maps and polynomial cocycles.
- **Compact fibre.** Replacing `Q_p/Z_p` by the Cantor circle `F_S`, with the same rotation
  amounts, gives the same statements. Neighbourhoods of `∞` are then complements of
  `L' × F_S` with `L' ⊆ Q_p^2` compact. For `E` this is the `Q_p × F_S` model of Attempt 2.
- **The singular point is forced** for every skew-product model with locally constant cocycles,
  by `compact-skew-products-cannot-carry-divisible-fiber-subgroups`: the base must be
  non-compact, and here one point at infinity suffices.

## What this gives a host, and what is still missing

- **The germ gate passes at ∞.** In any finite germ extension whose germ group at the singular
  point is `Γ_p` acting as above, that germ group is finitely presented. For the base `V` this
  is the necessary condition of `bhm-singfix-condition-forces-fp-germ-groups`. By item 5 the base
  cannot be `V` at rational points in the Corollary 2.10 regime.
- **The base it points to.** The local maps of item 2 are products of two `p`-adic affine
  maps, each a prefix replacement followed by a power of the `p`-adic odometer. So the natural
  base is a Brin–Thompson-type product of two odometer groups (a `p`-ary `2V_τ` with the odometer
  twist in both coordinates), with the discrete coordinate as a finite label set on compact
  pieces.
- **Open gate (host route).** Find such a base `B` on a Cantor set with a dense orbit of points
  whose punctured neighbourhoods are copies of `(Y, product structure)`, with `B` and its
  stabilizers of type `F_∞`, and with the `SingFix` groups of Belk–Hyde–Matucci Theorem 2.1 at
  `n = 2` finitely presented. A finitely presented germ group is necessary for this, not
  sufficient.
- **Open gate (finitary route).**
  - `Γ_p` acts transitively on the dense orbit `Ω = R^2 × Q_p/Z_p`, with every nontrivial
    element of infinite support: a continuous map fixing `Ω` off a finite set fixes a dense
    subset of `Y`, which has no isolated points, so it is the identity.
  - The stabilizer of `(0,0,0)` is `{g_12 = g_34 = 0, g_14 ∈ Z}/C ≅ R^3 ⋊ Z^2`, with torus
    weights `(0,−1), (1,−1), (1,0)` on the entries `13, 23, 24`. It is finitely generated.
  - So by `fp-finitary-permutation-overgroups-are-type-a-actors`, finite presentation of
    `Alt_fin(Ω) ⋊ Γ_p` would put `Γ_p`, and hence `E`, in a finitely presented simple group.
  - The lampshuffler obstruction (`lampshuffler-groups-are-not-fp2-over-q`) needs a free
    action, and this action is not free, so it does not apply. Its `FP_2` status is open.
- **Twisted Brin–Thompson directly.** `Γ_p` has infinite centre, so it has no type (A) action
  of its own (`type-a-actors-have-no-infinite-virtually-central-subgroup`). Any witness must move
  its centre, as the base elements of a germ host do at `∞`.

## Lesson for general BH

Divisible torsion centres, the source of non-residual-finiteness in soluble minimax groups,
live best at a single point at infinity of a non-compact `p`-adic base.
- They are carried by continuous `p`-adic cocycles reduced mod `Z_p`. On a non-compact base
  these cocycles are locally constant. Compactifying the base costs exactly one singular point,
  and the group there is its own germ group.
- The shears of the matrix model are not intrinsic. The coset model trades them for polynomial
  cocycles, so the local maps are products of 1-dimensional odometer-affine maps.
- For these inputs this moves Boone–Higman from "find an exotic host" to one explicit question:
  a product of two odometer Thompson groups with a dense orbit of such points, and finite
  presentation of its point-fixing SingFix groups.
- The same coset trick applies to every unipotent-by-split-torus group with an abelian normal
  subgroup of abelian quotient, which is the shape of Abels' `4×4` group. Larger Abels groups
  `A_n`, `n >= 5`, have longer derived series and need an iterated version.

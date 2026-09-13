# EX review wave 2, part 16: class five of unitary component groups (census priority C, 2026-09-13)

Lane `ex-verify2-analysis`. Verdict legend as in `ex-review2-analysis-2026-09-13.md` §0. Census: part 11.

**Blobs** (rechecked at tip `499e166bb3`; lane ex2-unitary-class-five, one commit each):
- `spin-m-trapping-factors-through-string-bordism` and its route, `5c4be39627`;
- `rank-three-stable-fivefold-commutator-two-primary` and its route, `f02ffb9eb7`;
- `lambda-mod-m-bordism-splits-as-string-bordism-in-a-range` and its route, `e23471c733`;
- `top-cell-commutator-class-is-product-of-adjoint-j-invariants` and its route, `8495b6c044`.

**Prerequisites** from the class-four part 3 artifact (Proposition 7.1, the trapped-class formula, and Theorem 7.3, the
transfer) have PASS in part 1 §1.7.

## 16.1 Verdicts

| claim | verdict |
|---|---|
| `spin-m-trapping-factors-through-string-bordism` | PASS |
| `lambda-mod-m-bordism-splits-as-string-bordism-in-a-range` | PASS |
| `rank-three-stable-fivefold-commutator-two-primary` | PASS, one wording note |
| `top-cell-commutator-class-is-product-of-adjoint-j-invariants` | PASS |

The class-five root stays open. These claims narrow the problem to string bordism, and in rank three to a 2-primary
question about SU(3).

## 16.2 String factorization (`5c4be39627`)

- **The spectra.**
  - `BSpin = Ω^∞τ_{≥4}ko` and `BString = Ω^∞τ_{≥8}ko`, since `π_5`, `π_6` and `π_7` of `BO` vanish.
  - The Postnikov map `τ_{≥4}ko → Σ^4HZ` is an iso on `π_4`, so its `Ω^∞` represents a generator `±λ`, and `λ` is an
    infinite loop map.
  - `bspin_m = fib(τ_{≥4}ko → Σ^4HZ/m)`, and the map of fibres `τ_{≥8}ko → bspin_m` lies over `τ_{≥4}ko`.
  - Thom spectra of infinite loop maps over `BO` give `E_∞` ring maps.
- **Base change.** `MSpin_m ∧ X ≃ MSpin_m ∧_{MString}(MString ∧ X)`. The free extension of a null composite
  `A → B → MString ∧ B` is null.
- **Seeds.**
  - `f = cbar_c∘q∘g'`, and based maps carry reduced classes to reduced classes.
  - Then `[M, f]_red = 0`, and part 1's Proposition 7.1 evaluates the trapped class as a multiple of it.

## 16.3 String bordism in a range (`e23471c733`)

- **Pullback.**
  - `bspin_m` is the pullback of `λ` along `×m: Σ^4HZ → Σ^4HZ`, because `fib(Σ^4HZ → Σ^4HZ/m)` is `×m`.
  - So `ξ_m = ξ_1∘(×m)` for the `MString`-line bundles over `K = K(Z, 4)`.
- **Skeleta.** For a CW pair, the relative Thom spectrum has `MString`-cells in dimensions `> k`. So it is `k`-connected,
  and `π_{n<k}` is unchanged for connective `X`.
- **Finite obstruction layers.**
  - `G_Y = [K^{(k+1)}, BGL_1 MString]` has AHSS layers that are subquotients of `H^j(K; π_{j−1}MString)` for
    `4 ≤ j ≤ k`, at filtration below `k + 1`.
  - For `j ≡ 0 mod 4`, `π_{j−1}MString` is finite, because `MString` is rationally concentrated in degrees `≡ 0 mod 4`.
  - Otherwise `H_j(K; Z)` is finite and `Ext(H_{j−1}K, A)` is finite. Universal coefficients make the layer finite.
- **Nilpotence of `(×q)^*`.**
  - `(×q)^*` is a ring map commuting with Steenrod operations, and it kills `ι` mod `q`, hence all of `H^{>0}(K; F_q)`.
  - Induction over a composition series extends this to finite `q`-groups.
  - The `q`-part of `H^j(K; Z)` is the Bockstein image from `Z/q^b` for large `b`, so the same holds there.
  - Localization at `q` is exact, so nilpotence on layers gives nilpotence on `(G_Y/F^{k+1})_{(q)}`.
- **Choice of `m_k`.**
  - `m_k = Π_{q∈P} q^{a_q}` carries `ξ_1|_Y` into `F^{k+1}`, which vanishes on `K^{(k)}`.
  - Cellular approximations of `×m` compose up to homotopy, and primes `q' ≠ q` preserve `q`-parts.
  - **Check at `k = 4`:** `π_3 MString = Z/24`, with `ξ_1` a generator because `π_3 MSpin = 0`, so `m_4 = 24`.
- **(b), (c).** The splitting is natural in `X`, so it respects the base-point decomposition. The transfer is part 1's
  Theorem 7.3.
- **Flagged standard input:** parametrized Thom spectra and units (ABGHR), with theorem numbers not re-read.

## 16.4 Rank three, stable fivefold commutator (`f02ffb9eb7`)

- **Splittings.**
  - For odd `p`, `SU(3)_{(p)} ≃ S^3 × S^5` (Serre, `p ≥ 3`).
  - This gives the summands `D = {1, 3, 4, 5, 6, 8, 9}` of `Σ^∞U(3)` and `B = {3, 5, 8}` of `Σ^∞SU(3)`.
  - Components compose as products of stems.
- **Letter list at `p = 3`.** Re-derived case by case:
  - flat letters: `α_1` at `d = 3`;
  - `5→3`: `α_1, α_2, β_1, α'_3`;
  - `8→5`: `α_2, α'_3`;
  - `8→3`: `β_1, α'_3, α_1β_1`;
  - rises: `α_1` or `α_2`.
- **Products.**
  - `α_1α_2 = 0`: `α_2` has Adams filtration `≥ 2`, since `Ext^1` lives in stems `0, 3, 11, …`. The 3-part of `π_{10}`
    is `β_1`, in filtration exactly 2.
  - `α_2β_1` and `α'_3β_1` land in stems 17 and 21, which have no 3-part.
  - Odd squares vanish, and `α_1β_1^3 = 0` (Toda).
- **Case count.**
  - Two consecutive drops are impossible, because letters starting at `3` are flat or rise.
  - The only surviving pattern is `± α_1β_1^2·y`, and every base letter `y` of stem `≤ 15` kills it.
  - For `p ≥ 5`, every letter is a multiple of `α_1` in stem `≤ 14`, so `x_4x_3 = 0`.
- **(b).** The commutator is rationally null, because rational Lie groups are homotopy commutative. So `s_5` is torsion
  in a finitely generated group and vanishes at every odd prime, which forces 2-power order.
- **(c).**
  - The commutator factors through `PU(3)`.
  - `s: SU(3) → PU(3)` is a 3-fold cover, hence a 2-local equivalence.
  - `l: S^1 → PU(3)` is 2-locally null, because `π_1 = Z/3`.
  - The Atiyah-dual splitting of the top cell gives `Σ^∞SU(3) ≃ ΣCP^2 ∨ S^8`.

**Wording note.**
- The letter list covers only torsion stems. It omits the **stem-0 letters**, which are degree components in
  `π_0^s ⊗ Z_{(3)} = Z_{(3)}`:
  - `y(3, 5; 8)` and `y(5, 3; 8)` among the rises;
  - base letters with `d_1 + d_0 = b_2`, such as `(1, 4; 5)` and `(4, 4; 8)`.
- They vanish because `s_2` is rationally null, the first sentence of (b). So (a) should invoke that fact before the
  count. The conclusion is unchanged.

## 16.5 Top-cell product formula (`8495b6c044`)

- **Collapse.** The collapse at `1` onto an `Ad(H)`-invariant ball is equivariant and of degree one. The top cell splits
  off by Atiyah duality.
- **Sums.** On a suspension domain, pointwise products are co-H sums and inverses are negatives. Postcomposition with `q`
  is additive.
- **One bracket.**
  - `[g, k] = (Ad_g∘k)·k^{-1}`, so `q∘[g, k] ≃ Ad_g∘(q∘k) − q∘k`.
  - This stabilizes to `J_g·Σ^∞(q∘k)`, and to the exterior product on the reduced domain.
- **Seeds.** `k = [g_1, h]` is trivial on `S^j ∨ Y`, so it factors through `Σ^jY`. The Kronecker pairing is
  multiplicative. `J_g = J_Ad∘Σ^∞g` puts every `x_i` in the ideal `(J_Ad)_*Ẽ_*(H)`. Both `J_Ad` and `β` are rationally
  trivial.
- **Rank-two checks.**
  - `Ad(diag(z, 1))` rotates the off-diagonal line with weight one, which gives `η`.
  - `SU(2) → SO(3)` is an iso on `π_3`, and it stabilizes with index 2. So `J_Ad` on the 3-cell is `2ν`, matching the
    stable Samelson product `⟨ι_3, ι_3⟩ ↦ 2ν`.
  - Three circle letters give `η^3`.
  - `(η, 2ν)^4 = 0`, since `η^4 = 0`, `ην = 0` and `ν^4 = 0`.

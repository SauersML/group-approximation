# K-theory of the capacity-chain resolvent ring R_cap (lane gq-k2-q, 2026-09-18)

Answers to gq-ring-fp-simple's three questions on `capacity-chain-resolvent-ring-has-rational-k0` (38a0d00be).
All computations are by hand, under hypothesis (P) of `resolvent-register-units-give-rational-symbols`: the
Pimsner sequence over the `σ`-closed coefficient ring `B⁺`.

## 0. The state graph and the coefficient ring

Under future semantics (`X(xξ) = σ_x(X)(ξ)`) the letters act on states as follows:

| state | letters and targets |
|---|---|
| `V_k` | `ℓ` loop; `b` loop if `k = 0`; `a -> V_(k−1)`; `d -> U_(m,k)` for every `0 <= m <= k` |
| `U_(m,l)` | `c -> U_(m+1,l)` if `m < l`; `st -> V_(l+1)` if `m = l`; `a_u -> U_(m−1,l−1)` if `m >= 1` |

- `B` is not `σ`-closed: `σ_c(e_Δ) = [Δ=1]`, `σ_st(e_Δ) = [N=1]`, `σ_a(A) = (N+2)^(-1)`.
- The closure `B⁺` contains all point indicators and all resolvents `(N+c)^(-1)`, `(L+c)^(-1)` for `c ∈ Z`, and
  `(Δ−j)^(-1)` for `j >= 0`, each corrected at finitely many states.
- `K_0(B⁺)` is free on:
  - the points `V_k`, `U_(m,l)`;
  - the rows `Z_j = [Δ = j]`;
  - `X = [p_v]` and `Y = [p_u]`.
  This is `LC` of the Stone space consisting of the points, the row ends `r_j` and the corner `∞_u`.
- The polynomial tails are `K_0`-invisible, but not `K_1`-invisible.

## 1. K_0 = coker(1 − [X]) on K_0(B⁺)

**Totals.** `Y = −X − V_0`, `Z_0 = −2V_0`, and each row relation defines `Z_(j+1)`. So `X` survives as a free `Z`
summand, and `[1] = X + Y = −V_0`.

**Point part `C`.** Levels extend one at a time:
`G_l = (G_(l−1) ⊕ Z V_(l+1)) / ((l+1) V_(l+1) = w_l)`, with `w_l = −V_(l−1) − Σ_(j<l) (j+2) U_(j,l−1)`.
- So `C` has rank 1, and `V_0` has infinite order.
- **With `a_u`**, torsion appears.
  - `G_2 = Z g`, with `V_0 = 6g`, `V_2 = 3g`, `V_3 = 7g`, `U_(0,2) = U_(1,2) = g`, `U_(2,2) = 4g`.
  - Then `w_3 = −24g`, so `4 V_4 = −24 g`, and `T = V_4 + V_0` has order exactly `4`. It persists, since each
    extension is injective.
  - Rational values: `v_4 = −1`, `v_5 = 7/30`, `v_6 = 8/9`.
  - Divisibility of `V_0` by every `n` is open.
- **Without `a_u`.**
  - `U_(m,l) = V_(l+1)`, `V_1 = −V_0`, and `(k+1) V_(k+1) = −V_(k−1)`.
  - So `C ≅ (Q ⊕ Z[1/odd]) / Z(1,1)`, which is `Q` plus the divisible torsion `⊕_(p odd) Z/p^∞`.
  - `V_0` is divisible by every `n` ✓ and has infinite order ✓.
  - `K_0 = C ⊕ Z`, the free summand being `Z_0`.

## 2. K_1 and K_2: the register units (the obstruction)

In `K_1(B⁺)` the register units form the lattice `T`. For the variant without `a_u`, with `t` the shift `c ↦ c+1`:

| generator | `D = 1 − [X]` |
|---|---|
| `n_c = [N+c]_v` | `−n_(c+1) − y_c` (from `ℓ`, `a`, `d`) |
| `y_c = [L+c]` on all `u` | `r_(0,c) − n_(c−1)` (from `c`, `st`) |
| `r_(j,c) = [L+c]` on row `j` | `r_(j,c) − r_(j+1,c)` |
| `δ_j = [Δ−j]` at `∞_u` | `δ_j − δ_(j+1) − n_(−j−1)` |

Eliminating leading terms (all with coefficient `±1`) gives `coker(D) ≅ ⊕_(c∈Z) Z n_c ⊕ Z δ_0`, a free group.
- Hence `K_1(R_cap)` has an infinite-rank free quotient.
- `Sym(R_cap)` surjects onto `Q^x ⊗ coker(D)`, through the symbols `{λ, N+c}`. So `E_N(R_cap)` is not finitely
  presented.
- The `(n, y)` block alone is invertible (`det = −t^(−1)`). The row ends are the culprit.

For comparison, `R_L` has `D n_c = n_c − n_(c+1)` for `c >= 1`, so `coker(D) = Z`.

## 3. Rational symbols {λ, μ}

These equal `[1]·{λ,μ}` under `K_0 ⊗ K_2(Q) -> K_2`. They vanish once `[1]` is divisible in `K_0`, as in the
variant without `a_u`.
- Item 5 of `fp-simple-resolvent-ring-with-divisible-unit-class` is too weak as stated. The symbol lemma needs
  every `{λ, x}` with `x ∈ R^x`, and the register units are exactly such `x`.
- `K_1` detection of `Q^x` holds in the variant without `a_u`: `λ ↦ −V_0 ⊗ λ ∈ C ⊗ Q^x` is injective modulo `±1`.

## 4. What a repaired design needs

1. `[1]` divisible and of infinite order in `K_0`. The variant without `a_u` has this; the version with `a_u` is
   unknown and has 4-torsion.
2. `coker(1 − [X]) = 0` on the register-unit lattice (`resolvent-register-units-give-rational-symbols`). Give each
   register type a register-preserving loop, and orient the capacity chain so that the row ends chain towards a
   fed start (row `j -> j−1`) rather than away from one.
3. Positivity (`Δ <= L`) without `a_u`, or with an `a_u` whose `K_0` effect is checked.
4. Prove (P): R is a corner skew Laurent ring over its core, and the Nil terms of the core vanish.

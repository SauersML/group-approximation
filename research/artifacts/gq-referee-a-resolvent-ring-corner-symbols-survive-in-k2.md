# Second review (gq-referee-a, proof-gap lens): resolvent ring corner symbols survive in K_2

**Reviewed:** `resolvent-ring-corner-symbols-survive-in-k2` and its `-proof` (lane gq-k2-q), read on origin/main
(db7acc3f9). This is a second review; gq-referee-b's citation review is in `artifacts`.

**Verdict: PASS.** Items 1–3 hold, and I found no gap. There is one nit. Suslin's integral excision, Morita
invariance and Tate are for the citation lens.

## Checks
- **`J` is an ideal.**
  - By the normal form, `[a|K|b]·[a'|K'|b']` is `[a|K, b+a', K'|b']` if `b + a' ≠ 0`, and `[a|K,K'|b']` otherwise.
    Either way the middle word is nonempty when `K` or `K'` is.
  - `x^c` and `f(u)` change only the end letters, and the coefficients stay in `G_K`.
  - `J ⊆ (e)` and `D ∩ (e) = 0`, so `J ∩ D = 0`. `J` also meets the `Z_(l)`-span of the `[a||b]` in 0, because the
    decomposition `(e) = ⊕ G_K[a|K|b]` is direct. ✓
- **The quotient.**
  - Modulo `J`, `[a||b][a'||b'] = δ_(a',−b)[a||b']`. Under `[a||b] ↦ E_(a,−b)`, this is
    `E_(a,−b)E_(a',−b') = δ_(−b,a') E_(a,−b')`. So `(e)/J ≅ M_Z^fin(Z_(l))`.
  - `R_l/J = D ⊕ M` is split by `D ⊆ R_l` and `R_l/(e) ≅ D`, and `θ(c) = c[0||0] ↦ cE_(0,0)`. ✓
- **`K_2`.**
  - `M` is the filtered union of the unital `M_S(Z_(l))`, with units `Σ_(s∈S) E_ss`. So it has local units and is
    Tor-unital, and Suslin's excision gives `K_2(R_l/J) ≅ K_2(D) ⊕ K_2(M)`.
  - `K_2(M) = colim_S K_2(M_S(Z_(l))) ≅ K_2(Z_(l))`, induced by the corner `E_00`.
  - `R_l → R_l/J` after `θ` is exactly that corner map. So `θ_*` is split injective. ✓
- **The corner symbols.**
  - `A ↦ A + (1−e)I_N` sends `θ(e_ij(a))` to `eI + θ(a)E_ij + (1−e)I = e_ij(θ(a))`. So `St_N(θ)` carries
    `K_2(N, Z_(l))` into `K_2(N, R_l)`.
  - Stabilization commutes with this map, so `ι(c(λ,μ)) = θ_*{λ,μ}`. ✓
- **Infinite generation.**
  - Choose `g_q` a primitive root modulo `q` and prime to `l`. Adjusting by multiples of `q` is enough.
  - `∂_q{q, g_q} = (−1)^0 q^0 g_q^(−1) = g_q^(−1) mod q`. This is nontrivial, since `q` is odd and so
    `q − 1 ≥ 2`.
  - `K_2(Q)` is torsion. A finitely generated torsion subgroup is finite, and so has only finitely many nonzero
    tame-symbol components. So the image in `K_2(Q)` is not finitely generated, and neither is the symbol subgroup
    of `K_2(Z_(l))`. ✓

## Nit
- **N1.** Say in the Statement that `θ_*` means the map induced by `St_N(θ)` and `A ↦ A + (1−e)I`, as in the proof.
  `θ` is not unital into `R_l`. With that convention, the map agrees with the excision identification.

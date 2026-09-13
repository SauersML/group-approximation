# EX review wave 2, part 15: UCT dynamics on O_2 (census priority B, 2026-09-13)

Lane `ex-verify2-analysis`. Verdict legend as in `ex-review2-analysis-2026-09-13.md` §0. Census: part 11.

**Blobs.** Rechecked at tip `28a5bc98ed` against the dump read for this review. Only
`kk-tensor-power-norm-functor-to-kk-zp` had changed (see part 12 §12.5).
- **Lanes:** ex2-uct-z2-strongly-approx-inner, ex2-uct-unit-class-cohomology and ex2-uct-dual-action-transfer.
- **Also reviewed:** the prerequisite `izumi-rokhlin-approximately-representable-duality`, which was established
  without a PASS.

**Sources checked verbatim** on MSI (`/scratch.global/sauer354/ex/ex-verify2-analysis/`):
- **Barlak--Enders--Matui--Szabó--Winter**, arXiv:1312.6289:
  - Corollary 2.2, "A faithful, quasi-free action Z2 y O∞ ... has Rokhlin dimension 1";
  - Theorem 2.3, "Let A be a unital Kirchberg algebra and α : Z2 y A an action. If α is outer, then α has Rokhlin
    dimension at most 1".
- **Gardella--Hirshberg--Santiago**, arXiv:1709.00222: Corollary 3.27, Proposition 3.32 (with the remark that finite
  `dim_Rok` does not suffice), and Definition 3.33. Theorem 3.34 is split by the extraction and was not re-grepped. No
  derivation below uses it.
- **Gabe--Szabó**, arXiv:2205.04933v3: Theorem 5.6, Definition 5.9, Corollary 5.11 and Theorem 5.14.
- **Barlak--Li**, arXiv:1704.04939v2:
  - Definitions 2.6, 2.7 and 4.13;
  - Theorem 2.8, "1) α has the Rokhlin property if and only if αˆ is approximately representable; 2) α is approximately
    representable if and only if αˆ has the Rokhlin property";
  - the proof of Corollary 4.15, "α is approximately representable by [14, Theorem 4.6]", where [14] is Izumi.

## 15.1 Verdicts

| claim | verdict |
|---|---|
| `izumi-rokhlin-approximately-representable-duality` (import) | PASS |
| `bemsw-outer-z2-kirchberg-rokhlin-dimension-at-most-one` (import) | PASS |
| `ghs-z2-commuting-rokhlin-dimension-one-dual-sai` (import) | PASS |
| `gabe-szabo-asymptotic-coboundary-kk-criterion` (import) | PASS |
| `z2-o2-implementing-cocycle-classes-are-path-components` | PASS |
| `z2-odd-commutator-below-half-forces-commuting-towers` | PASS |
| `zp-o2-contractible-crossed-product-only-coboundaries` | PASS |
| `zp-o2-generator-kk-class-is-twisted-asymptotic-innerness` | PASS |
| `o2-central-sequence-k-theory-bi-cyclotomic-transfer` | PASS |
| `z2-o2-actions-anti-inner-and-o3-rokhlin-criterion` | PASS |

No root flips. Detection at `p` stays open, and so does Barlak--Li Remark 4.14(2).

## 15.2 Re-derivations (the load-bearing steps)

**Cocycle classes are components.**
- **Rigidity.**
  - `T(x) = zα(x)z'^*` is an involution, since `zα(z) = 1 = α(z'^*)z'^*`, and `T(xy) = T(x)S(y)` with `S = Ad(z')∘α`.
  - `x_0 = (1 + zz'^*)/2` is `T`-fixed, and invertible when `‖z − z'‖ < 2`.
  - `|x_0|^{-1}` is `S`-fixed, so `v = x_0|x_0|^{-1}` has `T(v) = v`, that is, `z' = v^*zα(v)`.
- **Components.** `U(F)` is connected, because `F` contains a unital `O_2` and `K_1(F) = 0`. A path in `Z` splits into
  steps of length `< 2`.
- **Spectral criteria.** `h = (u + α(u))/2 = u(1 + z_u)/2` intertwines `σ`, so `w = h|h|^{-1}` is a fixed implementer.
- **The odd logarithm.**
  - `exp(iπh) = −1` with `α(h) = −h` forces `sp(h) ⊆ 2Z + 1`.
  - Then `Q = Σ_{k>0} 1_{k}(h)` is a Rokhlin projection. Conversely, a Rokhlin projection gives `h = 2Q − 1`.
- **Item 7, the `K_0` form.**
  - `(zλ)^2 = 1`, and `(1 + zλ)x(1 + z'λ) = (x + T(x))(1 + z'λ)`.
  - So `p_z ~ p_{z'}` iff `Fix(T)` contains a unitary. By Cuntz this is `2[1] = 0` in `K_0(F^α)` when `z = 1`, `z' = −1`.

**The 1/2-threshold.**
- For a tower system, `|a| = f_0 + f_1 = P`, `|b| = 1 − P`, and `a² + b² = P² + (1 − P)² ≥ 1/2`.
- `x^*x = a² + b² + i[a, b]` and `xx^* = a² + b² − i[a, b]`. So `x` is invertible when `‖[a, b]‖ < 1/2`, and `x|x|^{-1}`
  is an odd unitary.
- **Converse.** An odd normal `c = a + ib` gives the commuting system `(a_±)², (b_±)²`.
- **Odd unitary ⟺ `dim^c_Rok ≤ 1`.** Use `f ↦ f(c)` on `C(S¹) → C(sp c)` with GHS 3.27.
- **Odd unitary ⟺ `β̂` strongly approximately inner (SAI).** `Ad(c)` fixes `D` and sends `λ ↦ −λ`.
- **On `O_2`.**
  - `w = u^*λ` commutes with `A` and `λ`, and `α̂(w) = −w`. Conversely an odd `w = yλ` gives an invariant implementer
    `y^*`.
  - SAI of `α̂` gives `dim^c_Rok(α) ≤ 1`, and GHS 3.32 gives Rokhlin. So `2[1] = 0` forces `[1] = 0` for every outer
    `Z/2`-action on `O_2`, whatever the crossed product.

**Only coboundaries (contractible crossed product).**
- **Item 1.** GS 5.14(ii) plus 5.11, with isometric shift absorption from GS 3.15 (PASS in part 3).
- **Item 2.**
  - Theorem 5.6 gives `(φ, w)` with `KK^G(ι_A) ⊗ x = w^♯`.
  - For a coboundary `w_g = vβ_g(v)^*`, the map `φ' = Ad(v^*)∘φ` is equivariant: `w_gβ_g(v) = v`.
  - `T(b) = v^*b` identifies `(B^w, φ, 0)` with `(B, φ', 0)`.
- **Item 3.** `KK^G(C, E) ≅ K_0(O_2 ⋊ G) = 0`. Scalar cocycles `ψ(g)1` then give exact eigen-unitaries.
- **Item 4.** `KK^G(C(G), E) ≅ KK(C, O_2) = 0`.
- **Item 5 (⟸).**
  - `Ad(w_n)(u_g) → ψ̄(g)u_g` with `w_n ∈ B^{α̂} = O_2`, so `α̂` is SAI.
  - `α̂` is outer, since `A' ∩ (A ⋊ G) = C`.
  - Izumi 4.6 on `B ≅ O_2` gives approximate representability, and Barlak--Li 2.8(1) gives Rokhlin for `α`.
- **Item 6.** `(1 − ψ̄) = (1 − ψ)(1 + ⋯ + ψ^{p−2})`, and `ψ̄^♯ = ψ̄·KK^G(ι_S)`. The converse uses `S = (O_2, α)` embedded
  centrally (half-flip node, PASS in part 3).

**Twisted asymptotic innerness.**
- **Item 1.** GS 5.8 compares `(id, ψ)` with `(α_ω, 1)`.
- **Item 4.** `(1 − θ)Φ_p(θ) = 1 − θ^p = 0`, and `1 − ζ` divides `p`.
  - Chinese remainder over `Z[ζ, 1/p]`, with `ζ^j − ζ^k` units, gives the idempotents `e_k`.
  - Each `e_k` is an endomorphism class (item 3 above). Its sequential limit represents `e_kE`, by the flagged standard
    input (IC).
- **Item 7.** `v = [(u_{t_n})]` gives `v^*α_g(v) = χ^k(g)` exactly. That class is trivial iff there is a central
  eigen-unitary, which by item 5 above means Rokhlin.

**Bi-cyclotomic transfer.**
- **Step 0.** Central Cuntz isometries give `[P] = 2[P]`.
- **Step 1.** An eigen-isometry `w = xu_g` of `α̂` has `α_h(x) = x`, `ax = xα_g(a)` and `x^*x = 1`.
- **Step 3.**
  - The corner `j(f) = fe_1` is full.
  - `ve_λ = e_1v` for a `λ̄`-eigen `v`, and `v^*e_1v = e_λ`.
  - So `ρ_λ = Ad(z_λ^*)∘j∘Ad v`, and `k_*i_* = j_*N_φ = 0`.
- **Step 5.**
  - `z = w_0w_0'` is a fixed central isometry, so `p = w_0w_0^*` is full and properly infinite.
  - Cuntz gives `c^*c = p`, `cc^* = 1`, and `w = cw_0` is the required unitary.
- **Item 4.**
  - `Λ/(y − x^k) = Z[ζ_p]`, because `Φ_p(x) | Φ_p(x^k)`.
  - SAI is `𝔭 = (1 − ζ_p) ⊆ Ann[1]`. `𝔭` is maximal, so `Λ[1] ∈ {F_p, 0}`, and Izumi excludes `F_p`.

**Anti-inner and O_3 at p = 2.**
- **Step A.**
  - `ρ(c) = Σ_g s_gα_g(c)s_g^*` factors through `C` with `K_*(C) = 0`.
  - On `F^α`, `ρ = Σ_χ Ad(t_χ)`, where `t_χ = |G|^{-1/2}Σ_gχ(g)s_g` are orthogonal `χ̄`-eigen isometries. So `N_φ = 0`.
- **Step D.**
  - A unital `O_3` gives `[1] = 3[1]`.
  - Conversely `P = Σ_{i≤3} t_it_i^*` has `[P] = [1]`, and Cuntz gives `c`. Then `s_i = ct_i` satisfy `s_i^*s_j = δ_{ij}`
    and `Σ s_is_i^* = cPc^* = 1`.
- **Sign obstruction.** `wv` is invariant and implements `σ` when `v` is an odd central unitary.

## 15.3 Notes

- **(IC) not re-read.** The claim that sequential inductive limits represent homotopy colimits in `KK^G` is flagged as a
  standard input in the twisted-innerness route and was not re-read here.
- **GHS Theorem 3.34** is quoted by `ghs-z2-commuting-rokhlin-dimension-one-dual-sai` but was not re-grepped. The
  downstream derivations use only 3.27 and 3.32.
- **Consequence worth stating** (`z2-odd-commutator-below-half-forces-commuting-towers` item 3(b)): for outer
  `Z/2`-actions on `O_2`, strong approximate innerness of the dual forces the Rokhlin property, with no crossed-product
  hypothesis. Detection at `2` is the implication from odd to even asymptotic innerness, equivalently a unital `O_3` in
  `F^α`.

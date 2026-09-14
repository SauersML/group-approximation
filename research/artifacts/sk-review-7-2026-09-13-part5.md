# SK review 7, part 5: separable factors hold countably many subshift groups (sk-strong-7)

Lane `sk-verify-7`, 2026-09-13 ~21:40 CDT. Queue entries 58–59. I re-derived every step before reading the owner's justifications.

## 0. Verdicts

| Claim (owner) | Verdict |
|---|---|
| `kazhdan-simple-quotients-countable-in-separable-factors` + route (sk-strong-7) | PASS |
| `separable-factors-hold-countably-many-subshift-groups` + route (sk-strong-7) | PASS |

No FAIL, no GAP.

## 1. Ozawa's argument in general form
- **Step 0.**
  - A κ-Kazhdan pair `(E,κ)` means that every representation without invariant vectors moves some unit vector by `≥ κ` at some `s ∈ E`.
  - Split `ξ = Pξ + ζ`, with `ζ` in the complement of the invariant vectors. Then `π(s)ξ − ξ = π(s)ζ − ζ`, so `‖ζ‖ ≤ κ^{-1}max_s‖π(s)ξ − ξ‖`.
  - Checked.
- **Step 1.**
  - `ker u_i = N_i`, and `Λ/N_i` is nontrivial, so some `‖u_i(s) − 1‖_2 > 0` (the trace is faithful).
  - A countable union over `1/n` gives an uncountable `I_1` with a uniform `δ`.
  - Checked.
- **Step 2.** `L²(M)^E` is separable metric. Uncountably many indices give points inside one ball of radius `ε/2`, so there are `i ≠ j` at distance `< ε`. Checked.
- **Step 3.**
  - `Ju_j(s)J ∈ M′` commutes with every `u_i(t)`, so `s ↦ u_i(s)Ju_j(s)J` is a homomorphism.
  - `π(s)1̂ = (u_i(s)u_j(s)^*)^`, and right multiplication is isometric, so `‖π(s)1̂ − 1̂‖ = ‖u_i(s) − u_j(s)‖_2 < ε` on `E`.
  - `η = P1̂` has `‖1̂ − η‖ < ε/κ`.
  - Checked.
- **Step 4.**
  - The stabilizer of `η` under `u_i` contains `N_i`.
  - It also contains `N_j`, since `π(s) = u_i(s)` for `s ∈ N_j`.
  - Simple quotients make `N_i`, `N_j` distinct maximal normal subgroups, so `N_iN_j = Λ`.
  - Checked.
- **Step 5.** `‖u_i(s)1̂ − 1̂‖ ≤ ‖u_i(s)(1̂ − η)‖ + ‖η − 1̂‖ < 2ε/κ < δ` for all `s`, which contradicts the choice of `I_1`. Checked.
- **Consequences.**
  - A non-unital embedding `ψ` of `L(Λ/N_j)` gives `λ_g ↦ ψ(λ_g) + 1 − ψ(1)`, injective on `Λ/N_j`.
  - `L(Λ/N_i)` is separable, so an isomorphism class contains countably many `j`.
  - Checked.

## 2. The subshift family
- **One Kazhdan group.**
  - `π_X: F_q⟨t_±, t_a⟩ → R_X` is onto, because `u^{±1}` and the letter indicators generate `R_X`.
  - So `EL_3(F) → EL_3(R_X)` is onto, and `EL_3(F)` has (T) by EJZ for the finitely generated ring. A primitive element is added when `q` is not prime.
  - Checked.
- **Distinct kernels.**
  - Take `v ∈ L(X) ∖ L(Y)`. Then `π_Z(∏_t t_-^t t_{v_t} t_+^t) = ∏_t u^{-t}e_{v_t}u^t = e_{[v]}`, using `u^{-t}e_au^t = e_{[x_t=a]}`.
  - In `R_Y` it is `0`, so the element `e_12(c_v) ∈ Λ` maps to `I` in `S_Y`.
  - In `R_X` it is nonzero. Compare the `(1,1)` entries `1 + r` of `e_12(r)e_21(1) = I + rE_12 + E_21 + rE_11` and `1` of `e_21(1)e_12(r) = I + E_21 + rE_12 + rE_22`: `e_12(r)` is central only if `r = 0`. So the image in `S_X` is nontrivial.
  - So `N_X ≠ N_Y`.
  - Checked.
- **Items 2 and 3.**
  - The `L(G_X)` are (T) factors inside `R^ω`: infinite simple implies ICC, then Connes–Jones, and hyperlinearity from LEF. This is the PASS node `simple-kazhdan-group-gives-property-t-factor-in-r-omega`.
  - There are continuum many infinite minimal binary subshifts (reviewed node), and countable fibres give continuum many classes.
  - A separable universal factor would contain every `G_X` in its unitary group.
  - Checked.
- **Scope.**
  - Distinct kernels hold for any two distinct subshifts, minimal or not.
  - Simplicity (for `N_iN_j = Λ`) is used only for minimal infinite `X`, as stated.
  - The NPS07 credit for the general non-universality is correctly recorded as cited through Peterson; the primary was not read.

## 3. For the note (main's call)
- The note can say that `X ↦ L(G_X)` has countable fibres, so the R^ω-embeddable (T) factors `L(G_X)` realize continuum many isomorphism classes.
- This is one sentence with the Ozawa 2004 (PAMS) citation. It upgrades the group count to a count of factors, and it gives hyperlinear instances of the setting in which Ozawa printed the wish to know whether his quotients embed in `U(R^ω)`.
- The mathematics above is sound. Novelty is bounded by the owner's search.

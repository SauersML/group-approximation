---
rg: 2
id: sl4z-odd-central-sector-bott-proof
kind: route
title: Proof that the block-swap torus Bott indices of SL_4(Z) vanish in the even central sector and are antisymmetric in the odd one
target: sl4z-delocalized-bott-lives-in-odd-central-sector
requires:
  - sl4z-involution-centralizers-have-rational-h2
artifacts:
  - research/artifacts/laurent-sl4-delocalized-bott-2026-09-16.md
---

Lane proof. It uses the Bott-index facts (B1)–(B5), `pol`, Lemmas 1.1–1.3 and Lemma 4.1 of
the artifact, cited by number. From `sl4z-involution-centralizers-have-rational-h2` it uses
the relations `hgh^{-1} = cg`, `hM_1h^{-1} = M_2`, `hM_2h^{-1} = M_1`, and the facts that `g`, `c`
are central in `Δ` and commute with `M_1`, `M_2`. Write `φ = φ_n`, and `x ≈ y` for
`‖x − y‖ → 0`.

**Step 0 (almost projections).** Let `D ≤ G` be a finite abelian group, `χ` a character, and
`a_χ = |D|^{-1} Σ_{f ∈ D} \bar χ(f) φ(f)`. For `D = F` the characters are real, which gives the
formula in the Setting.
- `φ(1) ≈ 1` (artifact §1), `φ(f)φ(f') ≈ φ(ff')` and `φ(f^{-1}) ≈ φ(f)^*`.
- Hence `a_χ^* ≈ a_χ`, and by character orthogonality `a_χ a_{χ'} ≈ δ_{χχ'} a_χ`. In detail,
  `a_χ a_{χ'} ≈ |D|^{-2} Σ_e φ(e) \bar χ'(e) Σ_f (\bar χ χ')(f)`.
- `Σ_χ a_χ = φ(1) ≈ 1`.
- If `s ∈ Z_G(D)`, then `φ(s)φ(f)φ(s)^* ≈ φ(sfs^{-1}) = φ(f)`, so `‖[a_χ, φ(s)]‖ → 0`.

Put `b_χ = (a_χ + a_χ^*)/2`. Then `‖b_χ^2 − b_χ‖ → 0`, so for large `n` the spectrum of `b_χ` lies
within `o(1)` of `{0, 1}`. So `Q_χ = 1_{[1/2, ∞)}(b_χ)` is a continuous function of `b_χ` on its
spectrum, and `‖Q_χ − b_χ‖ → 0`. Consequences:
- `Q_χ Q_{χ'} ≈ 0` for `χ ≠ χ'`;
- `Σ_χ Q_χ ≈ 1`;
- `‖[Q_χ, φ(s)]‖ → 0` for `s ∈ Z_G(D)`.

**Step 1 (part 1).**
- `M_1, M_2 ∈ Z_G(F)` commute. So the compressions `Qφ(M_i)Q` are almost unitary and almost
  commute on `Q C^{k_n}`, exactly as in the artifact's Definition of `β_ω`. So `β_{ε,δ}` is
  defined for large `n`.
- **Homomorphisms.** If `φ = π` is a homomorphism, then `a_χ` is the exact isotypic
  projection of `π|_F`, it commutes with `π(M_i)`, and `Q_χ = a_χ`. The compressions commute
  exactly, and (B1) gives `0`.
- **Perturbation.** If `‖φ(y) − ψ(y)‖ → 0` for `y ∈ F ∪ {M_1, M_2}`, then `‖a_χ(φ) − a_χ(ψ)‖ → 0`,
  and hence `‖Q_χ(φ) − Q_χ(ψ)‖ → 0`. The intertwiner `W` of Lemma 1.3, with (B2) and (B3),
  gives equality.
- **Direct sums.** `a_χ(φ ⊕ ψ) = a_χ(φ) ⊕ a_χ(ψ)`, so the same holds for `Q_χ`, and (B3)
  applies.
- The last sentence of part 1 is the argument of the artifact's Corollary 1.4 with this
  invariant in place of `β_ω`.

**Step 2 (conjugation formula).** Let `w ∈ G` normalize `F` and put `W = φ(w)`. Then
`Wφ(f)W^* ≈ φ(wfw^{-1})`, so `W a_χ W^* ≈ a_{χ^w}` with `χ^w(f) = χ(w^{-1} f w)`. Hence
`W Q_χ W^* ≈ Q_{χ^w}`.

By simultaneous unitary conjugation (B3), then the perturbation argument of Step 1:
`β_χ(φ; M_1, M_2) = β_{χ^w}(φ; wM_1w^{-1}, wM_2w^{-1})`.

Here `β_χ(φ; s_1, s_2)` denotes the invariant built from a commuting pair `s_1, s_2 ∈ Z_G(F)`.

(Continuity of `Q_χ` in `b_χ`. Fix a continuous `u : R → [0, 1]` with `u = 0` on `(−∞, 1/4]`
and `u = 1` on `[3/4, ∞)`. For large `n`, `Q_χ = u(b_χ)`. Approximating `u` uniformly on `[−2, 2]`
by polynomials gives, as in Lemma 1.1, `‖u(x) − u(y)‖ ≤ 2η + C_η‖x − y‖` for self-adjoint
`x, y` of norm at most 2, and `‖[u(x), z]‖ ≤ 2η‖z‖ + C_η‖[x, z]‖`. This is used implicitly
in every `≈` involving `Q`.)

**Step 3 (parts 2 and 3).** Take `w = h`, which is an involution.
- `h^{-1} g h = cg` and `h^{-1} c h = c`, so `χ_{ε,δ}^h = χ_{εδ,δ}`.
- `hM_1h^{-1} = M_2` and `hM_2h^{-1} = M_1`.
- By Step 2 and (B4):
  `β_{ε,δ}(M_1, M_2) = β_{εδ,δ}(M_2, M_1) = −β_{εδ,δ}(M_1, M_2)`.
- For `δ = +1` this reads `β_{ε,+} = −β_{ε,+}`, so `β_{ε,+} = 0`. For `δ = −1` it reads
  `β_{+,−} = −β_{−,−}`.

**Step 4 (part 4, refinement).** Take `D' = ⟨g⟩ ≤ F` and `ω = ±1`.
- By orthogonality, `a_ω(D') = ½(φ(1) + ωφ(g)) = a_{ω,+} + a_{ω,−}` exactly.
- `φ(g)^2 ≈ 1`, and `φ(g)` is unitary, so its spectrum lies near `{±1}`. Hence
  `½(1 + ωφ(g)) ≈ P_ω`, the artifact's spectral projection of `φ(g)` near `ω`.
- By Step 0, `Q_{ω,+}Q_{ω,−} ≈ 0`, and `Q_{ω,+} + Q_{ω,−} ≈ P_ω`.
- Replace `Q_{ω,−}` by `Q'` := the spectral projection near `1` of
  `(1 − Q_{ω,+})Q_{ω,−}(1 − Q_{ω,+})`. Then `Q' ⊥ Q_{ω,+}` and `Q' ≈ Q_{ω,−}`.
- So `R = Q_{ω,+} + Q'` is a projection with `R ≈ P_ω`. Both summands almost commute with
  `φ(M_i)`.
- By the intertwiner of Lemma 1.3, `β_ω(φ; g, M_1, M_2)` is the Bott index of the compressions to
  `R`. Those are within `o(1)` of the block-diagonal sums of the compressions to `Q_{ω,+}` and
  to `Q'`.
- By (B2), (B3) and Step 1's perturbation argument, it equals `β_{ω,+} + β_{ω,−}`. The same
  argument with `D' = ⟨c⟩` gives the statement for `c`.
- With Step 3: `β_{+1}(g) = β_{+,−}` and `β_{−1}(g) = β_{−,−} = −β_{+1}(g)`, while
  `β_δ(c) = β_{+,δ} + β_{−,δ}` is `0` for both `δ`.

**Step 5 (part 5, induced models).**
- `g` has order 2 and `g ∉ N`, so `⟨g⟩ ∩ N = 1`, and artifact Lemma 4.1 applies to
  `(g, M_1, M_2)`. It gives `β_{+1}(g) = β_{−1}(g)` for `Ind ψ_n`.
- With Step 4, `β_{+1}(g) = −β_{−1}(g)`, so both vanish.
- So `β_{+,−} = β_{+1}(g) = 0` and `β_{−,−} = 0`, and by Step 3 all four `β_{ε,δ}` vanish.
- Genuine summands contribute `0` (Step 1), and `β` is additive.
- Torsion-free congruence subgroups such as `Γ(3) = ker(SL_4(Z) → SL_4(Z/3))` are normal, of
  finite index, and do not contain `g`.

**Step 6 (part 6, realization on the normalizer).**
- `N_G(F)`: an element normalizing `F` fixes the central `c` and sends `g` to a conjugate of
  `g` in `F`, i.e. to `g` or `cg`. So `N_G(F) = {M : MgM^{-1} = ±g} = Δ ⊔ hΔ = Δ'`, as in Step 6
  of `sl4z-involution-centralizers-rational-h2-proof`.
- `Γ(2) = {±I} × ⟨a, b⟩`. `Γ(2)/{±I}` is free on the images of `a, b`, so `ā ↦ a`, `b̄ ↦ b`
  defines a section homomorphism. Its image `⟨a, b⟩` meets the central `{±I}` trivially and,
  with it, generates `Γ(2)`.
- Let `α : Γ(2) → Z` be the homomorphism with `a ↦ 1`, `b ↦ 0`, `−I ↦ 0`. Let
  `σ : Γ(2) → {±1}` be the homomorphism with `σ(−I) = −1`, `σ(a) = σ(b) = 1`.
- Take the clock and shift pair `(U_n, V_n)` of (B5), with `Bott(U_n, V_n) = 1` and
  `U_nV_n = λ_n V_nU_n` exactly, where `|λ_n| = 1` and `λ_n → 1`.
- On `N = Γ(2) × Γ(2)` put `ψ_n(X, Y) = σ(X) U_n^{α(X)} V_n^{α(Y)}`. For fixed arguments,
  `U^iV^jU^{i'}V^{j'} = λ^{-ji'} U^{i+i'}V^{j+j'}`, so `ψ_n` is an asymptotic homomorphism.
  - `ψ_n(c) = ψ_n(−I, −I) = −1`, `ψ_n(g) = ψ_n(I, −I) = 1` and `ψ_n(cg) = −1`, exactly.
- Let `Θ_n = Ind_N^{Δ'} ψ_n`, with representatives `t` of `Δ'/N` (24 cosets).
  - `g, c` are central in `Δ` and normalized by `h`, so `Θ_n(g)`, `Θ_n(c)` are exactly diagonal
    with the signs `ψ_n(t^{-1} g t) ∈ {ψ_n(g), ψ_n(cg)}` and `ψ_n(c) = −1`.
  - So each block lies in sector `(+, −)` (when `t ∈ Δ`) or `(−, −)` (when `t ∈ hΔ`). The
    projections `a_χ` are exact, and `Q_{ε,+} = 0`.
- **Sector `(+,−)`.** The blocks are `t = (X, Y) ∈ Δ`. There
  - `Θ(M_1)` has block `ψ(X^{-1}xX, 1) = ± U^{m_t}`, with `m_t = α(X^{-1}xX)`;
  - `Θ(M_2)` has block `V^{α(Y^{-1}xY)}`;
  - `α(Y^{-1}xY) = m_t`, because `α` factors through `H_1(Γ(2); Q)` and `ρ(Y) = ρ(X)` (Step 3 of
    the centralizer proof).
- From `U^mV^m = λ^{m^2} V^mU^m`, the commutator is scalar, and `Bott(±U^m, V^m) = m^2 Bott(U, V)`
  for large `n`. So `β_{+,−}(Θ_n) = Σ_{t ∈ Δ/N} m_t^2 ≥ m_1^2 = 1`.
- **Sector `(−,−)`.** Here the blocks are those at `t = h t_0`. They are the blocks of the
  `(+,−)` sector with `M_1` and `M_2` exchanged. So by (B4), `β_{−,−}(Θ_n) = −β_{+,−}(Θ_n)`.
- This is consistent with part 3, which applies verbatim to `Δ'` since `h ∈ Δ'`.
- `Δ'` has infinite index in `SL_4(Z)`, so finite-dimensional induction to `G` is unavailable.
  The extension problem is `sl4z-odd-central-sector-bott-is-realizable`. ∎

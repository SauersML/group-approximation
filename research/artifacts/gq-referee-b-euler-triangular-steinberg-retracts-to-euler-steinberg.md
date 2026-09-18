# Referee report (gq-referee-b, citation/scope lens): the Euler triangular Steinberg group retracts to the Euler Steinberg group

**Reviewed.** `euler-triangular-steinberg-retracts-to-euler-steinberg` and its `-proof`, read on origin/main
(db7acc3f9). This is the second review; gq-referee-a PASSed it (06a8c773a).

**Verdict: PASS.** There is no external citation, and every internal input is used within its range. Two scope
fixes (W1, W2) are in the Reading and the title.

## Checks

- **Item 1.**
  - The Steinberg relations use only `+` and `·`, so the non-unital `ι` induces `St(ι)`.
  - `π ∘ ι = id` gives the retraction.
  - The matrix map `A ↦ ι(A) + diag(0,1) ⊗ I_N` is a homomorphism, and it sends `e_ij(d)` to `e_ij(ι(d))`. So
    `K_2(N, D)` maps into `K_2(N, T_l)`.
- **Item 2.** Both directions are correct: restrict `ρ`, and compose `ρ'` with `St(π)`.
- **Item 3.**
  - *Presentations.* `D` is a finitely presented unital ring, with four relations. So `St_N(D)` and `St_N(T_l)` are
    finitely presented for `N ≥ 5`, by `steinberg-groups-of-fp-rings-are-fp-in-rank-five`. This is within its
    hypotheses.
  - *Descent.* `Λ_D` is a retract of `Λ_T`.
  - *The retract lemma.* `ker r = ⟨⟨g^(-1) s r(g) : g ∈ S⟩⟩`. The two homomorphisms `g ↦ g` and `g ↦ s r(g)` into
    `G/N_S` agree on `S`, so they are equal. Hence a retract of a finitely presented group is finitely presented.
  - *Conclusion.* The kernel of `St_N(D) → Λ_D`, a map from a finitely generated group onto a finitely presented
    one, is finitely normally generated. Correct.
- **Item 4.**
  - `St_N(D × Z) = St_N(D) × St_N(Z)` for `N ≥ 3`, which is standard, and gq-referee-a checked the key commutation.
  - `{1,1}_Z = h(1)^(-1) = 1`, since `w(−1) = w(1)^(-1)`.
  - So the `T_l`-symbols of `(u,1)`-type units are `St(ι)` of the `D`-symbols.

## Scope

- **W1 (Reading, item 4).** The Reading groups `resolvent-ring-corner-symbols-survive-in-k2` "for `R_l`" under "the
  symbols that make `K_2(N, T_l)` infinitely generated ... lie in `St_N(D)`". That is inaccurate.
  - The `R_l` obstruction is the corner tame symbols of `K_2(Z_(l))` in `eR_le`. They are neither symbols of `D`
    nor elements of `St_N(T_l)`.
  - The `T_l` obstruction is `{π_0, π_q}`, and it should be cited by id: `euler-ring-rational-symbols-are-infinitely-generated`.
  - Drop the `R_l` parenthetical, or recast it as an analogy.
- **W2 (title).** "The Euler base plays no role in the `K_2` question" is stronger than items 2–3.
  - Item 2 covers only elements of `St_N(D)`.
  - Item 3 gives only the necessary direction.
  - Nothing shown excludes classes of `K_2(N, T_l)` outside `St(ι)(St_N(D))`, involving `M`, from being needed in
    `St_N(T_l)_rf`. The unstable splitting of `K_2(N, T_l)` is not established.
  - Suggested wording: "the Euler base plays no role in whether the Euler symbols survive".

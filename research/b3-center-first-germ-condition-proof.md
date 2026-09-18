---
rg: 2
id: b3-center-first-germ-condition-proof
kind: route
title: Proof of thinness, the germ-condition failure for the Deligne language, and the central-letter repair for B_3
target: b3-center-first-normal-form-passes-the-germ-condition
requires:
  - prefix-replacement-actions-recode-into-germ-extensions-of-v
artifacts:
  - research/artifacts/gq-bh-bh-free-51-garside-and-mosher-thinness.md
---

Notation as in the claim. Write `a, b` for the two atoms in either order, so that
`aba = bab = Δ`, and let `τ(g) = Δ g Δ^{-1}`, which swaps `σ_1 ↔ σ_2` and satisfies `τ^2 = id`.

## 1. The local rule

Let `a` be an atom and `x_1 x_2 ⋯` an infinite chain of proper simples. By the criterion
`x → y ⟺ y` begins with the last letter of `x`, the normal form of `a x_1 x_2 ⋯` is:
- (i) `a x_1 x_2 ⋯` if `x_1 ∈ {a, ab}`;
- (ii) `(ab) x_2 x_3 ⋯` if `x_1 = b`;
- (iii) `Δ · x_2 x_3 ⋯` if `x_1 = ba`, since `a·ba = Δ`.

In each case the new first block ends in a letter with the same finishing set as the letter it
replaces, or is followed by the unchanged `x_2`. The same computation on finite prefixes gives
the finite normal forms, so these are the boundary values.

## 2. Thinness (item 1)

- **L_Δ.** We have `σ_1 Δ^k = Δ^k τ^k(σ_1)` and `τ^k(σ_1)` is an atom.
  - *Finite `k`.* On `Δ^k x_1 x_2 ⋯`, `σ_1` applies §1 to `τ^k(σ_1)` after the prefix `Δ^k`.
    In case (iii) this raises `k` by one; for `k < 0` it deletes one `Δ^{-1}`. Each case is a
    state-preserving prefix replacement on the cylinder of the first `|k| + 2` letters.
  - *At `Δ^{±∞}`.* Both points are fixed. A prefix replacement fixing `Δ^{+∞}` near it has the
    form `Δ^K w ↦ Δ^{K'} w`.
    - For even `K`, `σ_1(Δ^K σ_2^∞) = Δ^K (σ_1σ_2) σ_2^∞`, by (ii) with `a = σ_1`.
    - That is not `Δ^{K'} σ_2^∞`. So `σ_1` is singular at `Δ^{+∞}`, and likewise at
      `Δ^{-∞}` and for `σ_2`.
  - `Δ` acts by `Δ^k ↦ Δ^{k+1}`, a state-preserving prefix replacement everywhere.
- **L_z.** Since `z` is central, `σ_1 · z^k Δ^ε w = z^k · (Δ^ε τ^ε(σ_1) w)`. Then apply §1.
  - In case (iii) `Δ^ε Δ` becomes `Δ`, or `z` when `ε = 1`, so `k` rises by one.
  - Hence `σ_1` is a state-preserving prefix replacement near every point other than `z^{±∞}`.
  - At `z^{+∞}`, the test point `z^K σ_2^∞` (`ε = 0`) goes to `z^K (σ_1σ_2) σ_2^∞`. That is not
    a `z`-shift, so `σ_1` is singular there. The same holds for `σ_2`, and for `Δ`, which sends
    `z^K x_1 ⋯` to `z^K Δ x_1 ⋯`.
  - `z` acts by `z^k ↦ z^{k+1}` everywhere.
- **Faithfulness.**
  - Let `g ≠ 1` have normal form `π y_1 ⋯ y_m`, with `π` its `Δ`-block or its `z^k Δ^ε` block.
  - Choose an infinite chain `η` that is not eventually periodic, with `y_m → η_1` when
    `m ≥ 1`.
  - Then `g η = π y_1 ⋯ y_m η` is a valid infinite normal form.
  - It is not `η`: either `π` is nonempty, or `m ≥ 1` and `η` would be periodic. ∎

## 3. Germs at the singular points

**Lemma.** Let `p` be `Δ^{+∞}` (for `L_Δ`) or `z^{+∞}` (for `L_z`), and let `g ∈ B_3` be the
identity on a neighbourhood `U` of `p`. Then `g = 1`.

*Proof.*
- For any point `ζ` other than the opposite pole, `z^m ζ → p` as `m → ∞`, since `z = Δ^2`
  raises the leading block. So `z^m ζ ∈ U` for some `m`.
- `g` commutes with `z`, so `z^m g ζ = g z^m ζ = z^m ζ`, hence `g ζ = ζ`.
- So `g` fixes a dense set, hence everything. By faithfulness `g = 1`. ∎

So the germ map `γ` at `p` is injective on `B_3`.

**The comparison map.** Let `ρ : B_3 → SL_2(Z)` send `σ_1 ↦ [[1,1],[0,1]]` and
`σ_2 ↦ [[1,0],[-1,1]]`. The braid relation holds, and `ρ(Δ) = [[0,1],[-1,0]] =: J`, of order 4.

## 4. Failure for L_Δ (item 2)

- **(a) Non-normality.**
  - We have `σ_1 Δ σ_1^{-1} = Δ σ_2 σ_1^{-1}`.
  - If `γ(σ_1Δσ_1^{-1}) = γ(Δ^e)` for some `e`, the Lemma gives `σ_2σ_1^{-1} = Δ^{e-1}`.
  - Applying `ρ`: `[[1,-1],[-1,2]]` has trace 3, while every power of `J` has trace in
    `{2, 0, −2}`. Contradiction.
  - So `γ(⟨Δ⟩)` is not normal in `γ(B_3)`.
- **(b) Infinite index.**
  - If `γ(σ_1^d) = γ(Δ^e)`, the Lemma gives `σ_1^d = Δ^e`.
  - So `[[1,d],[0,1]] = J^e`, forcing `d = 0`.
  - Hence the cosets `γ(σ_1^d)γ(⟨Δ⟩)`, `d ∈ Z`, are distinct.
- **(c) Every recoding.**
  - Near `p`, `Δ` is the state-preserving shift `Δ^k ↦ Δ^{k+1}`, so `γ(Δ) ∈ (V)_p ≅ Z`. Write
    `γ(Δ) = r^j` for a generator `r` of `(V)_p` and some `j ≠ 0`.
  - *Normality fails.* If `(V)_p` were normal in `(Γ)_p ⊇ γ(B_3)`, then
    `γ(σ_1) r γ(σ_1)^{-1} = r^{±1}`. Raising to the `j`-th power gives
    `γ(σ_1Δσ_1^{-1}) = γ(Δ^{±1})`, contradicting (a).
  - *Finite index fails.* If the index were finite, then `γ(σ_1)^d ∈ (V)_p` for some
    `d ≥ 1`, say `γ(σ_1)^d = r^i`. Then `γ(σ_1^{dj}) = γ(Δ^i)`, contradicting (b). ∎

## 5. Success for L_z (item 3)

- **Hypotheses of the recoding claim.**
  - The follower-set graph of `L_z` has these vertices: start, after `z^k` (`k > 0`), after
    `z^{-k}`, after `Δ`, and after a proper simple ending in `a`, for each atom `a`.
  - Every vertex has out-degree `≥ 2`. For example, after a simple ending in `a` the next
    letter may be `a` or `ab`.
  - By §2, each generator is state-preserving off `{z^{±∞}}` and fixes those two points, which
    are eventually periodic.
- **Choice of codes.** Give the `z`-loop the code `0` and the `z^{-1}`-loop the code `10`.
  Both are primitive and they are cyclically distinct. Complete each at its vertex to a
  complete binary prefix code.
  - Then `(V)_p` at `p = z^{+∞}` is generated by the one-period shift, which is `γ(z)`. The
    same holds at `z^{-∞}`.
  - The two points lie in different `V`-orbits.
- **The germ groups.** The special case recorded in that claim gives
  `(Γ)_p = ⟨(V)_p, γ(σ_1), γ(σ_2)⟩ = γ(B_3) ≅ B_3`, by the Lemma. It also gives
  `(V)_p = γ(⟨z⟩) = γ(Z(B_3))`, which is central and hence normal.
  - The quotient is `B_3/Z(B_3) ≅ PSL_2(Z) ≅ Z/2 ∗ Z/3`, of type `F_∞` (standard).
- **Conclusion.** Items (3) and (4) of `prefix-replacement-actions-recode-into-germ-extensions-of-v`
  apply with every `n`. ∎

## Trust surface

- Imported from standard sources:
  - `Z(B_3) = ⟨Δ^2⟩`;
  - `B_3/Z(B_3) ≅ PSL_2(Z)`;
  - the identification `B_3 ≅ Mod(S_1^1)`, which is not used in the proof;
  - the left-weightedness criterion, recalled in
    `deligne-commuting-parabolic-diagonal-singularity-proof`.
- The recoding and the germ-extension conclusions are
  `prefix-replacement-actions-recode-into-germ-extensions-of-v`.
- Everything else is the explicit computation above.

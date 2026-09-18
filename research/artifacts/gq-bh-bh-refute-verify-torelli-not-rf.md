# Adversarial check: `torelli-lower-central-quotients-are-not-residually-finite` (bh-refute, 2026-09-18)

Rotation item 9 (cf691c5e9). I checked the node, its proof `torelli-lower-central-quotients-not-rf-proof`,
and the input `torelli-lower-central-quotients-do-not-virtually-split`. Nowak's Theorem D
(`thm:nonlinearity`, TeX l.274–280) and Cor. `cor:centralline` (l.2317–2323) were read at source
(`gq/src/bh-free-38/torelli_T.tex`).

Verdict: **PASS**, conditional on the node's stated trust surface. That surface is:
- Borel's stable range covering `H^2` at `g >= 3`, not read at source. `H^2(Sp_2g(Z); Q) = Q` for `g >= 3` is
  standard;
- Hain's theorem and Nowak's `thm:arithmeticextension`, as quoted;
- the Deligne residual `2Z`, a node on main.

No gap was found in the lane steps.

## Non-virtual-splitting

- Suppose `Σ ∩ N` is finite. Then it lies in `τ`, and `NΣ/τ = (N/τ) ⋊ Σ̄` with `Σ̄ ≅ Λ`.
- Malcev: `N/τ ↪ N_c(Q)` with an `Aut`-extension. Superrigidity gives an algebraic `α` on a finite-index `Λ'`.
- `(n, λ) ↦ (j(n), λ)` is a homomorphism into the linear algebraic group `N_c ⋊_α Sp_2g`. So a finite-index
  subgroup of `Q` has a representation with kernel in `τ`.
- Inducing, the kernel becomes the core, which is finite. This contradicts Theorem D. **Correct.**

## Non-residual-finiteness

- **Step 1.** `Mod(S_g)` is perfect for `g >= 3`, so it acts trivially on the line `Z_g ≅ G_a` (its character is
  into `Q^×`). So `D = j^{-1}(Z_c(Q))` is normal, with `D/τ ≅ Z`. This uses that `j(N)` is a lattice in `N_c`, so it
  meets the rational line in a lattice.
- **Step 2.** `ker(Q → L(Q)) = D`.
- **Step 3.** This is virtual splitting of `Γ = Q/D ≤ U'(Q) ⋊ Sp_2g(Q)`, layer by layer:
  - `H^1` vanishes (Margulis–Raghunathan) for the conjugation;
  - the leftover class is torsion, because it dies in `H^2(S; V(Q))` and `S` is of type `FP_∞`;
  - pushing out along `Λ ⊂ (1/n)Λ ≅ ×n` kills it.

  This is the standard fact that arithmetic groups in a Levi decomposition virtually split. **Correct.**
- **Step 4.** `E_0 ∩ N = D`, because `Σ_0` meets `Γ ∩ U'` trivially.
  - The action on `D` factors through a finite group (fix `τ`, `d ↦ dt`). So `E_1` centralizes `D`, and
    `D_1 = E_1 ∩ D ⊆ Z(D)` is central in `E_1`.
  - `D_1 = Z ⊕ F`, and `E/F` is a central `Z`-extension of `S_1`. **Correct.**
- **Step 5.** Torsion classes in `H^2(S_1; Z)` are Bocksteins of characters of finite image, since the
  abelianization is finite. So a torsion `e` would split on a finite-index subgroup, giving a `Σ` with finite
  `Σ ∩ N`. This contradicts non-splitting (take `Q' = Q`). **Correct.**
- **Step 6.**
  - Borel gives `m e − n u` torsion.
  - Pushouts along `×m` and `×n` put `E_e` and `S̃_3` in a common `X` with finite index.
  - `Res` is invariant under passing to finite-index subgroups.
  - So `Res(E_e) = Res(S̃) ⊇ 2Z` (Deligne). **Correct.**
- **Step 7.** Residual finiteness passes to quotients by finite normal subgroups. **Correct.**

## Attacks tried (all failed)

- **`E_1` has infinite index, while the non-splitting node quantifies over finite-index `Q'`.** Harmless: take
  `Q' = Q`. Only `Σ ∩ N` finite and `π(Σ)` of finite index are used.
- **A trivial central line in the discrete group.** Excluded by Malcev: `j(N) ∩ Z_c(Q) ≅ Z`.

## Lesson for general BH

Non-residual finiteness arises exactly where a unipotent completion kills a rational central line. The line
then survives in the discrete group as a central `Z`, whose extension class is a nonzero multiple of the
universal-cover class. The group is therefore commensurable-up-to-finite with a Deligne lattice. For BH, this
turns a whole family (all `Mod(S_g)/T_g[c+1]`, `c >= 2`) into Deligne-type inputs. Those are exactly the
inputs for which main already needs non-residually-finite, non-self-similar hosts, such as the Lagrangian
Thompson host of `deligne-lattice-satisfies-boone-higman`. The right move is to make that host
construction uniform in the central-extension class, not to treat each family separately.

---
rg: 2
id: char-2-benoist-quint-needs-the-homogeneous-form
kind: claim
title: The crux (BQ_2) as stated is false for every F (period-3 orbits) and fails with positive entropy for Frobenius-twisted F (a four-subgroup measure); its correct form (BQ_2') asks for Haar measure on one Γ-orbit of cosets, which under a non-square-trace condition (NS) means Haar or finitely supported, equivalently that every ergodic measure of infinite support is invariant under infinitely many translations; (BQ_2') still rules out algebraic T1
requires:
  - char-2-benoist-quint-for-free-groups-on-ledrappier-rows
  - algebraic-t1-needs-failure-of-char-p-measure-rigidity
  - algebraic-rows-carry-rigid-free-commutants-but-never-minimality
distinct_from:
  char-2-benoist-quint-for-free-groups-on-ledrappier-rows: that states (BQ_2) with "algebraic" meaning Haar measure on one coset; this shows that form is false, states the corrected homogeneous form (BQ_2'), determines which homogeneous measures exist (Haar and finite orbits under (NS), Frobenius-subfield families otherwise), and turns (BQ_2') under (NS) into a translation-invariance statement.
  algebraic-t1-needs-failure-of-char-p-measure-rigidity: that proves "(BQ_2) implies no algebraic T1" for the one-coset notion; this proves the implication from the weaker hypothesis (BQ_2'), with finite unions of cosets and finite-index stabilizers.
---

**ESTABLISHED (lane bh-bq2, 2026-09-19; lane proof, elementary given Kitchens–Schmidt as read at source in
`algebraic-t1-needs-failure-of-char-p-measure-rigidity`; not independently reviewed; no priority claimed).**
The crux itself stays **OPEN**, in the corrected form (BQ_2') below.

## Setting

- `k = F_2(s)`, `A = F_2[s^(±1), (1+s)^(-1)]`, `t = 1 + s`. `A` is a principal ideal domain, and `A/(c)` is finite
  for every `c ≠ 0`.
- `X = X_L^2 = Hom(A^2, F_2)`, the Pontryagin dual of `A^2`. A unit `u` acts by `(u·x)(a) = x(ua)`; the shifts are
  the units `u^v = s^(v_1) t^(v_2)`. `γ ∈ GL_2(A)` acts by `(γ·x)(a) = x(γ^T a)`. Let `F ≤ GL_2(A)` and
  `Γ = F × Z^2`.
- Frobenius: `A' = {a^2 : a ∈ A} = F_2[s^(±2), (1+s)^(-2)]`. As `s ∉ k^2` and `s^2 ∈ A'`, `A = A' ⊕ sA'`; also
  `A ∩ k^2 = A'`, since a square root of an `S`-integer is an `S`-integer.
- A `Γ`-ergodic probability measure `ν` is **homogeneous** if `ν = (1/n) Σ_(i ≤ n) m_(C_i)`, where the `C_i` are
  cosets of closed subgroups forming one `Γ`-orbit (`C_i = γ_i C_1`) and `m_C` is Haar measure on `C`. This is
  the form of the conclusion of Benoist–Quint and of Bourgain–Furman–Lindenstrauss–Mozes on tori: finite orbits
  and finite unions of translates of subtori.
- **(BQ_2'):** every `Γ`-invariant ergodic probability measure on `X` is homogeneous.
- **(NS)**, for non-solvable `F ≤ SL_2(A)`: every finite-index subgroup of `F` contains an element whose trace is
  not a square in `A`. For `F ≤ GL_2(A)`, apply it to `F ∩ SL_2(A) ⊇ [F, F]`.

## Statement

1. **The one-coset form of (BQ_2) is false for every `F`.** The points fixed by the shifts in `3Z^2` form a
   `Γ`-invariant group `P_3` of order 16, on which `σ_(e_1)` has order 3 and fixes only `0`. So every `Γ`-orbit
   of a nonzero point of `P_3` has size divisible by 3. Cosets in the 2-group `X` have 2-power size, so the
   uniform measure on such an orbit is `Γ`-ergodic and is not Haar measure on a coset.
2. **Frobenius-twisted `F` carry a positive-entropy four-subgroup measure.** Let `F ≤ GL_2(A')`, for example the
   entrywise Frobenius image of any free `F_0 ≤ GL_2(A)`, which is again free. For `c ∈ {1, s, 1+s, s+s^2}` put
   `Y_c = (cA'^2)^⊥`. Then:
   - the `Y_c` are four distinct infinite closed subgroups of Haar measure 0, each `F`-invariant;
   - `Z^2` permutes them transitively, through `Z^2/2Z^2`;
   - `ν_4 = (1/4) Σ_c m_(Y_c)` is `Γ`-invariant and `Γ`-ergodic, `h_(ν_4)(σ_(e_1)) > 0`, and its support is
     not a coset.

   `ν_4` is homogeneous (with `n = 4`), so it is consistent with (BQ_2'). But it shows that the Frobenius-subfield
   phenomenon, the positive-characteristic failure of sum-product, gives genuinely non-Haar, non-atomic
   invariant measures, and that any classification must allow them unless (NS) holds. Every `F ≤ SL_2(A')`
   violates (NS).
3. **Under (NS), homogeneous means Haar or finite.** Let `F ≤ SL_2(A)` be non-solvable and satisfy (NS). Then
   every closed subgroup of `X` invariant under a finite-index subgroup of `Γ` is finite or `X`. So every
   homogeneous `Γ`-ergodic measure is Haar measure or the uniform measure on a finite orbit, and (BQ_2') becomes
   the exact analogue of the torus theorem: **every `Γ`-ergodic measure is Haar or finitely supported.**
4. **Translation form.** For any non-solvable `F`, the translation stabilizer
   `Stab(ν) = {w : (x ↦ x+w)_* ν = ν}` of a `Γ`-invariant `ν` is a closed `Γ`-invariant subgroup, hence finite
   or `X`. So `ν` is Haar measure iff `Stab(ν)` is infinite. Under (NS), (BQ_2') is therefore equivalent to:
   **every `Γ`-ergodic measure of infinite support is invariant under infinitely many translations.** This is
   the analogue of the Rudolph–Host form of Furstenberg's ×2 ×3 question.
5. **(BQ_2') still rules out algebraic T1.** If (BQ_2') holds for `F`, no closed, infinite, `Z^2`-minimal,
   `F`-invariant `M ⊆ X` carries an `F`-fixed `Z^2`-invariant probability measure. This holds with or without
   (NS).

## Proof

**1.** `P_3 = (I A^2)^⊥` with `I = (s^3 − 1, t^3 − 1)`.
- In `A/I`, `s^3 = 1` and `(1+s)^3 = 1 + s + s^2 + s^3 = s + s^2 = 1`, so `s^2 + s + 1 = 0`. Conversely
  `s^3 − 1 = (s+1)(s^2+s+1)`, so `A/I ≅ F_2[s]/(s^2+s+1) = F_4`, and `P_3` is dual to `F_4^2`.
- Elements of `GL_2(A)` commute with the shifts, so `P_3` is `Γ`-invariant.
- `σ_(e_1)` is dual to multiplication by `s` on `F_4^2`. That map has order 3 and fixes only `0`, so its dual
  does too. Hence `Z/3` acts freely on `P_3 \ {0}`.
- A `Γ`-orbit of a nonzero point is a union of these free `Z/3`-orbits, so its size is divisible by 3. The
  uniform measure on it is `Γ`-invariant and ergodic, since `Γ` acts transitively on the orbit.

**2.**
- *Distinct, infinite, null.* `A^2 = A'^2 ⊕ sA'^2`, and the four elements `c` are pairwise independent over
  `k^2` (coordinates `(1,0), (0,1), (1,1), (s^2,1)` in the basis `1, s`). So each `A^2/cA'^2` is infinite, and
  `cA'^2 + c'A'^2` has finite index in `A^2` for `c ≠ c'`. Hence each `Y_c` is infinite and of infinite index,
  so Haar-null, and `Y_c ∩ Y_(c')` is finite.
- *`F`-invariance.* For `γ ∈ GL_2(A')`, `γ^T` preserves `cA'^2`, so `γ` preserves `Y_c`.
- *The shifts.* `u·Y_c = Y_(u^(-1)c)`, and `Y_c` depends only on `c` up to `A'^×`.
  - Since `s^2, t^2 ∈ A'^×`, `2Z^2` fixes each `Y_c`.
  - `s^(-1)` swaps `1 ↔ s` and `1+s ↔ s+s^2`, using `s^(-1) = s·s^(-2)` and
    `s^(-1)(1+s) = (s+s^2)s^(-2)`.
  - `t^(-1) = (1+s)(1+s)^(-2)` swaps `1 ↔ 1+s` and `s ↔ s+s^2`.
  - So `Z^2` is transitive on the four.
- *Ergodicity and entropy.*
  - The Frobenius isomorphism `A → A'` gives `(Y_s, m, 2Z^2) ≅ (X, m_X, Z^2)`: indeed
    `Y_s = (sA'^2)^⊥ ≅ Hom(A'^2, F_2)`, and `s^2, t^2` act dually to multiplication on `A'^2`. Haar measure
    on `X` is mixing (Ledrappier, recalled), so `m_(Y_s)` is ergodic for `2Z^2`. The measure `ν_4`, induced
    from this finite-index stabilizer, is `Γ`-ergodic.
  - Row `0` of a point of `X_L` is unconstrained, so `h_(m_X)(σ_(e_1)) ≥ log 2 > 0`. Hence
    `h(σ_(2e_1)) > 0` on each `m_(Y_c)`, since these are images of one another under automorphisms commuting
    with `σ_(2e_1)`. Entropy is affine, so `h_(ν_4)(σ_(e_1)) = h_(ν_4)(σ_(2e_1))/2 > 0`.
- *Not a coset.* The support `∪ Y_c` contains `0`. A coset equal to it would be a subgroup containing
  `Y_1 + Y_s = (A'^2 ∩ sA'^2)^⊥ = X`, yet the union is Haar-null.

**3.** Let `H` be closed and invariant under a finite-index subgroup of `Γ`. That subgroup contains `F_0 × Λ` with
`F_0 ≤ F` and `Λ ≤ Z^2` of finite index. So `N = H^⊥` is an `F_0^T`-stable module over
`A_Λ = F_2[u^λ : λ ∈ Λ]`. Let `k_Λ = Frac(A_Λ)` and `W = k_Λ N ⊆ k^2`.
- *`k_Λ` is a Frobenius field.*
  - Choose `m = 2^e m'`, with `m'` odd, such that `mZ^2 ⊆ Λ`.
  - First, `L = F_2(s^(m'), (1+s)^(m'))` equals `k`. The extension `k/L` is separable, since `m'` is odd. If
    `[k : L] > 1`, some `L`-embedding moves `s` to `s' ≠ s` with `s' = ζs` and `1 + s' = η(1+s)`, where
    `ζ^(m') = η^(m') = 1`. Then `(ζ + η)s = 1 + η`. So either `s` is algebraic over `F_2`, which is false, or
    `ζ = η = 1`, so `s' = s`, which is also false.
  - Hence `k_Λ ⊇ F_2(s^m, t^m) = k^(2^e)`.
  - `k/k^(2^e)` is simple and purely inseparable, so its intermediate fields form the chain
    `k^(2^e) ⊂ … ⊂ k^2 ⊂ k`. So `k_Λ = k^(2^i)` for some `i`.
- *Scalars.*
  - Let `B ⊆ M_2(k)` be the `k_Λ`-algebra generated by `F_0^T`.
  - For `γ ∈ F_0 ≤ SL_2(A)`, Cayley–Hamilton gives `γ^T + (γ^T)^(-1) = tr(γ)·I`.
  - By (NS), some `γ ∈ F_0` has `tr γ ∉ A'`, hence `tr γ ∉ k^2`. Then `k_Λ(tr γ) ⊄ k^2`, so
    `k_Λ(tr γ) = k` by the chain. As `tr γ` is algebraic over `k_Λ`, `k_Λ[tr γ] = k`, and so `B ⊇ k·I`.
- *Conclusion.*
  - `W` is `B`-stable, hence a `k`-subspace, and it is `F_0^T`-stable. A non-solvable group fixes no line, so
    `W = 0` or `W = k^2`.
  - If `W = 0`, then `H = X`.
  - If `W = k^2`, then `A^2/N` is a finitely generated torsion `A_Λ`-module. `A` is integral over `A_Λ` and
    finitely generated, hence a finite `A_Λ`-module. So some `c ≠ 0` in `A_Λ` kills `A^2/N`, and `A_Λ/(c)` is
    a finite ring (a finitely generated `F_2`-algebra of Krull dimension 0). So `H` is finite.
  - For a homogeneous `ν`, the stabilizer of `C_1 = x_1 + H_1` has finite index and preserves
    `H_1 = C_1 − C_1`. So `H_1` is finite, and `ν` is finitely supported, or `H_1 = X`, and `ν` is Haar
    measure.

**4.**
- `γ τ_w γ^(-1) = τ_(γw)`, so `Stab(ν)` is `Γ`-invariant, and it is closed.
- A closed `Γ`-invariant subgroup is the annihilator of an `F^T`-stable additive subgroup that is stable under
  `s^(±1), t^(±1)`, hence an `A`-submodule. That submodule is `0` or of full rank, since `F` fixes no line. So
  the subgroup is `X` or finite, and `Stab(ν) = X` iff `ν` is Haar measure.
- Combine with item 3.

**5.** Let `μ` be the `F`-fixed `Z^2`-invariant measure on `M`, and let `ν` be a `Γ`-ergodic component of it.
- `supp ν ⊆ M` is closed and `Z^2`-invariant, so `supp ν = M`. It is infinite.
- If `ν` is homogeneous, then `M = C_1 ∪ … ∪ C_n` with `C_1 = x_1 + H_1`. Let `Λ_1` be the finite-index
  subgroup of `Z^2` preserving `C_1`. It preserves `H_1`, and `W = ⟨x_1⟩ + H_1` is a closed `Λ_1`-invariant
  subgroup.
- The `Λ_1`-action on `W` is expansive, as a finite-index restriction of an SFT action. It has the descending
  chain condition, as its dual is a finite module over the Noetherian ring `A_(Λ_1)`. By Kitchens–Schmidt
  Theorem 7.2, `Λ_1`-periodic points are dense in `W`.
- `C_1` has index at most 2 in `W`, because `2x_1 = 0`, so it is open in `W` and contains a `Λ_1`-periodic
  point. That point has a finite `Z^2`-orbit inside `M`, so `M` is finite: a contradiction.
- If `ν` is finitely supported, `M` is finite: a contradiction again. ∎

## Relation to the crux's first tests

- **Test 1 (Frobenius).** The relevant non-Haar structure is not a self-similar measure. It is the
  four-subgroup Frobenius-subfield measure of item 2. It exists as soon as `F ≤ SL_2(A')`, which is exactly a
  way of violating (NS).
- **Test 2 (Berend-type).** Under (NS), the closed subgroups invariant under a finite-index subgroup of `Γ` are
  only the finite ones and `X` (item 3). What is left open is closed invariant *sets*.

## Credit

- Non-algebraic invariant sets and measures for zero-dimensional algebraic `Z^d`-actions go back to M.
  Einsiedler, *Invariant subsets and invariant measures for irreducible actions on zero-dimensional groups*,
  Bull. LMS 36 (2004) 321–331. The title was verified; the paper was not re-read. The four-subgroup
  construction is of the same Frobenius/subfield type, and no priority is claimed.
- The homogeneous form follows Benoist–Quint and Bourgain–Furman–Lindenstrauss–Mozes (JAMS 24 (2011)).
- Subfield phenomena in positive-characteristic homogeneous dynamics: Einsiedler–Lindenstrauss–Mohammadi,
  *Diagonal actions in positive characteristic*, arXiv:1705.10418. The title comes from a search; the paper was
  not read.

## Lesson for general BH

- **The crux is Rudolph–Host, not Benoist–Quint.** Once the subfield obstruction is excluded by the non-square
  trace condition (NS), measure rigidity for a free group of algebraic automorphisms of Ledrappier's square
  says one thing: every ergodic invariant measure of infinite support is invariant under infinitely many
  translations.
- **The subfield obstruction is real.** It is realized by Frobenius-twisted free groups, and it produces
  positive-entropy non-Haar measures. But they are unions of subgroups, and so useless for minimality.
- So the algebraic face of (RA_free) needs a measure with finite translation stabilizer. That is exactly the
  measure that no known positive-characteristic technique has yet produced or excluded.

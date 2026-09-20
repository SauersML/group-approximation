---
rg: 2
id: char-2-bq-homogeneous-form-review
kind: claim
title: Referee review of dbd5f105f8 (char-2 Benoist–Quint, homogeneous form) — both counterexamples to the one-coset form of (BQ_2) are correct (the period-3 orbits of size divisible by 3 inside F_4^2, and the four-subgroup Frobenius measure, with positive entropy, ergodic and not a coset); under (NS), homogeneous means Haar or finitely supported, so (BQ_2') is equivalent to "every infinite-support ergodic measure has infinite translation stabilizer", and (BQ_2') still excludes algebraic T1
distinct_from:
  char-2-benoist-quint-needs-the-homogeneous-form: that is the lane node under review; this checks its items 1–5.
  ct-z-bounded-transverse-drift-review: that reviews bh-2044-tc's drift theorem; this reviews bh-bq2's correction of the BQ_2 crux.
---

**ESTABLISHED (referee bh-ref-c, 2026-09-19; review of `char-2-benoist-quint-needs-the-homogeneous-form` in
dbd5f105f8, lane bh-bq2).** Verdict: **PASS.**
- Items 1–5 check line by line.
- The original crux (in the parent of dbd5f105f8) is the one-coset form: "Haar measure on a coset of a closed
  subgroup". Item 1 refutes it as stated.
- The companion node on T1 sets carrying free distal commutator actions, in the same commit, was **not** reviewed
  here.

## Item 1: the period-3 counterexample is correct

- **The finite group.** `P_3 = (I A^2)^⊥` with `I = (s^3 − 1, t^3 − 1)`. Since `t = 1 + s` is a unit,
  `(s^3 − 1) = (s^2+s+1)`, and `t^3 − 1 = s(s^2+s+1)`. So `A/I ≅ F_4` and `|P_3| = 16`.
- **The free action.** `GL_2(A)` commutes with the scalar shifts, so `P_3` is `Γ`-invariant. The shift
  `σ_(e_1)` is dual to multiplication by a primitive cube root of unity. A dual fixed point would vanish on
  `(s−1)F_4^2 = F_4^2`, so it is `0`. So `Z/3` acts freely on `P_3 ∖ {0}`, and every `Γ`-orbit there has size
  divisible by 3.
- **Not a coset.** Finite cosets in the exponent-2 group `X` have 2-power size. So the uniform measure on such an
  orbit, which is ergodic because `Γ` is transitive on it, is not Haar measure on a coset, for every `F`.

## Item 2: the four-subgroup Frobenius measure is correct

- **`A = A′ ⊕ sA′`.** Write `a = α^2 + sβ^2` in `k = k^2 ⊕ sk^2`. Then `d/ds (a) = β^2 ∈ A ∩ k^2 = A′`, since `A`
  is closed under `d/ds` and is integrally closed. So `α^2 ∈ A′` as well.
- **Distinct, infinite, null.** The coordinates `(1,0), (0,1), (1,1), (s^2,1)` are pairwise independent over
  `k^2`. So `cA′ + c′A′` has full `A′`-rank 2 in `A`, and finite index, since `A′ ≅ A` has finite residue rings.
  Hence `Y_c ∩ Y_(c′)` is finite, and each `Y_c` is infinite and of infinite index, so Haar-null.
- **Invariance.** `γ^T ∈ GL_2(A′)` preserves `cA′^2`. `u·Y_c = Y_(u^(-1)c)`, and `Y_c` depends only on the class
  of `c` modulo `A′^×`. The four swaps under `s^(-1)` and `(1+s)^(-1)` check, so `Z^2` is transitive through
  `Z^2/2Z^2`.
- **Ergodicity.** `A^2/sA′^2 ≅ A′^2`, and Frobenius gives `(Y_s, 2Z^2) ≅ (X, Z^2)`. Ledrappier Haar measure is
  mixing (a standard fact). So `m_(Y_s)` is ergodic for its finite-index stabilizer `F × 2Z^2`, and the induced
  `ν_4` is `Γ`-ergodic.
- **Entropy.** Projecting to row 0 is a surjective homomorphism `X_L → F_2^Z`. It carries Haar measure to
  Bernoulli(1/2), so `h(σ_(e_1)) ≥ log 2`. Transport through the Frobenius isomorphism, use affinity on the
  mutually singular pieces, and Abramov's formula: `h_(ν_4)(σ_(e_1)) > 0`.
- **Not a coset.** The support contains `0` and would contain `Y_1 + Y_s = (A′^2 ∩ sA′^2)^⊥ = X`, yet it is
  Haar-null.
- **Freeness.** Entrywise Frobenius is an injective homomorphism `GL_2(A) → GL_2(A′)`, so the image of a free
  group is free. Every `F ≤ SL_2(A′)` violates (NS), since its traces are squares. Correct.

## Item 3: under (NS), homogeneous means Haar or finite; correct

- **`k_Λ = k^(2^i)`.** Suppose `[k : L] > 1`. By separability (`m′` odd), `s` has a conjugate `s′ = ζs` with
  `1 + s′ = η(1+s)`. Then `(ζ+η)s = 1+η` forces `ζ = η = 1`, a contradiction. So `k_Λ ⊇ k^(2^e)`. The
  intermediate fields of the simple, purely inseparable `k/k^(2^e)` form a chain.
- **Scalars.** Cayley–Hamilton in `SL_2` gives `γ^T + (γ^T)^(-1) = tr γ·I`. (NS) gives `tr γ ∉ A′ = A ∩ k^2`, so
  `k_Λ(tr γ) ⊄ k^2`, hence it is `k` by the chain, and `B ⊇ kI`.
- **For `F ≤ GL_2(A)`.** (NS) is applied to `F_0 ∩ SL_2(A)`, which has finite index in `F ∩ SL_2(A)`. This is
  consistent with how (NS) is defined.
- **Dichotomy.** A non-solvable `F_0` fixes no line, so `W = 0` or `k^2`. If `W = k^2`:
  - `A` is finite over `A_Λ`, since `s^(-1) = s^(m−1)s^(−m)` and similarly for `t`;
  - `A^2/N` is then finitely generated and torsion;
  - it is killed by some `c ≠ 0`, and `A_Λ/(c)` is a finite ring;
  - so `H` is finite.
- **The homogeneous conclusion** follows from the finite-index stabilizer of `C_1`.

## Item 4, the equivalence: correct

- `γτ_wγ^(-1) = τ_(γw)`, so `Stab(ν)` is closed and `Γ`-invariant.
- A closed `Γ`-invariant subgroup is the annihilator of an `A`-submodule, because the full shift group is present.
  The submodule spans an `F^T`-stable subspace of `k^2`, which is `0` or `k^2` with no need for (NS). So the
  subgroup is `X` or finite, and `ν` is Haar measure iff `Stab(ν)` is infinite. This holds for every non-solvable
  `F`.
- With item 3: under (NS), (BQ_2') says that every ergodic `ν` is Haar measure or finitely supported (a finite
  ergodic measure is uniform on one orbit, hence homogeneous). That is **equivalent** to "every ergodic `ν` of
  infinite support has an infinite translation stabilizer".
- The Rudolph–Host analogy is apt.

## Item 5: (BQ_2') excludes algebraic T1; correct

- **Setup.** `supp ν = M` by minimality, and `M = ⋃ C_i`. `Λ_1 = Stab_(Z^2)(C_1)` has finite index.
  `W = ⟨x_1⟩ + H_1` is closed and `Λ_1`-invariant.
- **Kitchens–Schmidt applies.** The action on `W` is expansive, being a finite-index restriction of an
  expansive action. It has the descending chain condition, since the dual is finite over the Noetherian
  `A_(Λ_1)`. So Kitchens–Schmidt Theorem 7.2 (verified at source earlier, via MSI) gives dense
  `Λ_1`-periodic points.
- **Contradiction.** `C_1` is open in `W`, being of index `≤ 2`. So it contains a point with a finite `Z^2`-orbit,
  and then `M` is finite by minimality. The finitely supported case is immediate.

## Bottom line

The lane's correction is right. The crux should be (BQ_2'). Under (NS) it is the Rudolph–Host-type statement
"infinite support ⇒ infinite translation stabilizer", and it still kills algebraic T1. The Frobenius
four-subgroup measure shows that (NS), or an allowance for subfield families, is genuinely needed.

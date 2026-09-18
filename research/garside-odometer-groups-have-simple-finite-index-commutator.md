---
rg: 2
id: garside-odometer-groups-have-simple-finite-index-commutator
kind: claim
title: For a finite-type Artin monoid, the decorated Garside odometer full group has finite abelianization and simple commutator subgroup
requires:
  - decorated-garside-odometer-full-groups-are-type-f-infinity
distinct_from:
  decorated-garside-odometer-full-groups-are-type-f-infinity: that proves only the finiteness property F_infinity; this asks for the simplicity and abelianization facts that turn it into a Boone--Higman host.
artifacts:
  - research/artifacts/gq-bh-bh-free-15-2026-preprints.md
---

**OPEN.** Let `P = A^+` be a finite-type Artin monoid with at least two
generators, and `F_P = F(I_l(D) ⋉ ∂Ω_D)` as in
`decorated-garside-odometer-full-groups-are-type-f-infinity`. The claim is:
- (a) `F_P / D(F_P)` is finite;
- (b) `D(F_P)` is simple.

## Why this closes Boone--Higman for finite-type Artin groups

Suppose (a) and (b) hold.
1. **Finite presentation.** `D(F_P)` has finite index in the finitely presented
   group `F_P`, so it is finitely presented.
2. **Embedding.**
   - Let `e` be the exponent of `F_P / D(F_P)`, and let `U_i = X × [w_i]`,
     `i = 1..e`, be disjoint prefix cylinders in the `C_2` factor, with
     `|w_i| = ⌈log_2 e⌉`.
   - Let `ψ_i(g)` be `P_{w_i} Φ_g P_{w_i}^{-1}` on `U_i` and the identity
     elsewhere, where `P_w` is the prefix-adding bisection and `Φ` is the
     embedding of `artin-groups-embed-in-decorated-garside-odometer-groups`.
   - The `ψ_i(g)` lie in `F_P` (fullness). They have disjoint supports, and they
     are pairwise conjugate by the prefix-swapping involutions `U_i ↔ U_j`, which
     are in `F_P`.
   - Hence `ι(g) = ∏_i ψ_i(g)` is an injective homomorphism `A → F_P` whose image
     classes are `e·[ψ_1(g)] = 0`. So `ι(A) ≤ D(F_P)`.
3. **Conclusion.**
   - Every finite-type Artin group (at least two generators) embeds in the
     finitely presented simple group `D(F_P)`.
   - This includes E_6, E_7, E_8, F_4, H_3, H_4. It would answer
     Belk--Bleak--Chatterji--Matucci--Perego Question 1.12 without the
     characteristic-zero linear route.

## Gates (precise)

1. **(G1) Matui's standing hypotheses.**
   - `I_l(D) ⋉ ∂Ω_D` must be Hausdorff, effective and essentially principal.
   - Hausdorffness is expected, from finite alignment (`P'` has lcms) and
     pseudo-freeness of the odometer action. The latter was checked in step 6
     of the F_infinity node.
   - Effectiveness needs local faithfulness of left multiplication on the
     Garside boundary: `λ_x = λ_y` on a nonempty open set should force `x = y`.
     There is a fixed-set analysis like step B of
     `odometer-2v-is-fp-simple-and-contains-bs12-proof`. Degree mismatches in the
     binary factors give nowhere-dense (eventually periodic) fixed sets. The
     Garside-only case needs a separate argument, for example `a Δ^∞ = b Δ^∞` is
     an isolated coincidence.
2. **(G2) Pure infiniteness and minimality.** Lane remark in the F_infinity node:
   cylinders are equivalent to the whole space via `λ_c`, and the second factor
   doubles. With (G1), Matui's Theorem `simple2` (arXiv:1210.5800) gives (b).
3. **(G3) Finite abelianization.** Two approaches.
   - **Direct perfectness argument.** Imitate step D of the 2V_τ proof: the free
     colour kills odometer classes, since `σ_μ = σ_{μ0} σ_{μ1}` in `C_L`. The base
     full group needs its own argument.
   - **Homological argument.** Matui's AH-type sequence gives
     `H_0 ⊗ Z_2 → F_ab → H_1 → 0`. Here `H_0(G_D) = 0`, because `H_0` of the base
     is a quotient of `H_0(G_{C_P}) ⊗ H_0(G_2) ⊗ H_0(G_2)` and `H_0(G_2) = 0`
     (full 2-shift). So one needs `H_1(G_D)` finite.
     - For the base product without the odometer, Künneth with `H_*(G_2) = 0`
       suggests all homology vanishes. This is heuristic: Künneth for these
       ample groupoids is not checked at source.
     - The odometer's contribution must then be controlled.
4. **(G3') An alternative to (G3).**
   - Show that all nonempty clopen sets of `∂Ω_D` are `G_D`-equivalent. This is
     a Cuntz / Matui-Hopf-type statement; Matui proves it for SFT groupoids,
     Theorem `Hopf`.
   - Then the argument of `fp-full-binary-cantor-groups-have-type-a-actions`
     transfers: supported copies, and atom-pattern classification of clopen
     tuples.
   - That gives a type (A) action of `F_P` on proper clopens, hence
     Boone--Higman for `A` by Zaremsky's Corollary B, with no simplicity needed.
   - Note: pure infiniteness gives only mutual subequivalence of clopens, and
     Cantor--Bernstein fails in general (SFTs with nonzero `H_0`). So `H_0 = 0`
     must be used, in the form of a Hopf-type theorem for `G_D`.

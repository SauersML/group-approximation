---
rg: 2
id: ct-empty-z-odd-moduli-split-only-at-defect-primes
kind: claim
title: "Kourovka 21.74(a) for g in CT_∅(Z), odd moduli: an explicit g (n ↦ 4n, n+9, (n−3)/4) fixes every class mod 3 but permutes no nontrivial 2-power partition, so the one-prime answer does not decide 21.74(a); but a part over a flow component can split only at odd primes dividing a computable nonzero defect den(a)den(r)num(a−r)(2^s−1)"
distinct_from:
  ct-empty-z-cone-partition-question-is-decidable: that decides partitions into 2-power classes; this shows odd moduli genuinely add YES instances, and confines them to finitely many computable primes over the north-south part.
  ct-z-residue-partition-certificates-live-on-s-adic-coordinates: that proves splitting outside S needs K-blocks trivial mod ℓ (Theorem 2); this evaluates that condition along an attractor–repeller flow and extracts a computable bound on ℓ.
---

**ESTABLISHED** (lane proof; **Referee PASS** bh-ref-q11 2026-09-19). Elementary. No priority claimed.
- **What it gives.** Two facts about the odd-modulus layer of Kourovka 21.74(a) (S. Kohl) for
  elements of `CT_∅(Z) ≅ V`.
- **What stays open.** Full decidability for such elements. The remaining gap is a bound on
  prime-power depths (see the end).

## 1. The obstruction: YES through mod 3, NO through every 2-power partition

Define `g : Z → Z` by
- `g(n) = 4n` if `n ≢ 3 (mod 4)`;
- `g(n) = n + 9` if `n ≡ 3 (mod 16)`;
- `g(n) = (n − 3)/4` if `n ≡ 7, 11, 15 (mod 16)`.

**Claims.**
- (a) `g ∈ CT_∅(Z)`.
- (b) `g(n) ≡ n (mod 3)` for every `n`, so `g` fixes each of `0(3), 1(3), 2(3)` and is YES.
- (c) `g` permutes no partition of `Z` into at least two classes with 2-power moduli.

*Proof.*
- **(a).** The pieces are canonical maps between classes mod powers of 2:
  - `0(4), 1(4), 2(4)` go to `0(16), 4(16), 8(16)` by `n ↦ 4n`;
  - `3(16)` goes to `12(16)`;
  - `7(16), 11(16), 15(16)` go to `1(4), 2(4), 3(4)`.

  Both partitions are complete, so `g ∈ CT_∅(Z)` by item 3 of
  `ct-p-z-is-a-one-vertex-k-graph-full-group`.
  - In base-4 digits, least significant first, these are the prefix replacements
    `0→00, 1→01, 2→02, 30→03, 31→1, 32→2, 33→3`.
- **(b).** `4 ≡ 1`, `9 ≡ 0` and `3 ≡ 0 (mod 3)`, so each formula is `≡ n`.
- **(c).** Let `𝒫` be a permuted 2-power partition, `K = |𝒫|!`, and `C ∈ 𝒫` the part containing
  `0`. `Ĉ` is a clopen neighbourhood of `0` in `Z_2`, and it is fixed by `ĝ^K`.
  - Every `x ∈ Z_2 ∖ {−1}` satisfies `ĝ^n(x) → 0`. In digits:
    - `d z ↦ 0 d z` for `d ≠ 3`;
    - `3^k d z ↦ d z` in `k` steps for `d ∈ {1, 2}`;
    - `3^k 0 z ↦ 3 0 z ↦ 0 3 z`.

    So leading zeros accumulate.
  - Hence `ĝ^(Kn)(x) ∈ Ĉ` for large `n`, so `x ∈ Ĉ`.
  - Therefore `Ĉ ⊇ Z_2 ∖ {−1}`, so `Ĉ = Z_2` and `|𝒫| = 1`.
  - Equivalently: there is one flow component (repeller `−1`, attractor `0`), whose cone hull is
    `Z_2` (`ct-empty-z-cone-partition-question-is-decidable`). ∎

**Consequence.** For `g ∈ CT_∅(Z)`, the literal 21.74(a) is not decided by the 2-adic (V)
dynamics. The odd fibres of the skew product carry independent YES certificates.

## 2. Localization: odd splitting primes divide a computable defect

**Setting.** As in `ct-z-residue-partition-certificates-live-on-s-adic-coordinates` (S = {2}):
- `ĝ(x, y) = (g(x), β_x(y))` on `Z_2 × Ẑ_odd`, where each block `β_x` has the same affine formula
  as the piece of `g` at `x`;
- `V ⊆ Z_2` is the north–south part, and the `R_j` are its flow components, as in the cone node;
- `M` is a common period, so that `g^M` fixes each attractor `a` with formula
  `C(y) = a + 2^t(y − a)` (`t ≥ 1`) on a contracting cone, and each repeller `r` with formula
  `R(y) = r + 2^(−s)(y − r)` (`s ≥ 1`) near `r`;
- `a`, `r` are rationals with odd denominators.

**Theorem.** Suppose `g` permutes a partition `𝒫` of `Ẑ` into boxes, and some `C ∈ 𝒫` has an
odd prime `ℓ` dividing its modulus, with `C_2 ∩ V ≠ ∅`.
- Then `C_2 ⊇ R_j` for some `j`.
- For every flow edge `r — a` in `R_j`, `ℓ` divides the nonzero integer
  `D(r, a) = den(a) · den(r) · num(a − r) · (2^s − 1)`.
- In particular, only finitely many computable primes can occur in the odd part of moduli of
  parts over `V`. Parts over the finite-order part `U` are unconstrained, but they can always be
  refined, as in the cone node.

*Proof.* Put `K = |𝒫|!`.
- **Step 1: `C_2 ⊇ R_j`.** `ĝ^K(C) = C` gives `g^K(C_2) = C_2`. Then `C_2 ∩ R_j` is a nonempty
  `g^(MK)`-invariant clopen subset of `R_j`, so it equals `R_j` (Lemma A of the cone node).
- **Step 2: trivial blocks.** `ĝ^(MK)` fixes every part. The proof of Theorem 2 of the S-adic
  node uses only this, so the blocks of `ĝ^(MK)` at every `x ∈ C_2` are trivial mod `ℓ`. So is
  the formula of `g^(MKi)` at any `x ∈ C_2`, being a composite of such blocks along an orbit that
  stays in `C_2`.
- **Step 3: along a flow edge.**
  - Pick `x ∈ R_j` with `α(x) = r` and `ω(x) = a` that lies in `r`'s expanding cone `Γ_r`. A far
    backward iterate of any point on the edge does.
  - On `Γ_r`, `g^(−M)` is the contraction `ρ = R^(−1)` into `Γ_r`. Let `x` enter the contracting
    cone of `a` at time `M n_0`, and let `g^(M n_0)` have formula `T(y) = U_T y + B_T` at `x`
    (`U_T` a power of 2).
  - For `m ≥ 0`, put `x_m = ρ^m(x) = g^(−Mm)(x) ∈ Γ_r`. The formula of `g^(Mm)` at `x_m` is
    `R^m`. Pick `q ≥ 0` with
    `m + n_0 + q ∈ KZ`. The formula of `g^(M(m + n_0 + q))` at `x_m` is
    `F_m = C^q ∘ T ∘ R^m`, and it is trivial mod `ℓ` by Step 2.
  - Assume `ℓ ∤ den(a) den(r)`. Then `a` is ℓ-integral, and `F_m(a) − a ≡ 0 (mod ℓ)`.
  - But `F_m(a) − a = 2^(tq) (T(R^m a) − a)` and `R^m a = r + 2^(−sm)(a − r)`. So
    `T(r) − a + U_T 2^(−sm)(a − r) ≡ 0 (mod ℓ)` for every `m ≥ 0`.
  - Subtracting the cases `m = 0` and `m = 1` gives `U_T (a − r)(1 − 2^(−s)) ≡ 0`. So
    `ℓ | num(a − r)(2^s − 1)`. ∎
- **Check on §1.** Here `a = 0`, `r = −1`, `s = 2`, so `D = 1 · 1 · 1 · 3 = 3`, exactly the
  prime used.

## What remains for full decidability on `CT_∅(Z)`

- **The plan.** For each fixed odd `m`, whether `g` permutes a box partition whose odd parts divide
  `m` is a finite search of the cone-node type. Run it on the skew product over `Z_2 × Z/m`, an
  element of the Higman–Thompson group with `m` roots. Gilabert Vio's Cor. 2.4 covers all
  locally finite rooted trees, and boxes are cone × coset.
- **Primes.** §2 bounds the primes over `V`, and `U` is harmless.
- **What is missing.** A computable bound on the `ℓ`-adic depth `e` (`ℓ^e | m`). The same flow
  argument, run mod `ℓ^e` on the ball-invariance of Step 1 of Theorem 2 of the S-adic node,
  should give `e ≤ v_ℓ(D)`. This is not written out here.

## Lesson for general BH

**Coordinates add information that dynamics does not see, but only at primes the dynamics
certifies.**
- The odd fibres of a one-prime element carry YES certificates invisible to its V-dynamics.
- Yet every such certificate over the north–south part must pass through a flow edge, and the
  edge's affine data (the attractor–repeller displacement and the repelling slope) name the only
  primes where it can live.

**For hosts.** Hidden coordinate structure is a finite, computable perturbation of dynamical
structure in one base. In several bases the flow edges themselves carry the carries.

## Referee (bh-ref-q11, 2026-09-19): PASS for §1 and §2

**§1: membership and pieces checked explicitly.**
- The source classes `0(4), 1(4), 2(4), 3(16), 7(16), 11(16), 15(16)` partition `Z`, since `3(4) = 3,7,11,15 (16)`.
- The target classes `0(16), 4(16), 8(16), 12(16), 1(4), 2(4), 3(4)` partition `Z`, since `0(4) = 0,4,8,12 (16)`.
- Every piece is the canonical affine map `r_1 + km_1 ↦ r_2 + km_2`:
  - `1+4k ↦ 4+16k`;
  - `3+16k ↦ 12+16k`;
  - `7+16k ↦ 1+4k`, `11+16k ↦ 2+4k`, `15+16k ↦ 3+4k`.
- So `g` is a prefix replacement between complete binary codes, i.e. an element of `V = CT_∅(Z)` (Kohl, Remark 1.4, via class transpositions). The base-4 digit rules match.
- **Mod 3.** `4 ≡ 1`, `9 ≡ 0`, and `(n−3)/4 ≡ n − 3 ≡ n (mod 3)`, so every class mod 3 is fixed.
- **Dynamics on `Z_2`.** `d z ↦ 0dz` (`d ≠ 3`); `3^k d z ↦ dz` (`d ∈ {1,2}`); `30z ↦ 03z`. So every `x ≠ −1` tends to `0`, and `−1 = 333…` is fixed.
- The part containing `0` is `ĝ^(|𝒫|!)`-invariant, so it is all of `Z_2`. So there is no 2-power partition.
- This confirms that the 2-power sub-case (`ct-empty-z-cone-partition-question-is-decidable`) does not decide 21.74(a) for elements of `V`.

**§2: the localization is correct.**
- **Step 2 import.** Theorem 2 of the S-adic node uses only that `ĝ^K` fixes every part.
  - Its Step 1 is equal Haar measure.
  - Its Step 2: a non-trivial affine map mod `ℓ` fixes at most one residue, so a second part through `x` would need `C″_ℓ = Z_ℓ`, which overlaps `C`.
  - So it holds with `MK` in place of `K`, and it extends to composites along orbits in `C_2 = g^(MK)(C_2)`.
- **Step 3.** `F_m = C^q ∘ T ∘ R^m` is a formula of `g^(MKi)` at `x_m ∈ R_j ⊆ C_2`.
  - With `a` `ℓ`-integral, `F_m(a) − a = 2^(tq)(T(r) − a + U_T 2^(−sm)(a − r))`.
  - `m = 0, 1` give `ℓ | num(a−r)(2^s − 1)`, since `U_T` and `2^(tq)` are units.
  - `D ≠ 0` because `a ≠ r` and `s ≥ 1`.
- **The check on §1.** Near `−1` the formula is `(y−3)/4 = −1 + 2^(−2)(y+1)`, so `s = 2` and `D = 3`, which is exactly the prime used.

**Still open, as the node says:** the `ℓ`-adic depth bound, and so full decidability on `CT_∅(Z)`.

# What Kourovka 17.57 needs from Adamczewski–Bell (bh-pal-kourovka57, 2026-09-19)

**Source.** Adamczewski–Bell, *A problem about Mahler functions*, arXiv:1303.2019. The TeX was
read at source (v1, March 2013).

## How their proof of `thm: main` runs

This is Section `sec: main`.
- Reduce to `R` a localization of a number ring. For many prime ideals `𝔓`:
  - split `F = G · Π`;
  - prove `F mod 𝔓` is `k`- and `ℓ`-automatic, using Becker (Section `sec: auto`),
    elimination of singularities at roots of unity (`sec: elim`) and Chebotarev (`sec: chebotarev`).
- **Cobham's theorem** then makes `F mod 𝔓` eventually periodic, hence rational.
- The local–global Lemma `lem: rational` concludes.
  - It rests on Lemma `lem: AB`: a rational solution of a fixed Mahler equation has
    denominator degree at most `d`, uniformly.
  - All `(d+1)`-minors of the Hankel matrix then vanish mod `𝔓`, hence vanish.

Cobham's theorem, Chebotarev and the singularity analysis are used only to make every reduction
`F mod 𝔓` rational.

## Why 17.57 needs only the last two lemmas

Let `Φ = φ|ℕ₀` for a normalizer `φ ∈ Homeo(Ẑ)`, and `F = Σ Φ(n) xⁿ ∈ ℤ[[x]]`.
- Matui's spatial theorem makes `φ` a homeomorphism of `Ẑ` preserving `ℤ`. It is uniformly
  continuous, so `Φ mod M` is purely periodic for every `M`. So `F mod p` is rational for
  every prime `p`, for free.
- Purely periodic: `F mod p = C/(1 − x^T)` with `deg C < T`. Its reduced form `A/B` has
  `deg A < deg B`. So only the denominator bound of `lem: AB` is needed, not the numerator bound.
- `F` is 2-Mahler (steps 1–2 of `out-ct-z-is-c2`: dilation recursions, then regular ⇒ Mahler).
  - `lem: AB` gives `deg B_p ≤ d` for all `p` with `P_n mod p ≠ 0`.
  - `lem: rational` then gives a linear recurrence for `Φ` over `ℚ`.
- **Only one base is used.** Multiplicative independence and Cobham's theorem are not needed.
  The second prime enters through the continuity on `Ẑ = ∏ Z_p`, which comes from Matui.

## Formalized (Mathlib only, `GroupApproximation/ClassTransposition/Out/`)

| File | Content | Status |
|---|---|---|
| `MahlerAB.lean` | `natDegree_denom_le_of_mahler`: `lem: AB`, the denominator bound | proved, unprobed |
| `LocalGlobal.lean` | `exists_rat_recurrence_of_mod_primes`: `lem: rational` over `ℤ`, proved without minors via a cleared rational left inverse | proved, unprobed |
| `Cont.lean` | `IsProfinitelyContinuous`, `CTSpatialContOwed` (Rubin lane), `CTRigidContOwed`, and `kourovka_17_57_of_cont` | proved from those two props |

## What remains inside `CTRigidContOwed`

Each item is elementary, and none is formalized yet.
1. **Dilation recursion.** `Φ(2k+e) = β(k)Φ(k) + α(k)` with `β` and `α` periodic. Inputs:
   `CT ⊆ RCWA` (17.59) and continuity.
2. **Regular ⇒ Mahler.** Linear algebra over `ℚ(x)`.
3. **Glue.** `F mod p` periodic, together with the reduced Mahler equation, gives the
   hypothesis of `exists_rat_recurrence_of_mod_primes` with `D = d + 1`.
4. **Recurrence ⇒ quasi-polynomial.**
   - Fatou puts the denominator in `ℤ[x]` with constant term 1.
   - The growth bound `|Φ(n)| ≤ Cn^D` leaves no poles in `|x| < 1`.
   - Kronecker makes the poles roots of unity.
   - The Mahler property cannot replace this: every rational function is Mahler.
   - Continuity cannot either: the Lucas numbers are periodic mod every `M`.
5. **Counting.** A bijection forces an affine class, and continuity extends it to the whole class.
6. **(b) ⇒ (c).** Conjugating by class transpositions spreads affinity to RCWA.

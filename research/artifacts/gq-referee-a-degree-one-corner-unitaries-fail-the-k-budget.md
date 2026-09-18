# Referee report (gq-referee-a, proof-gap lens): degree-one corner unitaries fail the K-budget

**Reviewed:** `degree-one-corner-unitaries-fail-the-k-budget` and its `-proof` (lane gq-infinite-primes, c5c61e222),
read on origin/main (2e742d531).

**Verdict: FAIL at one step of item 1, repaired below.** With the repair, items 1–7 hold.
- Items 5–7 (the frame designs, and the answer to gate Attempt 10) are not affected. There `w = ewe` holds
  automatically.
- The three points the author asked about are all correct.

## The failing step (item 1)
The proof asserts "`w = ewe`, since `ew = ww'w = we`, and `w' = ew'e`". The two equalities are right:
`ew = ww'w = we`, and likewise `ew' = w'e`. But they do not give `w = ewe`, and the claim "`u_e = w + 1 − e` is a
unit" is false under the stated hypotheses.

**Counterexample.**
- *The ring.* `R = M_2(Q)[x^±1]`, graded by the power of the central `x`, with `e = E_11`, which is full.
- *The pair.* `w = x ∈ R_1` and `w' = E_11 x^(−1) ∈ R_(−1)`. Then `w'w = E_11 = e` and `ww' = E_11 = e`.
- *The failure.* `u_e = x + E_22 = diag(x, x+1)` is not a unit, because `x+1` is not a unit of `Q[x^±1]`. Also `w` is
  not in `eRe`, so it is not "a unit of `eRe` of degree 1".

**Repair (verified).** Replace `(w, w')` by `(ewe, ew'e)`.
- *They stay in the right degrees.* `ewe ∈ R_1` and `ew'e ∈ R_(−1)`, since `e ∈ R_0`.
- *The hypotheses survive.*
  - `(ewe)(ew'e) = e(we)w'e = e(ew)w'e = e(ww')e = e`.
  - `(ew'e)(ewe) = e(w'e)we = e(ew')we = e(w'w)e = e`.
- *Consequences.* Now `w = ewe`, so `wf = 0 = fw'`, `u_e = ewe + f` is a unit with inverse `ew'e + f`, and item 1
  holds.
- *Wording.* Either add the hypothesis `w = ewe` to the Statement, or define `u_e = ewe + 1 − e` and say that
  `(ewe, ew'e)` again satisfies the hypotheses.

## The three points the author asked about (correct)
- **The symbol computation in `C = eRe × fRf`.**
  - For `N ≥ 3`, `St_N(C) = St_N(eRe) × St_N(fRf)`, by the product-ring argument checked in my
    `euler-triangular-steinberg-retracts…` report.
  - `{(e, λf), (w, f)}_C = ({1_(eRe), w}, {λ·1_(fRf), 1_(fRf)}) = (1, 1)`.
  - Its image under `C ⊆ R` is `{λf + e, u_e}`, which is therefore 1. ✓
  - `λ = (λe+f)(λf+e)`. The units `λe+f`, `λf+e` and `u_e` commute pairwise: for instance
    `(λe+f)(w+f) = λw + f = (w+f)(λe+f)`. So bimultiplicativity in their commutative subring gives
    `{λ,u_e} = {λe+f, u_e}`.
  - The first factor of `K_2(C) → K_2(R)` is `A ↦ A + fI`, the corner map of (M). ✓
- **`μ_λ` is well defined on `K_0`.**
  - *Equivalent idempotents.* If `g = ab` and `h = ba`, then
    `λg + 1 − g = 1 + (λ−1)ab` and `λh + 1 − h = 1 + (λ−1)ba`. Since `[1 + xy] = [1 + yx]` in `K_1`, these have
    the same class.
  - *Stabilization.* `g ⊕ 0 ↦ (λg + 1 − g) ⊕ 1`, with the same class.
  - *Orthogonal sums.* The value is additive on them.
  - So this is a monoid map from idempotents modulo equivalence and stabilization to the group `K_1(R)`. It extends
    uniquely to `K_0(R)`, with `μ_λ[1] = [λ]` and `μ_λ[e] = [λe + f]`.
  - Then `t[1] = n[e]` gives `λ^t ∈ ker` for `λ ∈ Λ_e`. `{λ^t : λ ∈ Λ_e} ≅ Λ_e/(finite)` is not finitely generated when
    `Λ_e` is not. ✓
- **The clearing of denominators in 7(b).**
  - Write `[1_B] = cv + (1−A)z` with `c ≠ 0`, since otherwise (a) holds, and `[e] = εv`. Then
    `[1_B] = (c/ε)[e] + (1−A)z`.
  - Write `c/ε = a/b` and take `t = b`, `n = a ≠ 0`. Then `t[1_B] − n[e] = (1−A)(tz)`.
  - `K_0(B) = Q^m` is a `Q`-vector space, so `tz ∈ K_0(B)` and there is no integrality issue. ✓

## Other checks
- **Item 2.**
  - The graded node applies to `eRe`, with `λ ↦ λe` unital and the unit `ewe` in degree 1.
  - (M) identifies the kernel with `Λ_e`.
  - The symbols `{λ, u_e}` are Steinberg symbols of commuting units of `R`, so the symbol lemma applies. ✓
- **Item 4.** Take the torsion defect `z` of `t[1] − n[e]`, of order `o`, and rescale by `o`. ✓
- **Item 5.**
  - `x = xyx = φ(e)x` and `pφ(e) = φ(e)`, so `px = x`.
  - `w'w = ypx = yx = e` and `ww' = sφ(e)t = e`.
  - `w = ewe` holds here: `ew = esx = sφ(e)x = sx` and `we = sxe = sxyx = sφ(e)x = w`. So the failing step does
    not affect the frame part. ✓
- **Item 6.** With `T_n = diag(t)` and `S_n = diag(s)`, `(T_n g)(g S_n) = φ(g)` and `(g S_n)(T_n g) = g`. ✓
- **Item 7.**
  - `U_Q`-type factors have idempotents of every class in `[0,1] ∩ Q`.
  - Matricial cancellation gives `φ(e) ~ e`.
  - Perron–Frobenius: 1 is a simple root, so `ker(1−A) ∩ im(1−A) = 0` and `v ∉ im(1−A)`. A rational kernel vector
    can be chosen `≥ 0`. ✓
  - The open example checks: `A = [[2,1],[2,3]]` has eigenvalues 1 and 4, `ker(1−A) = Q(1,−1)`, and the left fixed
    vector is `(2,−1)`, with `(2,−1)·(1,1) = 1`.

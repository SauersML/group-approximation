# Referee report (gq-referee-b, citation/scope lens): renormalization return times tend to zero adically

**Reviewed.** `renormalization-return-times-tend-to-zero-adically` and its `-proof` (lane gq-nv-obstruct), read on
origin/main (db7acc3f9). There was no earlier review.

**Verdict: PASS.** There is no external citation. The one import is item 2 of
`renormalizable-thompson-elements-are-odometer-codes`, and it is used as stated. Items 1–3 are correct. One scope fix
(W1) is in the Calibration.

## Checks

- **Item 2.**
  - `π(x) = digit(x) + m π(Sx)`, so `π mod m^(j+1)` is determined by `digit(x)` and `π(Sx) mod m^j`.
  - The induction then goes through from the definition of `P`: the depth-`(D+(j−1)P)` brick of `Sx` is fixed by the
    depth-`(D+jP)` brick of `x`.
  - The tape-radius corollary depends on the coding constants `c_0`, `c_1`. It is stated as a consequence for
    bounded prefix codes, which is fine.
- **Item 3.**
  - `π ∘ T^n = π + n` for all `n ∈ Z`, since `T` is a homeomorphism.
  - Continuity of `π` gives `n_i → 0` in `Z_m`.
  - The contrapositive, with `m^j ∤ n_i` for all `i`, is correct.
  - The item needs a genuine convergence `T^(n_i) y → y`, at every radius.

## Scope

- **W1 (Calibration, last bullet).** "For binary-timing machines the test fails. See §3e" reads as a settled
  non-renormalizability result. The artifact's §3e says otherwise.
  - The returns of `y` found have `n ≡ 4 mod 8`, but only up to radius 18.
  - §3e's own Reading says convergence "is certified only up to radius 18, so this remains OPEN".
  - Suggested wording: "for the binary-timing machine `M°` of §3e, the returns found up to radius 18 violate item 3's
    condition. Item 3 applies only if they converge at all radii, which is OPEN."
- **The SMART calibration.** The `m = 3` factor comes from the proved node, and the MSI returns (`n ≡ 0 mod 729`) are
  reported as data. Accurate.

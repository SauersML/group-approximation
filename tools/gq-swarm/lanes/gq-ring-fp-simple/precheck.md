
## Rational-shear search (second round): blindness pre-check, done before any run

Searched subgroup: `G = <σ_2^j x_12(q) σ_2^-j, σ_2^j x_21(q) σ_2^-j, W, D>` with `|j| <= 1`. There are two
choices of `q`:
- `q in Q_2 = {±1, ±2, ±1/2}`;
- `q in Q_23 = Q_2 ∪ {±3, ±1/3}`.

`G ⊆ N` by Attempt 5. Put `S = {σ^j(p) : p | q, |j| <= 1}`, where `p | q` means `p` divides the numerator or
the denominator of `q`. So `S = {2, 3, 5}` for `Q_2` and `S = {2, 3, 5, 7}` for `Q_23`.

Every invariant known to be preserved by all generators of `G`, and whether `r` violates it:

| invariant | preserved by `G` | `r` |
|---|---|---|
| degree 0 (commutes with scalars) | yes | yes |
| maps lines through 0 to lines, linearly on each | yes | yes |
| `v_p(content)` for primes `p ∉ S`: `σ_2^j x(q) σ_2^-j` changes content only at primes `σ^j(p)`, `p \| q` | yes | yes: `r` changes content only at 2, which is in `S` |
| the set `Z[1/S]^2` | yes | yes: its factors lie in `GL_2(Z[1/2])` or are `σ_2`-conjugates of `GL_2(Z)` |
| full content | no (`x_12(1/2)`) | — |
| pair determinants | no (`σ_2 x_21(1) x_12(1) σ_2^-1` doubles the axis-pair determinant, Attempt 1) | — |
| axis character `χ`, three-line scalar `χ_3` | not known to be invariant | `χ(r) = χ_3(r) = 1`, so no violation either way |
| scalars on `ℓ_x, ℓ_y, ℓ_-` | not an invariant | `(1,1,1)`, as for the identity |

`r` violates none of these, so the search is not blind by any known invariant.
- *Test 1 is not blind.* The quotient `V_1 V_2^-1 = L` must preserve `p`-content for `p ∉ S`, so
  `L in GL_2(Z[1/S])`. Then `|det L|` is an `S`-unit and may be 2.
- *Test 2 is not blind.* `L r in G` forces only `L in GL_2(Z_(p))` for `p ∉ S`.

**Calibration inside `G`.** Take the planted target `P = X(-1) ∘ σ_2^-1 X(1) σ_2`, word `s-1X(1) s0X(-1)`.
It lies in `G` and fixes both axes and `(1,-1)`.
- Run `qcal` (`Q_2`, length <= 3, 38,619 elements) found all 39 of 39 translated words with `|det L| = 1`.
- It counted 902 words equal on the probes to a linear map of determinant ±1 other than `±I`, for example
  `x_12(1/2)` itself.
- It found no linear hit with `|det L| != 1`, as is necessary unless a hidden relation exists.

# Referee report (gq-referee-b, citation/scope lens): graded rings with degree-one units fail the K-budget

**Reviewed.** `graded-rings-with-degree-one-units-fail-the-k-budget` and its `-proof`, read on origin/main (db7acc3f9),
after e5c92f023. This is the second review; gq-referee-a PASSed it (223c763b9).

**Verdict: PASS.** The internal import is used exactly within its hypotheses, and the W1 fix is in place.

## Hypothesis match

`laurent-rational-symbols-block-fp-elementary-groups`, which I refereed PASS, requires four things. All four hold.

| Requirement | Why it holds |
|---|---|
| `B` unital, with a unital subring `Q ⊆ B` | `B = R_0`, which contains `1` and `Q` by item 1. |
| `σ` fixes `Q` pointwise | `Q` is central, since inverses of central units are central. |
| `R = B[u^(±1); σ]` | Item 1 identifies `R` this way. The map is injective because it respects degree. |
| The image of `Q^x → K_1(B)` is not finitely generated | Item 2: the image in `K_1(R)` is a quotient of the image in `K_1(R_0)`. |

**Dichotomy.** If the image is finitely generated, the kernel `K` has `K ⊗ Q` of infinite dimension, so `K` is not
finitely generated. The two cases are exclusive. Correct.

## The lamplighter computation (checked)

- `K_1(M_r(Q)) = Q^x` via `det`, and the scalar `λ` at stage `m` has determinant `λ^(n^(2m+1))`.
- The transition maps raise `det` to the power `n^2`.
- So the kernel is `{±1}` for `n` even and `{1}` for `n` odd. For `U_Q` the kernel is `{±1}`.
- `K_0(U_n) = Z[1/n]`, with `[1]` of infinite order.

## Scope

- **W1 fix.** "Adding homogeneous relations keeps the ring under the dichotomy ... can ... move the ring to the first
  case" is the corrected text, and it is accurate.
- **"Graded cures are dead".** This is correct as "fail the K-budget in one of its two halves". A cure that stays
  graded with a degree-one unit is excluded. The node names the only exits: a non-unit shift, or inhomogeneous
  relations.
- **The Pimsner calibration.** It relies on `∂{λ, u} = ±[λ]`, which is trust surface T1 of the Laurent node,
  recorded there. It is not load-bearing here.
- **"Not decided".** Correctly stated.

---
rg: 2
id: torsion-k1-modulo-central-scalars-kills-scalar-symbols
kind: claim
title: If the algebraic closure of Q is central in R and K_1(R) is torsion modulo the classes of central scalars, then every symbol {λ, x} with λ a central algebraic scalar vanishes in K_2(R)
distinct_from:
  algebraic-closure-kills-rational-steinberg-symbols: that kills the rational symbols {λ, μ}, and shows {λ, x} = 0 is forced for central Q̄ once E_N(R) is finitely presented; this gives a K_1 condition under which every {λ, x} vanishes, with no finiteness hypothesis.
  frame-unit-symbols-can-vanish-without-a-grading: that shows the frame unit is the wrong place to look for an obstruction; this reduces the scalar symbols of all units to a K_1 condition.
  fp-simple-resolvent-ring-with-divisible-unit-class: that is the ring gate; this turns the K_2 half of its symbol budget, for central Q̄, into a condition on K_1.
artifacts:
  - research/artifacts/gq-gq-k2-q-rf-hosts.md
  - research/artifacts/gq-referee-b-torsion-k1-modulo-central-scalars-kills-scalar-symbols.md
---

**ESTABLISHED (2026-09-18)** through `torsion-k1-modulo-central-scalars-kills-scalar-symbols-proof`. Lane proof
(gq-k2-q), elementary given classical inputs. *Reviewed:* citation PASS by `gq-referee-b`
(`research/artifacts/gq-referee-b-torsion-k1-modulo-central-scalars-kills-scalar-symbols.md`), all inputs pinned; the
proof-gap review is pending. This verifies the coordinator's sketch,
with the product built by hand rather than taken from Loday.

## Statement

Let `R` be a unital ring with `Q̄ ⊆ Z(R)` unitally, and let `ι : Q̄^x -> K_1(R)` be the map on classes of central
scalars.

1. **The scalar pairing.** For each `ν ∈ Q̄^x` there is a homomorphism `Φ_ν : K_1(R) -> K_2(R)` with
   `Φ_ν([x]) = {ν, x}` for every unit `x ∈ R^x`. It is multiplicative in `ν`: `Φ_(νν') = Φ_ν Φ_(ν')`.
2. **`K_2(Q̄) = 0`.** In particular `Φ_ν(ι[μ]) = {ν, μ} = 0` for all `ν, μ ∈ Q̄^x`.
3. **The criterion.** If `K_1(R)/ι(Q̄^x)` is a torsion group, then `Φ_λ = 0` for every `λ ∈ Q̄^x`. So
   `{λ, x} = 0` in `K_2(R)` for every central `λ ∈ Q̄^x` and every unit `x`. This includes the rational symbols
   and the symbols of every frame unit.

## Consequences

- **The K_2 half of the gate becomes a K_1 condition.** For
  `fp-simple-resolvent-ring-with-divisible-unit-class` with `Q̄` central, the symbol budget, taken over all units,
  holds as soon as `K_1(R)` is "scalars plus torsion". The design target is then:
  - a finitely presented simple ring `R` with `Q̄ ⊆ Z(R)`;
  - `[1]` of infinite order, and divisible;
  - `K_1(R) = ι(Q̄^x) + torsion`.

  The ultramatricial `U_Q̄ = colim M_(n!)(Q̄)` has all three properties except finite presentation.
- **Calibration.** The doubled lamplighter of `frame-unit-symbols-can-vanish-without-a-grading`, tensored up to
  `Q̄`, fails the criterion.
  - `K_1` contains the class of `diag(u, 1)`. The Bass–Heller–Swan boundary sends it to `[1_B] ∈ K_0(B)`, which has
    infinite order, while scalars go to `0`.
  - So that class is not torsion modulo scalars, and its scalar symbols are infinitely generated.
- **The criterion is only sufficient.** A non-torsion non-scalar class `y` does not by itself force `Φ_λ(y) ≠ 0`.
  The obstruction direction needs a map that detects `Φ_λ(y)`, such as the Pimsner boundary `K_2(R) -> K_1(B)`.
  This is heuristic here and conditional on `(P)` of `resolvent-register-units-give-rational-symbols`.
- **Only stable `K_2(R)` is concerned.** That is what `infinitely-generated-symbols-block-fp-elementary-groups`
  uses.

## Pimsner reading (conditional, not established)

This section assumes the Pimsner six-term sequence `(P)` of `resolvent-register-units-give-rational-symbols` for
`R` over a coefficient ring `B`, with the boundaries `K_*(Q̄)`-linear. Take `B` ultramatricial over the central
`Q̄`, so that `K_1(B) = K_0(B) ⊗ Q̄^x`, and write `A = [X]` on `K_0(B)`.

- *The `K_1` condition in terms of `A`.*
  - `(P)` gives `0 -> coker(1 − A) ⊗ Q̄^x -> K_1(R) -> ker(1 − A) -> 0`.
  - `Q̄^x` is a torsion group plus a `Q`-vector space. So `K_1(R)` is scalars plus torsion if and only if
    - `ker(1 − A)` is `0` (`K_0(B)` is torsion-free), and
    - `coker(1 − A) ⊗ Q` is spanned by `[1_B]`.
  - The gate also wants `[1_R]`, the image of `[1_B]`, of infinite order. So `coker(1 − A) ⊗ Q = Q·[1_B] ≠ 0`.
- *Index one is excluded.*
  - If `A[1_B] = [1_B]`, then `[1_B] ∈ ker(1 − A)`, so some `y ∈ K_1(R)` has `∂y = [1_B]`.
  - By linearity `∂(Φ_λ(y)) = ±[λ]`. So the scalar symbols of `y` map onto the image of `Q^x` in `K_1(B)`, which is
    infinitely generated.
  - This is the ungraded, `(P)`-conditional form of the graded dichotomy, and the mechanism behind the doubling
    calibration.
- *Finite rank is excluded.*
  - If `K_0(B)` has finite rank, injectivity of `1 − A` makes `coker(1 − A)` finite, so `[1]` is torsion.
- *The room left.* An index `≠ 1` correspondence over an ultramatricial `B` with `K_0(B)` of infinite rank, such
  that `1 − A` is injective with rank-one cokernel spanned by `[1_B]`. This is the infinite-rank `K_0(B)` room of
  gq-infinite-primes.

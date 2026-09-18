# Second review (gq-referee-a, proof-gap lens): the resolvent Steinberg residual is infinitely normally generated

**Reviewed:** `resolvent-steinberg-rf-residual-is-infinitely-normally-generated` (lane gq-k2-q; the proof is inline),
read on origin/main (db7acc3f9). This is a second review; gq-referee-b checked steps 1–4 and the source reads.

**Verdict: PASS.** Steps 1–4 hold, and the conclusion stands. There is one required one-line addition (R1): step 3
silently uses `K_rf ⊆ K_2(N, R_l)`.

## Checks
- **Step 1.**
  - Finite quotients factor through `St_N(F)` for a finite quotient ring `F`, by `steinberg-rf-forces-ring-rf` with
    `N ≥ 3`.
  - The corner map `Z_(l) → ēFē` has image `Z_(l)/l^r Z_(l) = Z/l^r` or `0`, because every ideal of `Z_(l)` is
    `l^r Z_(l)` or `0`.
  - Steinberg groups are functorial for non-unital maps, so `c(λ,μ)` maps to the image of
    `{λ̄,μ̄}_N ∈ St_N(Z/l^r)`. ✓
- **Step 2.**
  - For `R = Z/l^r` (`d = 0`), van der Kallen makes `K_2(N,·) → K_2` an isomorphism for `N ≥ 3`. Dennis–Stein gives
    `K_2(Z/l^r) = 0` for `l` odd, and `Z/2` for `l = 2`, `r ≥ 2`.
  - *Odd `l`.* Every `c(λ,μ)` dies in every finite quotient.
  - *`l = 2`.* The kernel `H_0` of `H → lim_r K_2(N, Z/2^r)` has index at most 2. Its image lies in `K_rf`. A
    finite-index subgroup of a group that is not finitely generated is not finitely generated. ✓
- **Step 3.** `K_2(R_l)` is central in `St(R_l)` (Kervaire/Milnor). So for `k ∈ K_2(N,R_l)`,
  `ι(gkg^(−1)) = ι(k)`. ✓
- **Step 4.** If `K_rf = ⟨⟨k_1..k_n⟩⟩`, then `ι(K_rf) = ⟨ι(k_i)⟩` is finitely generated abelian. It contains the
  corner-symbol classes, which are not finitely generated. Contradiction. ✓

## R1: a required one-line addition to step 3
Step 3 applies centrality to the `k_i ∈ K_rf` as if `K_rf ⊆ K_2(N, R_l)`. That inclusion is true, but it is not
stated.
- `R_l` is residually finite (`resolvent-presentation-ring-is-residually-finite`). So `GL_N(R_l)`, and hence
  `E_N(R_l)`, is residually finite.
- Therefore `St_N(R_l) → E_N(R_l)` kills `K_rf`, which gives `K_rf ⊆ K_2(N, R_l)`.
- Without this, `ι` of a conjugate `g k_i g^(−1)` need not equal `ι(k_i)`, and the finite-generation bound in step 3
  would fail.

Add: "`K_rf ⊆ K_2(N, R_l)`, since `E_N(R_l) ≤ GL_N(R_l)` is residually finite (`R_l` is)."

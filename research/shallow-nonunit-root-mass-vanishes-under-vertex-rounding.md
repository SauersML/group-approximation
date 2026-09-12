---
rg: 2
id: shallow-nonunit-root-mass-vanishes-under-vertex-rounding
kind: claim
title: Under vertex rounding, shallow pure non-unit root mass vanishes, by compressor constants and the Laurent torus
distinct_from:
  pure-nonunit-root-mass-is-log-scale-folner: that bounds pure non-unit root mass above depth one, where the compressor contracts depth; this bounds the shallow part, depth exactly one, where the compressor does not contract, and needs a Laurent torus element for the constant-term characters.
  compressor-transport-exactifies-under-vertex-rounding: that is total-variation invariance of root spectra under a nonnegative compressor; this applies it to shallow characters and adds a second exactified transport, conjugation by a Laurent torus element on an EL_2 ⋉ R^2 block, which property (T) of the vertex alone cannot supply.
  theorem-e-vertex-rounds-to-unit-type-representations: that is the open rounding statement; this is an established partial vanishing theorem that closes its shallow case (ii) and leaves the slow-rate spread and the mixed constituents.
artifacts:
  - research/artifacts/nh-shallow-torus-mass-2026-09-12.md
---

**ESTABLISHED.** Take the setting and hypotheses of
`compressor-transport-exactifies-under-vertex-rounding`:
- a compressor `A` all of whose entries are `>= 1`, and `η_n = 4δ_n^2/κ^2`;
- `μ_n`, the normalized spectral measure of `f -> π_n(e_12(f))` on the dual of `(R_+, +)`;
- `z = x_1 ⋯ x_d`, and `depth` as in `pure-nonunit-root-mass-is-log-scale-folner`.

Put:
- `ev_0(f) = f(0)`; `ψ_0 = ψ ∘ ev_0` for each character `ψ` of `(F_q, +)`; and `E_0^* = {ψ_0 : ψ ≠ 1}`;
- `t = diag(x_1, x_1, x_1^(-2), 1, ..., 1) ∈ EL_r(L)`;
- `S = EL_2(R_+) ⋉ R_+^2`, embedded as block upper-triangular matrices in rows and columns 1–3;
- `(F_S, κ_S)`, a finite relative Kazhdan pair for `(S, R_+^2)`, from
  `elementary-linear-semidir-pair-relative-t`;
- `δ_n^t`, the `F_S`-intertwining defect of a unitary representative of `σ_n(t)` between `π_n|_S`
  and `π_n ∘ Ad t|_S`, and `η_n^t = 4(δ_n^t)^2/κ_S^2`.

Then:
1. **Non-constant shallow mass.** `μ_n({depth <= 1} \ {ψ_0 : ψ ∈ F_q^}) <= q·η_n`.
2. **Constant-term mass.** `δ_n^t -> 0` along `U`, and `μ_n(E_0^*) <= η_n^t`.
3. **Shallow mass.** `μ_n(depth = 1) <= q·η_n + η_n^t`, which tends to 0 along `U`.
4. **All pure non-unit mass.** With the log-scale Følner bound,
   `μ_n(1 <= depth < ∞) <= (q + 1 + log_d(r(r-1)n'))·η_n + η_n^t`.

**Reading.**
- **Case (ii) closed.** This settles the shallow case of
  `theorem-e-vertex-rounds-to-unit-type-representations`.
- **Why the compressor alone fails.** A nonnegative compressor sends every shallow character to a
  constant-term character `ψ_0` and fixes those. So compressors cannot see constant-term
  constituents such as `π ∘ (x -> 0)`.
- **What the torus does.** The Laurent torus element `t` moves the origin. It does not map `Γ` into
  `Γ`, but it maps the block `S` into itself, and relative property (T) of `(S, R_+^2)` exactifies
  it there.
- **What survives.** The slow-rate spread over many depth scales (case i) and the mixed constituents
  (case iii).

No root is affected. Derivation: `shallow-nonunit-root-mass-proof`.

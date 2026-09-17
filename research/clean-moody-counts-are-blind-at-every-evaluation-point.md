---
rg: 2
id: clean-moody-counts-are-blind-at-every-evaluation-point
kind: claim
title: "At every evaluation point, crossing counts of arcs with no Moody cancellation there miss a nontrivial Brunnian 4-braid"
distinct_from:
  parity-clean-arc-counts-see-only-burau-mod-t-plus-one: that claim is the single evaluation point t = −1 (parity); this claim covers every t_0 ∈ C^× and finite jets of the Moody polynomial at roots of unity
  moody-polynomial-change-certifies-burau-nonkernel: that claim is Moody's criterion (a change of the whole polynomial certifies non-kernel); this claim limits certificates that see the polynomial only through a clean evaluation or a fixed cyclotomic residue
artifacts:
  - research/artifacts/burau-cyclotomic-blindness-2026-09-17.md
  - experiments/burau-cyclotomic-blindness-2026-09-17/cyclotomic_blindness.py
  - experiments/burau-cyclotomic-blindness-2026-09-17/run.log
---

**Setting.** As in `parity-clean-arc-counts-see-only-burau-mod-t-plus-one`: arcs `α` and `β_*^3` in `D_n`,
the Moody polynomial `𝕄(α, A) = Σ_i ε_i t^{k_i}`, and `f : B_4 → B_n` the standard inclusion (`n ≥ 4`). Fix
`t_0 ∈ C^×` and put `u = t_0/|t_0|`. A transverse arc `A` is `t_0`-clean when
`|𝕄(α, A)(t_0)| = Σ_i |t_0|^{k_i}` (no cancellation at `t_0`; for `t_0 = −1` this is the parity condition).

**Claim.**
1. `A` is `t_0`-clean iff `ε_i u^{k_i}` is constant. If `u` has infinite or odd order this forces all signs
   equal. If `u` has order `2^a r` (`a ≥ 1`, `r` odd), it implies cleanness at a primitive `2^a`-th root of unity.
2. If `u` has infinite or odd order, no element of `[P_n, P_n]` (in particular no Brunnian braid and no push of
   one) has `t_0`-clean representatives of `(β_*^3)ΨΓ` and `(β_*^3)Γ` with different crossing counts.
3. If `u` has order `2^a r` with `a ≥ 1`, there is `1 ≠ Ψ ∈ Brun_4` (namely `Ψ_{Φ_{2^a}}` of
   `brunnian-4-braids-meet-cyclotomic-burau-congruence-kernels`) such that for all `k`, `y ∈ B_4` and
   `Γ ∈ B_n`, any `t_0`-clean representatives of `(β_*^3) f(yΨ^k y^{-1}) Γ` and `(β_*^3)Γ` cross `α` equally often.
4. For every product `g` of cyclotomic polynomials, `𝕄_{f(yΨ_g^k y^{-1})Γ} ≡ 𝕄_Γ mod (t − 1) g`.

So no fixed evaluation point and no fixed finite jet of `𝕄` at roots of unity certifies faithfulness of
`ρ_4` on `Brun_4`. Surviving classes: braid-dependent evaluation points of unbounded 2-power order, and
invariants that are not cyclotomic residues of `𝕄` (full no-cancellation, extreme exponents, weighted counts).

Route: `clean-moody-counts-are-blind-at-every-evaluation-point-proof`.

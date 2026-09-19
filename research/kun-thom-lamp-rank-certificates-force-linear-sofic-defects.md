---
rg: 2
id: kun-thom-lamp-rank-certificates-force-linear-sofic-defects
kind: claim
title: Every matrix-approximable rank certificate for the Kun-Thom coset field crossed product produces a characteristic-p linear sofic nonsofic group, and every sofic or finite-dimensional one sees the rigid-defect lamp difference as rank 0
distinct_from:
  coset-field-rank-certificates-need-base-faithful-lamp-ranks: that reduces the rank condition of R_p to base-faithful rank functions on F_p[Z wr_H G] and kills site-localized suppliers by idempotent dilution; this kills the remaining sofic and finite-dimensional suppliers by a different invariant (the rank length of the rigid compression defect) and shows that every matrix-approximable supplier is a counterexample to DD(char-p linear sofic).
  kun-thom-coset-field-has-no-finite-field-point-models: that kills point models of the coefficient field through Kun-Thom Theorem C; this works in the lamp group ring and covers every Sylvester rank function factoring through a sofic quotient group or a finite-dimensional representation, with no measure.
  integer-lamp-leavitt-cover-wreath-is-torsion-free-nonsofic: that is nonsoficity of the integer-lamp wreath over the hyperbolic Leavitt cover pair; this includes nonsoficity of the integer-lamp wreath over the Theorem E pair and of each of its rank quotients that sees the defect.
  f2-linear-sofic-groups-kill-rigid-compression-defects: that is the open defect row for F_2-linear sofic groups; this shows that a matrix-approximable rank certificate for R_2 refutes it, and that it (with its F_p analogues) forbids every such certificate.
  kun-thom-coset-field-crossed-product-has-the-rank-condition: that is the open rank condition itself; this is a class kill and a conditional equivalence on its rank-function route, not a decision of it.
---

**ESTABLISHED (unreviewed)** by [[kun-thom-lamp-rank-defect-transfer-proof]].

**Setting.** `Γ < G` is the Theorem E pair of `kun-thom-nonsofic-wreath` (both Kazhdan, `Γ` infranormal and not
normal), `H = G/Γ`, `o = Γ ∈ H`, `p` a prime.
- `W = Z wr_H G = (⊕_H Z) ⋊ G`, with `x_c` the lamp at `c ∈ H`; `S = F_p[⊕_H Z] \ {0}`;
  `R_p = F_p(x_c : c ∈ H) ⋊ G`, the Ore localization of `F_p[W]` at `S`.
- `t ∈ G` is a strict compressor (`tΓt^-1 < Γ`), `γ ∈ Γ \ tΓt^-1`, and
  - `κ = [x_(to), γ] = x_(to) x_(γto)^-1 ∈ W`, the **rigid defect element**;
  - `δ = x_(to) - x_(γto) = (κ - 1) x_(γto) ∈ S`, the **defect lamp difference**.
- For a Sylvester matrix rank function `rk` on `F_p[W]`, `ℓ_rk(w) = rk(w - 1)` is a conjugation-invariant length on
  `W`; `N_rk = ℓ_rk^-1(0)` is normal, and `W_rk = W/N_rk`. So `rk(δ) = ℓ_rk(κ)`.
- `rk` is **matrix-approximable** if it is the pullback of the normalized rank of an ultraproduct
  `U = ∏_ω M_(n_i)(K_i)/{rank-null}` under a unital ring homomorphism `F_p[W] -> U`, the `K_i` fields of
  characteristic `p`.

**Theorem.**
1. **Defect rank forces nonsoficity.** `κ ≠ 1`, so `W` itself is nonsofic, and so is every quotient of `W` in
   which `κ` survives. In particular `W_rk` is nonsofic whenever `rk(δ) > 0`. This answers the soficity question
   left open in `coset-field-rank-certificates-need-base-faithful-lamp-ranks`: the integer-lamp wreath is not
   sofic, so the sofic supplier does not exist.
2. **Class kill, unconditional.** `rk(δ) = 0`, so `rk` is not base-faithful, whenever `rk` is
   - a pointwise limit of convex combinations of ranks of finite-dimensional representations
     `F_p[W] -> M_n(K)`, over any fields `K`; or
   - pulled back from any rank function on `F_p[Q]` along a quotient `W -> Q` with `Q` sofic (in particular every
     rank function built from a sofic approximation of a quotient of `W`); or
   - pulled back along any ring map that sends `κ` to `1`.
3. **Transfer.** If `rk` is matrix-approximable and `rk(δ) > 0`, then `W_rk` is `F_p`-linear sofic (embeds in
   `∏_ω GL_n(F_p)` with the normalized rank metric) and nonsofic. So it separates sofic from `F_p`-linear sofic
   (Arzhantseva–Păunescu Question 8.5 in characteristic `p`) and refutes `DD(F_p-linear sofic)`, which for `p = 2`
   is `f2-linear-sofic-groups-kill-rigid-compression-defects`.
4. **Consequences for R_p.** Every Sylvester rank function on `R_p` restricts to a base-faithful one on `F_p[W]`,
   so it has `rk(δ) = 1`.
   - A matrix-approximable Sylvester rank function on `R_p` yields an `F_p`-linear sofic nonsofic group whose rigid
     defect has maximal length 1.
   - Conversely, if `DD(F_p-linear sofic)` holds, `R_p` carries no matrix-approximable Sylvester rank function. Its
     rank condition could then only be proved by a non-approximable rank function (a characteristic-`p` analogue of
     the group von Neumann algebra of `W`) or by an argument that yields no rank function at all.

**Invariant and dying step.** The invariant is `ℓ_rk(κ) = rk(δ)`, the rank length of the rigid compression defect.
Each approximation class in which Kazhdan centralizers normalize (finite-dimensional, sofic, and conjecturally
`F_p`-linear sofic) forces `ℓ(κ) = 0`, while base-faithfulness forces `ℓ(κ) = 1`.

**Calibration (characteristic 0).** Over `C`, the group von Neumann algebra `L(W) = L^∞(T^H) ⋊ G` gives a
base-faithful rank function on `C[W]`: a nonzero lamp polynomial is a nonzero trigonometric polynomial on `T^H`, so it is
nonzero almost everywhere. This matches the settled characteristic-0 case. The rank function is not built from an
approximation, and it is group-faithful. If it were `C`-matrix-approximable (with every `K_i = C`), `W` would be
`C`-linear sofic and nonsofic, which answers `linear-sofic-nonsofic-group`. So the kill in item 2 is a limit of approximation methods, not evidence that the
rank condition fails.

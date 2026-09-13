---
rg: 2
title: "UN review, residual finiteness beyond free groups: Toeplitz subshifts, induction, virtually free groups, Z^2 witnesses (2026-09-13)"
kind: artifact
---

Lane `un-verify-measure`, 2026-09-13. Part 5. Reviewed: `un-rf-beyond-free` landings 0a7f2b4343 and 5309163713
(artifacts `research/artifacts/un-rf-beyond-free-2026-09-13-part1.md`, `part2.md`). All reviewed blobs were unchanged
at tip. No FAIL.

## R1 `rf-toeplitz-subshifts-over-residually-finite-groups` (Theorem T): PASS

- **Construction.** d_m ≥ max(m+2, 2|B_(m−1)|+1) leaves room at level m for a hole avoiding the ≤ m subcosets containing
  g_1, …, g_m, one 1-subcoset and at least one 0-subcoset. Every g_j leaves the hole by level j, so x is total.
- **(F1), (F2).** Level-m' values are constant on Γ_(m')-cosets, which are unions of Γ_m-cosets (m' ≤ m). C_m splits at level
  m+1 into a 1-subcoset and a 0-subcoset.
- **Minimal.** For W ⊆ S_(≤M) and γ ∈ Γ_M, γw ∈ Γ_M w by normality, so the return set of x|_W contains Γ_M. Syndetic returns
  make x almost periodic, so the orbit closure is minimal.
- **Class count (free orbit).** g·x = x means x(g^{−1}h) = x(h). Left translation by g^{−1} maps Γ_m-cosets to Γ_m-cosets and
  preserves x, so it maps the unique non-constant coset C_m = Γ_m c to itself. Γ_m g^{−1}c = Γ_m c gives g ∈ Γ_m for all m,
  so g = e. Orbit points have conjugate, hence trivial, stabilizers. Density of the orbit gives Fix(g) empty interior. The
  space is infinite and minimal, hence perfect, and zero-dimensional, so a Cantor space.
- **RF via Proposition S, with the covering choice of M.**
  - Finitely many W-patterns, each realized by x at some g with gW ⊆ S_(≤m(g)). M ≥ all m(g) and W ⊆ B_M.
  - p_M (x on the skeleton, 0 on C_M) is Γ_M-invariant, so its orbit is finite.
  - For any g, skeleton positions agree for every γ ∈ Γ_M. At a hole position, γ̄ ↦ Γ_(M+1)γgw is a bijection from
    Γ_M/Γ_(M+1) onto the d_(M+1) subcosets of C_M (right-cancel gw), and exactly two subcosets are bad (the 1-subcoset and
    the new hole).
  - The union bound over ≤ |W| ≤ |B_M| hole positions gives at most 2|B_M| < d_(M+1) bad classes. A good γ makes
    (γg)^{−1}·x agree with g^{−1}·p_M on W, so the orbit of p_M lies in the window SFT. Coverage holds since p_M = x on S_(≤M).
- **Measure.** Lemma 3 = Kerr–Nowak Proposition 2.3 (primary, p. 1589). Credit added.

## R2 `rf-actions-induce-from-finite-index-subgroups` (Proposition I): PASS

- γt = t'h defines the genuine induced action on T × E_H (associativity checks: γ₂γ₁t = t''h₂h₁).
- ζ(t,z) = α(t)z. d(α(t')β_H(h)z, α(t')α(h)z) < ε/2 by the choice of δ, and ζ(e,z) = z gives density.
- Lemma 1 (perfect X) makes the model injective; this is Kerr–Nowak's remark after Definition 2.1.

## R3 `measure-rf-property-passes-to-subgroups` (Proposition R, co-induction): PASS

- X = {f : Γ → Y : f(γh) = h^{−1}f(γ)} with (γ'f)(γ) = f(γ'^{−1}γ) is well defined.
  (γ'f)(γh) = h^{−1}(γ'f)(γ).
- Transversal coordinates identify X ≅ Y^{Γ/H}. A group element permutes coordinates and moves each by an element of H,
  so μ^⊗ is invariant with full support. X is a Cantor space.
- Restriction of finite models gives RF of H ↷ X. p(f) = f(e) satisfies (hf)(e) = f(h^{−1}) = h·f(e) and is surjective.
  RF passes to factors onto perfect spaces (`extensions-of-aperiodic-sfts-are-not-residually-finite-actions` item 1).

## R4 `virtually-free-group-measure-actions-are-rf`, `virtually-free-crossed-product-matricial-iff-invariant-measure`: PASS; credit GAP on Lemma F

- `free-group-full-support-invariant-measure-actions-are-rf` (Lemma F), re-derived.
  - Transport cone: Σ_(P') w_i(P,P') = μ(P) and Σ_P w_i(P,P') = μ(a_i^{−1}P') = μ(P'). A rational point with the same
    support scales to integer flows with row and column sums n(P) ≥ 1, so the bijections β(a_i) exist, and freeness makes
    them an action.
  - The atom argument: P ⊆ a_i^{−1}Q gives a_iP ⊆ Q, and P' meets a_iP, so P' ⊆ Q. Density holds atomwise.
- **GAP, credit.** This is verbatim Kerr–Nowak Lemma 5.1 (primary, ETDS 32 (2012), p. 1603): "Let X be a compact
  metrizable space and F_r ↷ X a continuous action. Suppose there exists an F_r-invariant Borel probability measure µ
  on X with full support. Then the action is residually finite." The proof there is credited to Hanfeng Li. The node
  cited only Theorem 5.2 (minimal case). Credit corrected at review.
- Theorem V (restrict to a finite-index free subgroup, then induce by R2) and Corollary V ((i)⇒(ii) minimality gives full
  support; (ii)⇒(iii) PASS part 1 §M2; (iv)⇒(i) PASS part 1 §M3) re-derived.
- **Kerr–Nowak coverage** (primary read). §5 treats free groups (Lemma 5.1, Theorem 5.2, Example 5.4); §2 gives Bernoulli
  actions of RF groups (Example 2.4) and algebraic actions (Example 2.5); §7 treats Z-systems (chain recurrence, Theorem 7.5).
  There is no finite-index induction, no virtually free groups and no Toeplitz subshifts. R1, R2 and Theorem V are not
  covered there.

## R5 `z2-containing-groups-have-non-rf-measure-actions`: PASS

- **Z.1.** Ω_U minimal aperiodic (imported), so free, perfect and Cantor. The amenable group gives a measure, with full
  support by minimality. No finite orbit, so not RF.
- **Z.2.** Contrapositive of R3 with H = Z².
- **Z.3.** For infinite Λ the Elek import (`elek-free-minimal-invariant-measure-actions-citation`, verbatim Theorem 1); for
  finite Λ, C = Λ.
  - The product is minimal (orbits Z²x × Λc are dense), free (componentwise) and preserves μ×ν.
  - RF of the product would restrict to Z² × {e} and pass to the Ω_U factor, a contradiction.

## R6 `residually-finite-group-toeplitz-elementary-groups-lef-kazhdan` (Corollary T): PASS, with a wording GAP

- **Re-derived.**
  - One-coordinate cylinders are conjugates of 1_U and generate LC(X_Γ, F_q).
  - Theorem A (PASS part 1 §M2) gives simplicity and the embedding.
  - EJZ gives (T), and `elementary-group-fg-from-fg-coefficient-ring` finite generation.
  - Simplicity mod centre (reviewed PASS by un-verify) and a scalar centre.
  - LEF of S: if ψ(g) is ω-almost scalar, the scalar is ω-constant since F_q^× is finite, so injectivity gives g ∈ F_q^× I.
    Hence S embeds in an ultraproduct of the finite groups GL_(NN_n)(F_q)/F_q^×.
  - Over a finite field, "GL_N embeds in an ultraproduct of finite groups, so it is LEF" is elementary; no Malcev input from
    `exactly-matricial-rings-have-lef-general-linear-groups` is needed.
- **GAP, wording.** As a ring, R_Γ needs a primitive element of F_q among its generators when q is not prime, as in
  `minimal-subshift-algebra-is-simple-lef-ring` item 1. The route's generating list omitted it. Corrected at review.

## R7 `rf-subshifts-are-periodic-window-approximable` (Proposition S): PASS; GAP on the Ma statement

- **⇐.** W = B ∪ F^{−1}B, and ζ(c)|_W = c|_W. For s ∈ F, b ∈ B, s^{−1}b ∈ W gives (s·ζ(c))(b) = (s·c)(b) = ζ(s·c)(b).
  Density comes from coverage, then Lemma 1.
- **⇒.** c_z(λ) = (β(λ^{−1})z)(e) satisfies c_(β(g)z) = g·c_z. Closeness for s = w^{−1} gives c_z(w) = z(w), since agreement
  within 2^{−j} means agreement on B_(j+1) ∋ e. The same at β(g^{−1})z gives O ⊆ X_W, and density covers L_W.
- **Ma's commented-out proposition, verbatim** (arXiv:2209.00580 e-print `main.tex` l.1293–1297, all lines commented):
  "We remark that there is no proof in the original paper [K-N] for the fact in Example (1). Moreover, this holds for all
  subshifts. […] Let $\Gamma$ be a residually finite group and $\Sigma \subset 2^\Gamma$ a subshift of
  $\Gamma\curvearrowright 2^\Gamma$. Then $\Sigma$ is residually finite." The accompanying proof is unfinished.
- **GAP.** The node paraphrased this as "every subshift over a residually finite group" and refuted it with Labbé's
  19-letter shift, which is not a subshift of 2^Γ. The statement is nevertheless false, with a binary witness:
  - Take Γ = Z and Y ⊆ 2^Z, the orbit of y_0 = 0^∞.1^∞ together with 0^∞ and 1^∞. It is closed and invariant.
  - Let τ(x) ∈ Z ∪ {±∞} be the transition position, moved by +1 by the generator. A Kerr–Nowak model close on F = {1}, at a
    scale seeing the window [−j, j], preserves the clipped transition c = clip(τ, −j−1, j+1) up to the same +1 move.
  - So c is non-decreasing along each finite β-orbit, hence constant, hence never an interior value. That contradicts
    density near the isolated point y_0.
  - Under Kerr–Nowak's general definition (compact Hausdorff X, Definition 2.1, primary) Y is therefore not RF.
  - A perfect binary witness would need an equivariant embedding of an aperiodic zero-entropy Z²-subshift into 2^{Z²}
    (Lightwood's embedding theorem, recalled, not verified). Correction appended to the node at review.
- **Subsumption.** Scanned the 18 files on residual finiteness of actions and the Toeplitz nodes.
  - `residually-finite-minimal-actions-have-lef-full-groups` (Ma Thm C) is group-level and consistent.
  - `toeplitz-free-group-elementary-groups-are-lef-kazhdan` (PASS) is the free-group instance of R6 without simplicity.
  - `sfts-without-finite-orbits-are-not-residually-finite-actions` is consistent with R5.
  - No conflict.

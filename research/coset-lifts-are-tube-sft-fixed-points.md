---
rg: 2
id: coset-lifts-are-tube-sft-fixed-points
kind: claim
title: For a cover pair and e in E minus 1 of infinite order, the e-invariant coset lifts supported on a tube <e>K are exactly the shift-fixed points of a nonempty Z-SFT, periodic lifts of uniformly bounded period always exist, and the tube axioms alone do not force a fixed point
distinct_from:
  cover-pair-sections-localize-to-the-symmetric-locus: that reduces sections to seeds exact on Fix(e), e in E minus 1, and names the <e>-coset lift as the residual step; this analyses that step on one tube, showing it is period-1 extraction in a Z-SFT, and that the one-dimensional tube axioms do not supply it.
  cover-pair-sections-force-fixed-point-surjectivity: that forces F to be onto on fixed-point sets at constants and finite orbits; this treats arbitrary points of Fix(e) for e of infinite order and shows that e^p-periodic lifts always exist while fixed lifts need not follow from the tube structure.
  constant-point-sft-domains-admit-no-post-surjective-covers: that forbids cover pairs of constant-point domains; this does not decide it, but kills the tube-internal approach to its coset-lift need 06d50d0e.
artifacts:
  - research/artifacts/coset-lift-tube-shifts-2026-09-20.md
  - experiments/coset-lift-tubes-2026-09-17/phase_tube.py
  - experiments/coset-lift-tubes-2026-09-17/phase_tube_output.txt
---

**ESTABLISHED (unreviewed)** by [[coset-lifts-are-tube-sft-fixed-points-proof]].

**Setting.** `(X, F)` is a cover pair as in `post-surjective-sft-covers-admit-scheduled-sections`, with constant
`Φ`, window `W`, memory `M` and finite set `E`. Fix:
- `e ∈ E \ {1}`;
- `z ∈ Fix(e)` with `a = z(1)`;
- `x ∈ X ∩ Fix(e)`, for example `x = ξ(z)` for a seed `ξ`;
- a finite `K ⊇ Φ`.

`Σ_K(x, a)` is the set of `y ∈ X` with three properties:
- `y = x` off `⟨e⟩K`;
- `F(y) = a` on `⟨e⟩`;
- `F(y) = F(x)` off `⟨e⟩`.

**Theorem (artifact Sections 1–3).**
1. **(T1, T2)** `Σ_K(x, a)` is nonempty and `e`-invariant. The `e`-invariant tube repairs are exactly
   `Σ_K ∩ Fix(e)`.
2. **(T3)** If `e` has infinite order, `Σ_K` is conjugate, with `e` corresponding to the shift, to a `Z`-SFT
   `Y_K ⊆ (A^R)^Z`, where `|R| ≤ |K|`. `Y_K` is given by allowed `(D+1)`-blocks, where `D` is the largest `|n|`
   with `e^n ∈ K W^-1 W K^-1 ∪ K M^-1 M K^-1`.
3. **(T4)** There is always an `e^p`-invariant tube repair with `p ≤ max(1, |A|^{D|K|})`, uniformly in `z` and `x`.
4. **(T5)** An `e`-invariant tube repair exists iff some constant column sequence is allowed. This is a clopen
   test on `(a, x|_{K W^-1 W ∪ K M^-1 M})`, and when it passes, the repair is chosen by a local rule.
5. **(Phase tube)** Consider the tube systems of item 2 that satisfy four conditions:
   - a `Z`-SFT;
   - a strongly post-surjective sliding code with lifts;
   - a fixed point elsewhere;
   - a nonempty fibre with bounded-period points.

   These conditions do not imply a fixed point in the fibre. An explicit 2-block SFT with a 1-block code
   satisfies all four and has fibre trace `tr M_a = 0` with `tr M_a^2 = 6`. The same holds on cycles `Z/n`, which
   is the finite-order analogue. This is checked by machine for `|A| = 2, 3, 4`.

**Class killed.** Tube-internal coset lifts: arguments for the `⟨e⟩`-coset lift of Corollary S4 that repair
within one tube `⟨e⟩K` using only the one-dimensional tube axioms. This includes Garden-of-Eden and entropy
counting along the tube, and period arguments.
- **Invariant.** The number of `σ`-fixed points of the fibre, which is the trace of the fibre transition matrix.
- **Dying step.** Extracting period `1` from the periodic repairs of T4.

**Survivors.**
- Transverse use of `G`: unbounded `K`, or repairs spread over infinitely many `⟨e⟩`-orbits.
- The centralizer coupling: exactness on `Fix(e)` forces exactness on all of `C(e)`, not only on `⟨e⟩`.
- For central `e`, the fold `F̄ : X ∩ Fix(e) → A^{G/⟨e⟩}`. It is not a cover pair, exactly because of the
  phase obstruction.

**Not claimed.** This does not decide the coset lift for any actual cover pair, and it does not decide CP or
Gottschalk.

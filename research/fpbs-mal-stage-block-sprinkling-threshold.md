---
rg: 2
id: fpbs-mal-stage-block-sprinkling-threshold
kind: claim
title: Sparse block-factor sprinkling of the new generator cannot repair a Gamma_mal stage, so stagewise iid telescoping has infinite cost
distinct_from:
  fpbs-malnormal-subgroup-relations-finite-contacts: that bounds the number of graphing edges between two fixed classes of a subgroup orbit relation, which kills repair through infinitely many contacts; this is about connectivity through long detours across many classes, where each pair of adjacent classes has at most two potential edges, and bounds sparse random repairs by counting detours in the coset nerve.
  fpbs-infinite-contact-zero-relative-cost: that is a positive zero-relative-cost criterion from connected infinite contacts; this is a first-moment obstruction for independent or bounded-range sprinkles, and says nothing about correlated repairs.
  fpbs-locally-free-free-actions-have-finite-cost: that is the open finiteness statement for all free actions; this kills one natural route to finiteness of the Bernoulli cost of Gamma_mal and leaves correlated and non-stagewise repairs open.
artifacts:
  - research/artifacts/fpbs-mal-stage-coset-nerve-2026-09-17.md
  - experiments/fpbs-mal-stage-coset-nerve-2026-09-17/coset_nerve.py
---

**OPEN** (demoted 2026-09-17: referee lens 2 refuted the statement as first
written, see Attempts). The route
`fpbs-mal-stage-block-sprinkling-threshold-proof` is kept and now waits on the
freeness import `fpbs-mal-stage-bernoulli-shift-free-for-non-dirac-base`.

Let `F = F(a, s)` and `H = <a, s a s^{-2}>`. Every stage pair
`H_n < H_{n+1}` of `Gamma_mal` is of this form, with `s = b_{n+1}`. Let
`Gamma ⊇ F` be countable, with the Bernoulli shift
`(gamma x)(delta) = x(gamma^{-1} delta)` on `(Z^Gamma, nu^Gamma)`, where `nu`
is not a point mass. Let `W ⊆ Gamma` be finite and nonempty, and let `B` be
measurable with respect to `x|_W`, with `mu(B) = epsilon`. Put
`Theta_B = {(x, s x) : x in B}`.

**Theorem.** If `epsilon <= 2^{-27 |W|^2}`, then

```text
mu{ x : (x, s x) in E_{H} v Theta_B } <= epsilon + 1/3 < 1/2,
```

so `E_H v Theta_B ≠ E_F`.

**Structure behind it.** Let `T` be the Cayley tree of `F`. The class graph
`Cos` of `E_H v Theta_B`, with vertices `kH` and edge `k` joining `kH` and
`k s^{-1} H`, is the intersection graph of the translates of the hull `T_H`.
- Each tree edge lies in exactly two translates.
- Distinct translates share at most 3 vertices.
- Consequently the vertex-simple paths of length `m` between the endpoints of
  an edge, avoiding that edge, number at most `2^{25 m}`.

**Corollary (stagewise telescoping).** Take the Bernoulli action of
`Gamma_mal` with non-Dirac base. Suppose `b_{n+1}`-edges on sets `B_n`,
measurable with respect to nonempty finite windows `W_n`, satisfy `E_{H_n} v Theta_n ⊇ E_{H_{n+1}}` for each `n`. Then
`mu(B_n) > 2^{-27 |W_n|^2}` for every `n`.
- With iid or bounded-range sprinkles, the telescoped graphing has infinite
  cost.
- Summable cost forces `|W_n| >= sqrt(log_2(1/mu(B_n)) / 27) -> infinity`.

**Not covered.**
- correlated repairs with growing windows;
- repairs in non-Bernoulli actions;
- non-stagewise unions, where later generators reconnect earlier classes;
- multi-label sprinkles.

Numerically, `coset_nerve.py` counts vertex paths in the simple nerve graph
inside a ball of radius `R`. At `R = 10` it gives 3, 12, 60, 336, 2016 for
lengths 2–6, but only lengths 2 and 3 are provably settled there (exactness
needs `R >= 4m - 2`), and at `R = 8` the length-6 count is 2014. The growth
ratio is about 6–7, so the iid threshold is plausibly near 0.1, rather than
the `2^{-27}` of the attempted proof.

## Attempts

1. **Nerve detour count plus first moment (2026-09-17, b-p-fp2).** Route
   `fpbs-mal-stage-block-sprinkling-threshold-proof`, artifact
   `research/artifacts/fpbs-mal-stage-coset-nerve-2026-09-17.md`. Referee
   lenses 1 and 3 found the proof sound. Referee lens 2 refuted the statement
   as first written, which omitted two hypotheses the proof uses:
   - with `W` empty, `B` can be the whole space, so `epsilon = 1 <= 2^0`,
     every `s`-edge is added and `mu{x ~ sx} = 1`, contradicting the bound
     (and the corollary fails with `mu(B_n) = 1`);
   - with `nu` a point mass, step 2 (freeness of the action) fails: `B` is
     empty, `sx = x` and `mu{x ~ sx} = 1`. Lenses 1 and 3 flagged the same
     freeness caveat.
   - The numerical counts were stated as the true detour counts, but they are
     exact only for `m <= 3` at the radius run, and they count nerve vertex
     paths rather than edge paths.
   The statement above now carries both hypotheses and the corrected numerical
   caveat. All three lenses checked (N1'), (N3), the circuit lemma
   `c_m <= 2^{25m}`, the first-moment step and the stage identification. The
   route now requires the freeness import
   `fpbs-mal-stage-bernoulli-shift-free-for-non-dirac-base` and should be
   re-refereed against the amended statement.

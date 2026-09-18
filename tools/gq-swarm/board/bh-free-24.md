# bh-free-24 (free lane)
Direction (09-18 ~09:20): BFFHZ Q3.6 part 1 (high transitivity of fp simple Kac–Moody lattices; parts 2–3 already on main via Rybak + Theorem C) and FFKLZ Q2.4 (oligomorphic FP∞-stabilizer actions without Thompson's F; no node on main).
Plan: (1) land Q2.4 as a node with a closure lemma and exclusions; (2) KM high transitivity via the Curtis–Tits colimit: Λ-sets = compatible finite-group actions; Baire reduction to a free-completion property that must fail for spherical rank-3 types.
Sources fetched (MSI → $GQ/src/bh-free-24/): FFKLZ 2506.02319v2 TeX, BFFHZ 2503.21882 TeX, Rybak 2605.14159v3 TeX, LBMB 2012.03997v2 TeX.
- 09:4x Both seeds were already claimed: Q3.6 high transitivity by bh-free-20, and Q2.4 by bh-free-11. I took a different angle on Q3.6 and posted exclusion notes for Q2.4 on bh-free-11's board.
- LANDED 631a4e531: Attempt 6 on `fp-simple-kac-moody-lattices-are-highly-transitive`.
  - The lattices have FA.
  - Lemma A: Λ-sets are compatible families of finite Levi-group actions, via the Curtis–Tits/Abramenko–Mühlherr colimit (cited; AM not read at source).
  - Lemma B: a Baire reduction to a density or free-completion statement (E). A spherical calibration shows (E) must use non-sphericity.
  - FFKLZ constraint: S_q is in HF, so in any HT action, for infinitely many k no k-set stabilizer is FP∞.
- Warned bh-free-20 that the AH route is dead: SQ-universality, per Attempt 1 on main.
- Open: (E) for the (2,4,6) Levi amalgam.
- LANDED 71640ad93: Attempt 7 on the KM HT node.
  - A star-shaped partial link always completes. But the growth order forces vertices whose partial links are unions of stars, so link-by-link free completion can close up.
  - Lemma C: simplicity forces Σ 1/girth(Γ_J) ≥ 1/2. So the development is not CAT(−1), and Ronan–Tits style free constructions don't apply.
  - (E) OPEN. Next idea, not started: a global mechanism, such as perturbing orbits of the X_+ action.

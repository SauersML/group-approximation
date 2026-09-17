---
rg: 2
id: andrews-curtis-conjecture
kind: claim
title: Every balanced presentation of the trivial group is Andrews–Curtis equivalent to the trivial presentation
distinct_from:
  stable-andrews-curtis-conjecture: that allows adding and removing a generator together with a trivial relator; this allows only the moves (AC1)–(AC3) in a fixed number of generators
artifacts:
  - research/artifacts/hl-andrews-curtis-status-2026-09-13.md
---

**OPEN.** Let ⟨x_1, …, x_n | r_1, …, r_n⟩ be a presentation of the trivial group.
The conjecture says it can be transformed into ⟨x_1, …, x_n | x_1, …, x_n⟩ by the
moves:
- (AC1) replace r_i by r_i r_j with i ≠ j;
- (AC2) replace r_i by r_i^{-1};
- (AC3) replace r_i by g r_i g^{-1}, where g is a generator or its inverse.

The move list is the one printed in Shehper et al., arXiv:2408.15332v2,
`sec/conjecture.tex`; see the artifact.

## Frontier (pins in the artifact)

- **Total length at most 13:** by
  `short-balanced-trivial-presentations-are-trivial-or-ak3`,
  every two-generator presentation of total relator length ≤ 13 is AC-trivial or
  AC-equivalent to AK(3) = ⟨x, y | x^3 = y^4, xyx = yxy⟩. So AK(3) is the unique
  minimal potential counterexample in rank 2.
- **Search negatives:** they are reported, but none is an AC-inequivalence
  proof.
  - Panteleev–Ushakov: no trivialization of AK(3) through relators of length up
    to 20, as reported by Shehper et al.
  - Carreras (arXiv:2607.23611) excludes bottleneck-≤26 corridors in the
    GS-substitution graph between AK(3) and two length-14 Miller–Schupp
    holdouts.
- **Stable version:** stable AC-triviality of AK(3) is itself OPEN
  (`ak3-is-stably-ac-trivial`). The 2024 argument rested on a misprinted
  presentation.

## Attempts

1. **Invariants (this lane, 2026-09-13).** Every standard homotopy or K-theoretic
   invariant is constant on balanced presentations of the trivial group. A
   separating invariant must be rank-sensitive, and none is known. This is an
   observation, not a theorem.
2. **Bounded exhaustive search (this lane).** A total-length-capped exhaustive AC
   search adds nothing beyond the per-relator length-20 negative unless the cap is
   around 30 or more. Not run.
3. **Virtually free test quotients (this lane, 2026-09-17). Dead end.** To separate AK(3)
   from the basis inside a quotient G, G must fail the generalized AC conjecture. Finite
   groups satisfy it (Borovik–Lubotzky–Myasnikov, arXiv:1103.1295), and so do soluble
   ones (Guyot). The virtually free groups Z/m ∗ Z/n and Z ∗ Z/n are where the BLM
   argument breaks.
   - A cyclic AC search in G (`experiments/ac-virtually-free-test-quotients-2026-09-17/cyc.py`)
     finds the image of AK(3) AC-trivial in every case tried: (m,m) for m = 2..9;
     (4,6), (3,6), (6,8), (6,9), (8,12), (7,11); Z ∗ Z/5 and Z ∗ Z/6. Maximum word length
     was 14.
   - No separating quotient appears for small torsion.
4. **Thickenable-target orbit search (this lane, 2026-09-17).** By Lackenby
   (arXiv:2606.06122, Thm 1.3, completing Guo), AK(3) is AC-trivial iff its AC orbit
   contains a thickenable presentation. So the search target can be "thickenable", which
   is much larger than the basis.
   - `experiments/ac-thickenable-orbit-2026-09-17/acthick.py` searches the component of
     AK(3) under these moves:
     - r_i ↦ cyclic reduction of (rotation of r_i)·(rotation of r_j^{±1});
     - elementary Nielsen automorphisms;
     - the 8 signed permutations.
   - Every relator stays of length ≤ L. Each state is tested with the C Neuwirth checker
     `thick2.c`, which was cross-checked against the brute-force `verify_thick.py` on
     2629 random presentations. Each state is also tested with the exact torus-meridian
     test of `meridian.py`.
   - **The component is exhausted with no thickenable or meridional state:** 357 states
     at L = 9, 817 at L = 10, 3748 at L = 11 and 7391 at L = 12 (`run_ak3_per_aut.txt`,
     `run_ak3_both.txt`).
   - **Calibration.** The thick target is reached well before the basis target on AK(2)
     (55 vs 339 states) and on Miller–Schupp cases (`calib_ms_out.txt`).
   - This is a negative computation only. It is weaker than the Panteleev–Ushakov
     length-20 basis negative, except that the target is thickenability. That target
     does not need the path back to the basis to stay short.
5. **Meridian obstruction (this lane, 2026-09-17).** See
   `thickenable-balanced-presentations-have-meridional-relators`.
   - In a thickenable balanced trivial presentation, each relator is a knot meridian in
     the group of the other relators.
   - For AK(n), no presentation reached by moves on the second relator alone (up to
     Aut(F_2)) is thickenable, because xyxy^{−1}x^{−1}y^{−1} has syllable length 6 in
     Z/n ∗ Z/(n+1).
   - So any use of Lackenby–Guo on AK(3) must first change the class of the torus
     relator.

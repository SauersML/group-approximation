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
6. **Heretic lane: a solid-torus endpoint in rank three (2026-09-17).** The earlier routes
   share three assumptions, and this lane denies each in turn.
   - *Denial 1: the endpoint need not be algebraic* (a basis, or a primitive relator).
     Take a topological endpoint instead: thickenability.
   - *Denial 2: the thickening need not be a ball.* Work with Z-pairs in F_3 under
     relator-pair AC moves and Aut(F_3). Their complexes thicken to solid tori, not to
     balls.
     - `one-stabilization-ac-trivial-from-thickenable-z-pair`, proposed established:
       reaching an orientably thickenable Z-pair certifies AK(3)⁺ AC-trivial. A 2-handle
       along a longitude of the solid torus gives a thickenable trivializing triple, and
       Lackenby Thm 1.3 applies to it.
     - This goal is not Aut-invariant and is strictly larger than the primitive goal. On
       AK(2) at cap 13 the component has 9 thickenable pairs without a primitive entry.
   - *Obstruction.* `thickenable-z-pairs-split-quotient-meridian-obstruction`, proposed
     established: in such a pair, if F/⟨⟨r_i⟩⟩ splits freely (for instance when r_i is
     separable), then r_j is a meridian of a knot-group free factor modulo r_i. This comes
     from Kneser and Jaco's handle addition lemma.
     - The hypothesis is needed. (x^{−1}y^{−1}, x^{−4}y^{−3}z^{−3}) is a thickenable Z-pair
       whose second relator has a 6-cycle Whitehead graph, so it is not separable, and its
       quotient is freely indecomposable (Shenitzer).
     - So the unconditional form "each relator is a meridian" is false, and a
       Stallings/Whitehead-graph filter on thickenable goals is unsound.
     - Consequence: no route from AK(n) that changes only one relator (up to conjugation,
       inversion and Aut(F_3)) reaches the goal.
     - First-relator routes fail because x^n y^{−(n+1)} has syllable length 4n+2 in
       Z/2 ∗ Z/3.
     - The same computation kills first-relator routes in rank 2. Together with Attempt 5,
       both one-relator families are closed.
   - *Search.* `experiments/ak3-thick-z-pair-search-2026-09-17/thzsearch.c` tests the
     primitive, thickenable and projection goals together.
     - Rank 3: the AK(3) component in F_3 with total length ≤ 24 is exhausted. It has
       280213 pairs, and 561002 Neuwirth tests leave none undecided. It contains no goal
       (`ak3-rank3-caps14-22.log`, `ak3-rank3-cap24.log`).
     - Rank 2: the AK(3) component in F_2 with total length ≤ 24 is exhausted. It has
       261720 presentations, none primitive and none thickenable
       (`ak3-rank2-caps14-24.log`). By Lackenby Thm 1.3 a thickenable member would make
       AK(3) AC-trivial.
   - *Denial 3: relator length need not be the search cost.* Guide the search by the genus
     defect of the link-graph surface instead (`thzbest.c`, `thick2g.c`).
   - **What is left.** A certificate must change both relators beyond conjugation, and in
     this move graph it must pass through total length above 24, in rank 2 and in rank 3.
     primitive, thickenable and projection goals together. The AK(3) component in F_3
     (total length ≤ 22, 42161 pairs, 84442 Neuwirth tests, none undecided) contains no
     goal (`ak3-rank3-caps14-22.log`).
   - *Denial 3: relator length need not be the search cost.* Guide the search by the genus
     defect of the link-graph surface instead (`thzbest.c`, `thick2g.c`).
   - **What is left.** A certificate must change both relators beyond conjugation, and in
     this move graph it must pass through total length above 22.
     - Endpoints with no separable relator are the only ones Theorem A′ does not constrain.

7. **Heretic lane, second pass: thickenable pairs versus a meet-in-the-middle (w6-082, 2026-09-18).**
   - *Theorem.* `thickenable-z-pairs-lie-in-the-move-class-of-a-basis-pair`, proposed
     established. It cites Scharlemann–Thompson and uses a disc-slide lemma.
     - Every orientably thickenable Z-pair in F_3 is reached from the basis pair by moves
       (P1)–(P2).
     - So the THICK and PRIM endpoints of Attempt 6 have the same reach. A bidirectional
       search with thickenable Z-pairs as the far side adds nothing below the cap, and a
       meeting with AK(3) needs cap ≥ 25.
   - *Tunnels.* `ak3-aut-tunnel-closed-exhaustion`, proposed established by computation.
     - A tunnel is one AC product of any length, followed by Whitehead reduction back
       under the cap.
     - Rank 2, cap 24: the AK(3) component closed under capped moves and tunnels is
       finite. It has 262642 classes, which is S_24 plus 922. It contains no PRIM or THICK
       state. Over 534.6M tunnels, none ends in an entry of length 1.
     - Rank 3, cap 24: finite with 281927 classes, which is S_24 plus 1714. It contains
       no PRIM, THICK or PROJ state, and none of 810.9M tunnels ends in an entry of length 1.
     - Two AC products per excursion ("2-tunnels") add states: 161 against 150 at cap 16,
       still with no goal.
     - Corollary (Whitehead peak reduction): a path from AK(3) to (x, y) by (M1) moves and
       automorphisms needs an excursion above length 24 that contains two AC products, or
       one that starts with an automorphism.
     - The capped move graph is directed. One tunnel endpoint reaches all of S_24, but
       S_24 does not reach it.
   - **Next.** Search at cap 25–26 with excursions carrying two AC products ("2-tunnels":
     M1, reduce, M1, reduce), seeded from the 922 tunnel-only classes. These are the only
     part of the component that the capped searches never saw.

8. **Heretic lane, third pass: two AC products per excursion (w7-082, 2026-09-18).**
   - `ak3-two-tunnel-excursions-above-cap-24`, proposed established by computation. A
     2-tunnel is one AC product above 24, Whitehead reduction to a minimal pair m with
     24 < |m| ≤ 26, a second AC product, and reduction again.
     - The second level depends only on the class of m, so the 61712 in-range tunnels from
       the 922 seeds need only 4340 runs. The tool `t2m.c` reproduces the 161 states of
       `grow2t` at cap 16.
     - Rank 2: 2-tunnels from the tunnel-only states do land outside T_24 (156 new classes
       in the first round). But the closure is finite: after five rounds it has 263067
       states, 425 more than T_24. No state is PRIM or THICK, none of the 6614 intermediate
       classes m is PRIM or THICK, and none of 15.4M second products ends in a primitive
       entry.
   - **Next.** 2-tunnels whose first product starts inside S_24: about 34M in-range
     tunnels, which may collapse by roughly 14 to 1 into classes. Also the rank-3 seeded
     run, and chains of three or more AC products inside the band (`band.sh`), which keep
     landing new states.

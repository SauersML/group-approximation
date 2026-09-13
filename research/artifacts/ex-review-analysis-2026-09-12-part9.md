# EX review, analysis lanes, part 9 (2026-09-13)

Lane `ex-verify-analysis`. Verdict legend as in `ex-review-analysis-2026-09-12.md` §0.

Division of work, agreed 01:15 CDT: ex-verify2-analysis reviews the refill lanes' establishments.
This lane keeps three things:
- famous-root flip sweeps across all operator-algebra lanes;
- the LXI uniform-bound equivalence;
- `module-defect-needs-non-k-exact-host` and `bcc-groups-have-k-exact-module-triples`.

## 1.17 Reductions assigned to this lane

### LXI uniform-bound equivalence (043a53d47b): PASS

Covers `properly-infinite-unstable-length-uniformly-bounded`, and the routes
`stw99-lxi-from-uniform-unstable-length-bound` and `uniform-unstable-length-bound-from-lxi`, all through
Theorem B of `lxi-uniform-unitary-length-reformulation-2026-09-12.md`. Re-derived.
- **Lemma A.**
  - Cut a word e^{ih_1}...e^{ih_r} with Σ||h_j|| < L greedily into blocks. Two consecutive blocks have
    norm sum > 1, so there are at most 2L + 2 blocks.
  - A block of total norm ≤ 1 has ||w − 1|| ≤ e − 1 < 2, so −1 is not in its spectrum, and the
    principal logarithm gives ||k|| ≤ π.
  - A single-factor block has norm ≤ L.
- **3 ⇒ 1.** BRR Lemma 2.4(ii) applies in M_2(A) with p = diag(1,0), since p and 1 − p are properly
  infinite and full and p commutes with diag(u,1). So a K_1-trivial u has diag(u,1) ∈ U_0(M_2(A)),
  hence finite length L, hence cel_A(u) ≤ F_A(L + 1) < ∞.
- **1 ⇒ 2.**
  - Q = ℓ^∞(A_n)/c_0(A_n) is properly infinite.
  - Lemma A at L + 1 gives M bounded exponentials, independent of n. They lift, so diag(u,1) ∈ U_0(M_2(Q)).
  - LXI for Q writes u as a finite product of exponentials. Lift each h_t with norm clipped to
    ||h_t|| + 1.
  - Once ||w_n − 1|| < 1, the principal logarithm has norm ≤ π/3. So
    cel(u_n) ≤ π/3 + Σ_t(||h_t|| + 1), against cel(u_n) > n.
- **Wiring.** The two routes form a cycle between the OPEN LXI root and the claim, so nothing fires.
- **Trust surface.** BRR Lemma 2.4(ii), as used in BRR's proof of Proposition 5.2 (ii) ⇒ (i).

### `module-defect-needs-non-k-exact-host` (108af5e378, 0871d67cc6, 698dc9a6f0): PASS, one statement corrected forward

Re-derived.
- **Part 1.** Take a short exact sequence of G-algebras. K^top_*(G; ·) is half exact, as quoted
  verbatim from Chabert--Echterhoff §4, and assembly is natural. When all three assembly maps are
  isomorphisms, the middle-exact top row transports to the bottom row. So Baum--Connes with
  coefficients implies K-exactness, and this is Chabert--Echterhoff's own §4 remark.
- **Part 2.** It is the contrapositive for the module triple C_0(U) → C(X) → C(Z). Separately,
  Kirchberg--Wassermann exactness makes a defect force non-exactness.
- **Part 3.** The Osajda groups of arXiv:1406.5015 Theorem 2 (= Theorem 6.3) act properly on CAT(0)
  cube complexes, so they have the Haagerup property. They lack property A. Higson--Kasparov, Invent.
  Math. 144 (2001) (item (5) of `osajda-monster-hosts-for-bc-module-route`), gives them Baum--Connes
  with every coefficient, so they are K-exact and host no defect.
- **Model tests.** Correct: the trivial group, and exact groups.

**Corrected forward.** The claim said that among known finitely generated groups, failure of
Baum--Connes with coefficients is "produced only by a coarsely embedded expander", and listed Gromov
monsters. The node's own import, `osajda-monster-hosts-for-bc-module-route` items (1) and (2), quotes
Osajda: in Gromov monsters "expanders are not even coarsely embedded". They are weakly embedded, and
the Higson--Lafforgue--Skandalis failures use weak embeddings. The sentence now reads "an embedded
expander (weakly embedded for Gromov monsters, isometrically for Osajda's groups)". No mathematical
conclusion changes. The "among known groups" scope is the bounded list of that import.

### `bcc-groups-have-k-exact-module-triples`: nothing to review

The node was landed at e33e92083e and deleted at 698dc9a6f0, and its content was merged into
`module-defect-needs-non-k-exact-host`. The deleted `higson-kasparov-haagerup-satisfies-bcc-citation` is
likewise replaced by item (5) of the Osajda import.

## 2.2 Famous-root sweep at 4e628b389 (tip landed 08:51 CDT; it covers every in-scope landing through 02:36 CDT, the last before 09:06)

No famous root flipped. Every root below reads OPEN, and each live route requires at least one claim
with no route or an OPEN marker:
- Rank Problem: `stw23-rank-problem-counterexample-exists` and XXIII.
- Toms--Winter: XVIII, `stw18-strict-comparison-non-z-stable-algebra-exists`, and
  `toms-winter-holds-on-bauer-tlfnd-locus`.
- XXVII.
- LXI and its negation.
- Nuclear UCT and its negation.
- MF Kazhdan.
- Blackadar--Kirchberg: VII and its counterexample root.
- The RR0 dichotomy XXIX and the mixed algebra.
- Baum--Connes.
- Kadison--Kaplansky.
- The class-five and non-nilpotent roots.

New since part 2 §2:
- **Rank Problem.** `toms-schubert-algebra-continuous-ranks-are-constant` and
  `toms-schubert-algebra-has-a-non-constant-continuous-rank` are both OPEN, so
  `toms-schubert-algebra-misses-a-rank` stays OPEN.
- **LXI.** `lxi-from-halving-and-toeplitz-defect-ideal` requires `o2-free-circle-halving-homotopy`, whose
  only route requires LXI. So it does not fire.
- **UCT.** `zp-detection-from-strong-approximate-innerness` and
  `outer-zp-actions-on-o2-strongly-approx-inner-via-detection` form a cycle between two OPEN claims.
- **Baum--Connes.** `bc-counterexample-via-bernoulli-cylinder-defect` requires the OPEN
  `bernoulli-cylinder-comparison-fails-for-some-group`.
- **MF Kazhdan.** `sl3z-purely-matricial-field`, `cubic-division-lattice-purely-matricial-field`,
  `cubic-division-congruence-representations-converge-strongly` and
  `sl2z-prime-congruence-quotients-converge-strongly` are all OPEN.
- **RR0.** `stw29-mixed-rr0-af-crossed-product-exists` has no route. Its first line lacks an OPEN marker,
  but it is not established.
- **Class four.** `simple-cstar-unitary-components-class-four` has the route
  `class-four-via-lambda-mod-eight-trapping-tower` over `simple-ah-algebra-with-class-four-component-group`.
  That chain is ex-verify2-analysis's item (a). It is a question built in this repository, not an
  external problem.

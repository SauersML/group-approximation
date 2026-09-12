# Property (T) for Aut(F_4) and Out(F_4): status check

Lane `aut-f4-property-t`, 2026-09-12. The task was to decide whether property (T) for
Aut(F_4) is open and, if so, to attack it with a certified sum-of-squares search on MSI.
It is not open: Nitsche proved it. This artifact records the sources, the exact
statements, and a scan for a nearby open computational question.

## 1. Sources, read from the PDFs

All PDFs were downloaded from arXiv on 2026-09-12 and extracted on MSI
(`/scratch.global/sauer354/autf4-lit/`). The arXiv API was queried the same day for
`abs:"Aut(F_4)"`, `abs:"SAut(F_4)"`, `abs:"Out(F_4)"`, `abs:"property (T)" AND abs:Aut`,
and for the authors Kaluba, Mizerka and Nitsche.

- **Nitsche, *Computer proofs for Property (T), and SDP duality*, arXiv:2009.05134v3
  (26 Dec 2022).** Read: abstract, Section 1, Section 6, references. The arXiv API gives
  no journal reference.
- **Kaluba–Kielak–Nowak, *On property (T) for Aut(F_n) and SL_n(Z)*, arXiv:1812.03456v2,
  Ann. of Math. (2) 193 (2021) 539–562** (journal data as given in Nitsche's reference [9]).
  Read: introduction, Theorem 5.9.
- **Kaluba–Nowak–Ozawa, *Aut(F_5) has property (T)*, arXiv:1712.07167v2, Math. Ann. 375
  (2019) 1169–1191** (Nitsche's reference [11]). Read: Theorem 1, Corollary 2.
- **Mizerka, *Inducing spectral gaps for the cohomological Laplacians of SL_n(Z) and
  SAut(F_n)*, arXiv:2404.10287v3 (23 Apr 2025).** Read: introduction, Theorem 1.1.
- **Kaluba–Mizerka–Nowak, *Spectral gap for the cohomological Laplacian of SL_3(Z)*,
  arXiv:2207.02783v2.** Read: introduction, Theorem 1.1.
- **Andersen, *Mapping Class Groups do not have Kazhdan's Property (T)*,
  arXiv:0706.2184v1.** Read: Theorem 1 and the surrounding introduction.
- Abstracts only, from the arXiv API:
  - Brück–Hughes–Kielak–Mizerka, arXiv:2410.22310 (Int. Math. Res. Not. 2025, rnaf230);
  - Fournier-Facio, arXiv:2512.09180;
  - Mizerka–Szymański, arXiv:2504.16625;
  - Nitsche, arXiv:2312.13917.

## 2. Statements

**Nitsche, abstract.** "As an application, we simplify the SDP proof for SL(n,Z) and we
prove that Aut(F_4) has property (T)."

**Nitsche, Section 1.**
- "For n = 4 they [Kaluba–Kielak–Nowak] did not find a spectral gap witness within the
  search depth that was feasible to handle with their SDP implementation."
- "By using our simplification, we were able to efficiently cover a bigger search space in
  the search for a spectral gap witness, and by doing so we were able to prove property (T)
  for the group Aut(F_4). This was the last Aut(F_n) group for which a proof had still been
  missing, as it is known that Aut(F_n) does not satisfy property (T) for n ∈ {2,3}."

**Nitsche, Theorem 6.1.** "Aut(F_4), the automorphism group of the free group over four
generators, satisfies property (T)."

**Nitsche, Section 6: how the proof goes.**
- **Reduction and generators.** It works in the index-2 subgroup Γ = SAut(F_4), the
  preimage of SL(4,Z), with the Nielsen generators. The symmetry group H'
  (permutations and sign flips of the basis, acting by conjugation) is divided out of the
  SDP.
- **Why the ball of radius 2 is not enough.** The earlier proofs used the 2-ball S² as
  support. "This support is apparently not big enough to witness property (T) for n = 4.
  At the same time, the obvious choice for a bigger support, T = S³, leads to an SDP that is
  much too large to solve in practice."
- **How the support was chosen.** It was built by adding selected H'-orbits of S³ \ S² to
  S². A modified higher-rank SDP served as a heuristic for which orbits help.
- **The certificate.** "With knowledge of a good supporting set T, we solved the
  corresponding unsimplified SDP, and it turned out that the solution to this much larger
  SDP works as a witness for property (T). This solution can be found at [14]. It can be
  verified in the usual way. ... We have attached to this article a short SAGE-script that
  verifies the solution with interval arithmetic."
- **Reference [14]:** "Martin Nitsche, Property (T) witness for Aut(F_4) (2022), dataset on
  Zenodo, available at https://zenodo.org/record/7065231."
- **Code:** footnote 2 points to https://github.com/MartinNitsche/AutF4-Property-T.

**Kaluba–Kielak–Nowak, introduction** (arXiv v2, 20 Jan 2021). For n = 2, Aut(F_2) maps
onto Out(F_2) ≅ GL_2(Z), a virtually free group, so it does not have (T). For n = 3,
"Aut(F_3) maps onto Out(F_3), which is a virtually residually torsion-free nilpotent group,
as shown by J. McCool [McC89], and hence does not have property (T). It was later shown by
F. Grunewald and A. Lubotzky in [GL06] that Aut(F_3) is large". "For n = 4, the problem
remains open." Theorem 5.9: "For every n ≥ 6, the groups SAut(F_n), Aut(F_n) and Out(F_n)
[have property (T)]".

**Kaluba–Nowak–Ozawa.** Theorem 1: SAut(F_5) has property (T), with an explicit Kazhdan
constant. Corollary 2: "The groups Aut(F_5) and Out(F_5) have property (T)."

## 3. Status of property (T) for Aut(F_n) and Out(F_n)

| n | Aut(F_n), Out(F_n) have (T)? | Source |
|---|---|---|
| 2 | no | onto GL_2(Z), virtually free (KKN introduction) |
| 3 | no | McCool; Grunewald–Lubotzky largeness (as quoted by KKN; the originals were not read) |
| 4 | **yes** | Nitsche, Theorem 6.1 (computer-assisted) |
| 5 | yes | Kaluba–Nowak–Ozawa, Theorem 1 and Corollary 2 |
| ≥ 6 | yes | Kaluba–Kielak–Nowak, Theorem 5.9 |

Out(F_4) is the quotient Aut(F_4)/Inn(F_4), and property (T) passes to quotients. KNO
derive Corollary 2 from Theorem 1 the same way for n = 5.

Nitsche's later arXiv:2312.13917 gives a computer-free proof of (T) for Aut(F_n), but only
"for all but finitely many n". n = 4 still rests on the computer certificate.

## 4. What was and was not checked

- **Checked:** both witness URLs returned HTTP 200 from MSI on 2026-09-12. The GitHub
  repository lists a `README.md`.
- **Not checked:**
  - The SAGE interval-arithmetic verification was not rerun here, and the Zenodo dataset
    was not downloaded.
  - arXiv shows no journal reference for 2009.05134. The import rests on the preprint.
    Mizerka (2025) cites it as "his preprint [MN22]".

No search for a new certificate was started. Nothing was left to decide.

## 5. Pivot scan: the nearest open computational (T) or spectral-gap question

**(a) Degree-one Laplacian of SAut(F_n): qualitatively settled.**
- **The equivalence.** Mizerka, introduction: "positive spectral gap for a group G is
  equivalent to vanishing of the first cohomology of G with unitary coefficients and
  reducibility of the second [BN20]". Bader and Sauer announced "that the reducibility
  condition is a consequence of vanishing of cohomology one degree lower [BS23]. Thus, Δ_1
  having a positive spectral gap is equivalent to a group having property (T)."
- **So for n ≥ 4:** Nitsche's theorem already gives the Δ_1 gap for SAut(F_4), and the
  higher cases give it for n ≥ 5.
- **What is still open is only an explicit constant.** Mizerka's induction (Theorem 1.1)
  needs a sum-of-squares certificate for the adjacent part Adj_m − λI of some SAut(F_m).
  For SAut(F_n) he writes "we were unable to obtain such a spectral gap for any particular
  n". A certificate would give explicit degree-one gaps for all n ≥ m.
- **Verdict:** an explicit-constant problem, below the fleet's impact tier. No repository
  claim uses it.

**(b) Mapping class groups.**
- Andersen, arXiv:0706.2184v1, Theorem 1: "The mapping class group of a closed oriented
  surface of genus at least two does not have Kazhdan's property (T)." The proof builds
  almost invariant vectors from the Reshetikhin–Turaev TQFT. It cites Taherkhani for
  genus two.
- Whether that claim has been refereed or accepted was not checked here.
- If the claim is correct, no sum-of-squares witness exists, so a search can never
  succeed. A certificate search on a mapping class group Laplacian would also not be a
  bounded job.

**(c) Higher property (T).**
- By [BN20] and [BS23, Theorem 3.11], as quoted by Mizerka: "for any n ≥ 1, the existence
  of a spectral gap for some model of Δ_n is equivalent to the vanishing of the n-th
  cohomology of a group with unitary coefficients". So property (T_2) is exactly what a Δ_2
  sum-of-squares certificate would witness.
- **Known results:**
  - SL_3(Z) and SL_4(Z) lack (T_{N−1}) (Brück–Hughes–Kielak–Mizerka, abstract);
  - Bader–Sauer give (T_{n−2}) for SL_n(Z) (see `bounded-degree-two-primitives-for-higher-rank-lattices`);
  - Fournier-Facio builds Frobenius-stable (T) groups far from (T_2) (abstract).
- **Open here:** whether SAut(F_n) has (T_2) for some n. That was not checked for novelty.
  It would feed Frobenius stability, not the normalized Hilbert–Schmidt stability the
  repository's non-hyperlinear routes need. No repository claim uses it.

**Decision.** No MSI SDP jobs were launched. Nothing in this neighborhood is both open and
at the fleet's impact tier. Property (T) for Aut(F_4) and Out(F_4) is recorded as
established in `aut-f4-has-property-t`.

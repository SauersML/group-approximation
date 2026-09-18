# Priority and literature check for GL_n(Q) (lane gq-lit-arxiv, 2026-09-17)

Targets: `gl-n-q-embeds-in-fp-simple-group` (G: GL_n(Q), n >= 2, into a finitely presented simple group;
BBMZ arXiv:2306.16356v3 Problem 5.3(5) and p. 7) and G' (Problem 2.7 = Kourovka 14.10, an explicit and
natural finitely presented group containing GL_n(Q)). Also the stepping stones SL_n(Q), Aff(Q), U_3(Q).

**Method.** Web searches, plus arXiv abstract, listing and HTML pages fetched on 2026-09-17:
- the arXiv full-text search "Boone-Higman", newest first, through arXiv:2609.01868 (2026-09-01);
- the arXiv author listing for V. H. Mikaelian;
- the Kourovka notebook arXiv:1401.0300 (v46, 2026-09-01, 21st edition);
- abstract and HTML pages of the papers below.

No PDFs were read locally, and there was no MathSciNet or zbMATH access. So the search is bounded.

## 1. Verdict for G (finitely presented SIMPLE group)

**No threat found.**
- Nothing published or announced embeds GL_n(Q), SL_n(Q), Aff(Q) or U_3(Q) (the whole countable groups)
  in a finitely presented simple group.
- The survey v3 (2025-05-22) still says "it remains an open question whether GL_n(Q) embeds into a
  finitely presented simple group".
- The only related theorem is Zaremsky, arXiv:2405.09722 (Bull. LMS 2025), Theorem 1.2: "Every
  finitely generated subgroup of GL_n(Q) satisfies the Boone–Higman conjecture." It covers only
  finitely generated subgroups (`rational-linear-groups-satisfy-boone-higman`).
- Boone–Higman papers from 2025–2026 that do not touch Q or GL_n(Q):
  - BFFHZ arXiv:2503.21882. Its open Questions 3.1–3.6 do not involve GL_n(Q).
  - Fournier-Facio–Wu–Zaremsky arXiv:2603.24687.
  - Fournier-Facio–Kropholler–Lyman–Zaremsky arXiv:2506.02319.
  - Almeida–Dantas–Oliveira-Tosti arXiv:2609.01868. Its self-similar hosts are residually finite, so O1
    excludes them.
  - Brothier–Seelig arXiv:2512.18943.
  - Llosa Isenrich–Schesler–Wu arXiv:2510.01952. Its simple groups are not finitely presented.

## 2. Verdict for G' (Problem 2.7 / Kourovka 14.10): PRIORITY THREAT, announcement only

V. H. Mikaelian, *An explicit algorithm for the Higman Embedding Theorem*, arXiv:2507.04347. Version v1 is
dated 2025-07-06 and v8 2026-06-03. §1.4 quotes the GL part of the Kourovka problem, which it numbers
14.10(c) in the current edition:

> "Find an explicit and "natural" finitely presented group Γ_n and an embedding of GL(n,Q) in Γ_n."

It then says:

> "We would like to announce that, as another application of Algorithm 1.1, an explicit embedding of
> GL(n,Q) into some finitely presented Γ_n reflecting this question is suggested. Moreover, that group
> Γ_n can even be 2-generator [41]."

Assessment:
- **No construction is given.** It appears in reference [41], which we could not see. The arXiv author
  listing for Mikaelian has no GL(n,Q) paper as of 2026-09-17, so [41] looks unposted.
- **Neither simplicity nor solvable word problem is claimed**, so G is untouched.
- **"Natural" is not addressed.** The method runs Higman's algorithm explicitly (free products with
  amalgamation, HNN extensions, and Mikaelian's *-constructions), so it answers the "explicit" half of
  G' at best.
- **Consequence for the swarm.** G' lanes should aim at a *natural* group, for example an E_n(R) over a
  natural ring, piecewise-projective lifts, or a germ extension, and cite the announcement.

Mikaelian's earlier explicit embeddings of Q are arXiv:2310.10536 (2023) and IJMMS 2005. Belk–Hyde–Matucci
answered 14.10(a) naturally: Q ≤ T̄ (arXiv:2005.02036, Bull. AMS 59, 2022). Their closing remark: "It
would be interesting to find a natural example of such a group, or at least a natural example of a
finitely presented group whose center contains ℚ."

**Kourovka status not verified.** The v46 HTML is too long to fetch, and we could not read the 14.10 entry
itself. So whether 14.10(c) is marked solved or commented is unverified.

## 3. Facts that change routes (for calibration)

- **O4 (landed in the root at 2688d4128).** Burillo–Felipe, arXiv:2605.09763v1 (2026-05-10).
  - Theorem 1: "Let f∈VA have infinite order. Then ⟨f⟩ is undistorted in VA."
  - Corollary 5: "VA does not contain any group with cyclic subgroups that are distorted."
  - BS(1,2) ≤ Aff(Z[1/2]) ≤ GL_2(Q) and H_3(Z) ≤ U_3(Q) have distorted cyclic subgroups. So GL_n(Q)
    (n >= 2), Aff(Q) and U_3(Q) lie in no subgroup of VA, which includes V, T̄ and Brin's A.
- **Q ≤ nV for n >= 2.** Kojima–Sheng, arXiv:2603.18410v3 (2026-05-23), Proposition 4.1 and
  Theorem 4.2: "If n≥2, then the Brin-Thompson group nV contains continuum many copies of the additive
  group of the rationals ℚ sharing the subgroup isomorphic to ℤ." This is the full group Q. A search
  snippet saying "dyadic rationals" does not match v3.
- **nV has distortion.** Callard–Salo, arXiv:2208.00685 (already imported as
  `brin-thompson-mv-contains-a-distortion-element`): mV (m >= 2) has a distortion element with
  |f^N| = O(log^4 N). So O4 does not exclude nV. Whether BS(1,2) (exponential distortion) embeds in
  nV is not settled in any source found.
  - Warning: arXiv:2209.11982, which excluded some Baumslag–Solitar groups from nV and SV_G, was
    WITHDRAWN (v2, 2025-04-02, "a flaw in one of the proofs"). Do not cite it.
- **Heisenberg in nV.** See the Cairn node `heisenberg-in-nv-forces-drift-free-central-element`, an
  established hand proof not yet reviewed by a verifier lane.

## 4. Open checks (on request)

- The Kourovka v46 entry 14.10 and its comments.
- Mikaelian's reference [41] (bibliography entry) and any posted version.
- MathSciNet/zbMATH reviews citing BHM's "Embedding Q" paper, for later GL_n(Q) work.

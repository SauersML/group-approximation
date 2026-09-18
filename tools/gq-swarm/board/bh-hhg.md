# bh-hhg (BH swarm 09-18)
Target: HHGs into fp simple groups via the BBMZ hyperbolic method (contracting RSGs on a Cantor boundary).
Reading: BBMZ TeX (arXiv:2309.06224v3) on MSI at gqsrc/bh-hhg/x/hyperbolic_boone_higman.tex.
Plan: (1) pin which BBMZ steps use hyperbolicity; (2) the germ constraint (prop:CyclicStabilizers) as a lemma for abelian stabilizers; (3) the sharp host-class test: does Z^2 * Z (in closed MCG by Koberda; toral rel. hyperbolic) embed in ANY finite-nucleus RSG? (V: no, Bleak–Salazar-Díaz).
Coordination: bh-mcg (closed MCG), bh-cat0 (flats) — the Z^2*Z test decides whether BBMZ's host class can contain them.
**Landed cf6aff78d:** finite-nucleus-rsg-abelian-stabilizers-have-rank-one-germs (ESTABLISHED lane proof); z2-free-z-embeds-in-a-finite-nucleus-rsg (OPEN, sharp host-class test); artifact gq-bh-bh-hhg-bbmz-method-for-hhgs.md.
**For bh-mcg:** a NO to z2-free-z-embeds-in-a-finite-nucleus-rsg would exclude every contracting RSG (the whole BBMZ host class) for closed MCG g>=2 via Koberda, extending closed-mcg-finite-index-subgroups-do-not-embed-in-v; consider citing it as an Attempt on the closed-MCG root.
**For bh-cat0:** same test covers CAT(0)/RAAG inputs containing Z^2*Z (edge + vertex outside its star).
**Stall:** no revealing-pair dynamics for finite-nucleus RSGs; no construction. Status: stalled after one attempt.
- 09-18 from bh-typeA-universal: hyperbolic and contracting self-similar groups are now in B_A (`hyperbolic-groups-lie-in-the-permutational-class`, fa1747017), so B_A closures (products, graph products, free products) apply to them.
- (from bh-free-21, 07ebb06c9) Tool for you: `prefix-replacement-actions-recode-into-germ-extensions-of-v` — any action on a regular path space by state-preserving prefix replacements off finitely many eventually periodic points gives a full clopen-transitive germ extension of V; F_n reduces to the germ condition at those points. Z^2*Z done (`z2-free-z-lies-in-an-fp-full-germ-extension-of-v`), germ groups Z^2 at rational points are fine here, unlike finite-nucleus RSGs.
**Pass 2 (free mode):**
- a6ff86235 + 752e85406: rsg-z2-locally-trivial-along-rational-attraction (ESTABLISHED lane proof) — germ lemma transported along orbits; Attempt 2 on the Z^2*Z node; RN rational-attractor sketch (corrected); ZS/product-of-trees route recorded as subsumed by BLIW (faithful factor ⇒ RF fibre ⇒ BLIW Thm C already applies).
- 0494a7f76: closed-mcg-self-similarity-needs-exotic-virtual-endomorphisms (+ -proof) (ESTABLISHED lane proof). For g ≥ 3, a finite-index L ≤ Mod(S_g) acting faithfully and self-similarly on a finite-alphabet tree needs a section hom that is non-injective with infinite image (Irmak rigidity + level-kernel recursion + normal core in Mod^±). So Zaremsky's self-similar route to 5.3(2) needs such an exotic hom (a virtual Z quotient would give one — Ivanov's question). **For bh-mcg:** cite as an Attempt on the closed-MCG root if useful.
- Pass 3: owner of BBCMP Q1.16 (MCGs continuous automatic?).
**Pass 3 (BBCMP Q1.16, claimed on UNOWNED):** a06edc3b3 + 2fc0a8e15 + this: mapping-class-groups-are-continuous-automatic (OPEN root, Q1.16 verbatim p.7); artin-groups-mod-central-garside-power-are-continuous-automatic (+proof, ESTABLISHED lane proof); low-complexity-mapping-class-groups-are-continuous-automatic (+proof): S_{0,n}, S_{1,0}, S_{1,1}, S_{2,0}. Open: S_{1,2}, S_{2,1}, genus ≥ 3. Idea recorded (Agol maximal splitting). Uses BBCMP Prop 1.4(2) as printed (proof absent from preliminary pp.1–16).
**Pass 4–5 (Q1.16):**
- 22241378f: continuity-of-automatic-structures-is-decidable (+proof) — continuity ⟺ bounded lookahead (K=|Q|^2), decidable by split-cycle search; twice-punctured-torus-mcg-is-continuous-automatic (OPEN modulo recalled Birman–Hilden S_{1,2}→S_{0,5}).
- 33125ffd1: mosher-suffix-uniqueness-gives-continuous-inverse-normal-forms (+proof) and once-punctured-mcgs-are-continuous-asynchronous-automatic (+proof): every Mod(S_{g,1}) is continuous ASYNCHRONOUS automatic ⇒ embeds in the rational group (BBCMP Cor 1.9). Input: Mosher's stated suffix uniqueness for 𝓛_0 (User's Guide math/9409209 §IV, K=1, n=3), read at source (TeX on MSI gqsrc/bh-hhg/mosher).
- **For bh-free-51:** BBCMP use LEFT multiplication; Mosher's forms are RIGHT-automatic. The object with a boundary action is the INVERTED language inv(ρ_*(𝓛_B)); run thinness/germ-rate tests there. Its left action = Mosher's backward "Do one move" ladder, a finite-state backward process with carry in B_1 and ≤3-letter chunks.
- Open (synchronous Q1.16): suffix uniqueness for Mosher's 𝓛_1 (Dehn twist factorization); closed surfaces (Mosher's closed structure is non-constructive).
- (from bh-free-51, f2fdbf369) For Q1.16:
  - Mosher's closed-surface automatic structure is non-constructive at source (Users' Guide
    arXiv:math/9409209, introduction), so there is no explicit structure to test for closed
    genus ≥ 2.
  - The once-punctured one is explicit (uncombing blocks, then L/R parity tails in one level;
    L_0 is prefix closed). The TeX is on MSI at `gqsrc/bh-free-51/x/Users_Guide.tex`.
  - Your Garside L̄ on B_n/Z (n ≥ 5), which gives S_{0,n} (n ≥ 6) and S_2, is continuous but NOT
    thin: `deligne-forms-are-singular-on-commuting-parabolic-diagonals`. So it cannot feed a
    germ-extension host.

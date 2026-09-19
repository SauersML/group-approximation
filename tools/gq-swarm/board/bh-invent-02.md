# bh-invent-02 (inventor lane: the compiler / ports / kernel removal, SYNTHESIS v5 gate 6)
Status: working (relaunched 09-18 ~14:30 after the coordinator restart).
- Landed: a8f37a022 amalgams-of-orbit-finite-actions-are-type-a2 (gluing lemma, regular ports).
- Now: Houghton ports. Any finite-rank free abelian subgroup with finitely many orbits is a port
  (Brown's H_3 carries a Z-element with two free orbits). So relPBH(D) holds for every fp D with a faithful
  fg-stabilizer action that is abelian-cofinite. Open: the one-dimensional Higman embedding problem.
- 5ea1bd4e0 LANDED: cofinite-abelian-subgroups-give-relative-pbh (ESTABLISHED lane proof), decidable-groups-embed-in-abelian-cofinite-hosts (OPEN),
  relative-permutational-boone-higman-conjecture (OPEN, FFWZ 1.8), relative-pbh-via-abelian-cofinite-hosts (route).
- Next: an abelian-cofinite host for one BH-open input (graph Houghton PB_r, Baumslag-Gersten, closed MCG); or closure of hosts under Higman's operations.
- a5f6a15a5 LANDED: higman-closure-of-abelian-cofinite-hosts-is-port-faithfulness (odometer host B is genuine; relative hosts closed under port amalgams/HNN/free products; faithfulness = the one gate; port rigidity).
- No host found for a BH-open input (PB_r, BG, MCG). Next: glue two copies of B along <a> twisted by a Thompson element, decide faithfulness (ping-pong on Z).
- 556e03d6f LANDED: port-amalgams-with-a-locally-moving-factor-are-never-faithful. Test answered NO: every gluing of two copies of B along <a> (B, cBc, or Thompson-twist HNN) has a kernel.
- Next: kernel removal by finitely many disjoint-support relators for the B *_<a> cBc image = V_(2,1)(<a,c>) (finitely presented? it is the RN group of D_infinity, contracting), which would make that one glued host explicit.
- a52e06127 LANDED (update): B *_<a> cBc image = B (cBc = B), fp, degenerate. RCWA partners always leave kernels. Next honest test: fp of G_(2,3) = <V_(2,1)(a), V_(3,1)(a)> <= RCWA(Z); kernel = mixed commutators; compare CT_{3}(Z).
- 084a4cff6 LANDED: class-wise-increasing-rcwa-p-groups-are-abelian-cofinite-hosts. R_P = F(Lambda_P x| Z) F_inf (Li III; thm:deg recheck for Lambda_P alone pending), host on Z; G_(2,3) <= R_(3), CT_(3)(Z) infinite index. Open: G_(2,3) = R_(3)? (generation lemma; mod-6 level done). Question posted in LESSONS for bh-pal-kourovka61 / bh-free-57.
- a2f925b55 LANDED: prime-odometer-groups-generate-class-wise-increasing-rcwa-p (G_(2,3) = R_(3), kernel removal by generation) + Li thm:deg recheck at source (R_P F_inf unconditional).
- Next: use the template on a BH-open input: which BH-open groups embed in a gluing of two Li-finite groupoid hosts along a port?
- 1887cf483 LANDED: baumslag-gersten-port-route-fails-at-the-dilation-centralizer. BG via port HNN fails at S1 (b-side port): baker map has cyclic centralizer (CHL). a-side port exists (Z^2 odometers in F((F2+ x F2+) x| Z^2), F_inf).
- Next candidates: a host where the BS dilation is non-expansive (e.g. lamplighter-type or affine hosts), or PB_r / closed MCG whose edge data are parabolic (Dehn twists) rather than hyperbolic.

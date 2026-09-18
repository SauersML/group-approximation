# Recent-preprint review for the BH swarm (late 2024 – 18 Sept 2026)

Lane bh-preprints, pass 1 (2026-09-18). Scope: every area the BH and GL_n(Q) swarms touch.
Method: arXiv API searches by keyword, category (math.GR listing from 2026-08-15 to 2026-09-17,
about 400 entries screened by title), and author (Zaremsky, Belk, Hyde, Matucci, Fournier-Facio,
Bleak, Nekrashevych, Lodha, Llosa Isenrich, Bux, Kojima, Xin Li, Mallery, Khanh, Voronetsky).
Relevant papers were fetched as TeX e-prints on MSI
(`/projects/standard/hsiehph/sauer354/gqsrc/preprints/<id>/x/`) and read at source for their main
theorems and open questions. Every id was grepped against `origin/main:research/` to separate new
material from material the graph already cites.

No claims of the lane's own. No priority judgments beyond what the sources say.

## 0. Headline

- **Nothing found settles an OPEN node of the BH graph, and nothing pre-empts an ESTABLISHED one.**
  No 2025–2026 preprint proves Boone–Higman for Out(F_n), closed-surface mapping class groups,
  one-relator groups, free Burnside groups, finitely presented residually finite groups, automatic
  groups, CAT(0) groups, all f.g. linear groups, all f.p. metabelian groups, spherical Artin groups of
  exceptional type, or GL_n(Q). The arXiv search for "Boone–Higman" returns 16 papers; all are
  already cited on main.
- **Version drift: none.** The versions main cites for the key imports are the current arXiv versions:
  BFFHZ 2503.21882v2, FWZ 2603.24687v2, FFKLZ 2506.02319v2, Zaremsky 2405.09722v2 and 2405.18354v2,
  BHM 2407.03149v1, BBMZ 2309.06224v3 and 2306.16356v3, Kojima–Sheng 2603.18410v3,
  BLIW 2408.05673v2, Khanh 2609.08428v1, HSZ 2605.20564v2, BDPR 2608.02111v1,
  Fournier-Facio–Zaremsky 2607.21727v1, LISW 2510.01952v1.
- So the graph's literature base is current. The items below are tools, calibration examples,
  new hard test cases and bookkeeping, not decisions.

## 1. New to main, medium relevance (read at source)

1. **Matte Bon–Nekrashevych–Zheng, arXiv:2607.13776 (Jul 2026), "Commensurating actions and
   self-similar groups."** Main theorem (Thm `t-sierpinski`): the iterated monodromy group of the
   square Sierpiński carpet subdivision rule is **amenable and has Property FW**. It is the first
   infinite f.g. amenable FW group, answering Cornulier. Also: contracting self-similar regular
   branch groups lack Property PW (for example, Grigorchuk's group).
   - *Bearing on the graph.* The carpet group is contracting self-similar, so it satisfies BH by
     Nekrashevych / Belk–Matucci (2405.10234). But as an infinite FW group it has no infinite image
     in any group with Property PW, and in particular it is not a subgroup of V (V acts properly on
     a CAT(0) cube complex, Farley). It is therefore an explicit amenable calibration for
     `almost-v-fw-subgroups-act-through-finitely-many-germs` and for the "Kazhdan subgroups of V /
     nV" nodes: FW, not only (T), pushes an input off V, and amenability doesn't help.
   - Relevant lanes: bh-kazhdan-inputs, bh-shell-kazhdan, bh-self-similar, bh-testcases.
2. **Nowak, arXiv:2609.12196 (Sept 2026), "Property (T) and nonlinearity of mapping class group
   quotients."** For g ≥ 3 and c ≥ 1, the Torelli lower-central quotients Mod(Σ_g)/(𝒯_g)_{[c+1]}
   have Property (T), and so do Aut(F_3)/(IA_3)_{[c+1]}. For c ≥ 2 every finite-dimensional complex
   representation of the Torelli quotient has infinite kernel, so these groups are **not linear over
   any field**.
   - *Bearing on the graph.* These are finitely generated, nilpotent-by-Sp_{2g}(Z), nonlinear
     Kazhdan groups, of the same flavor as the Deligne-lattice test case (bh-testcases item 4). Their
     solvable word problem and residual finiteness are not addressed in the abstract; check before
     using them.
   - They are natural new BH test cases: Kazhdan, nonlinear, arithmetic-by-nilpotent. Linear
     methods fail by Nowak, and V-type hosts fail by (T).
   - Relevant lanes: bh-testcases, bh-mcg, bh-kazhdan-inputs.
3. **Kuang, arXiv:2607.25729 and 2607.26572 (Jul–Aug 2026), "Near full groups of bounded type."**
   f.g. groups of bounded type from tile-inflation processes over Bratteli diagrams, containing the
   alternating group of the tail groupoid. Under a localization condition on finitely many singular
   germs, the topological full group is obtained by adjoining finitely many finitary
   transformations; near-fullness is controlled by a mod-2 dimension-group parity map.
   - *Bearing.* A "finite completion to a full group" statement. It is a possible tool for the
     full clopen-transitive host reformulation `permutational-boone-higman-iff-full-cantor-hosts`,
     which needs f.p. full hosts. Only f.g. is addressed there, not f.p.
   - Relevant lanes: bh-typeA-universal, bh-groupoid.
4. **Cortez–Urria, arXiv:2508.20005 (Aug 2025; v2 Jan 2026), "Stabilized automorphism groups and
   full groups of odometers."** The stabilized automorphism group of a free exact odometer (from a
   f.g. residually finite group action) equals the topological full group of the odometer acting on
   itself by right multiplication. Isomorphism is classified by clopen subgroups of equal index.
   - *Bearing.* Relevant to critic pass 3's U4 (stabilized automorphism groups) and to the
     Out(V) / Boyle-root calibration (`out-v-contains-the-root-problem-for-the-full-2-shift`),
     though for odometers rather than full shifts.
5. **Matui, arXiv:2412.05492 (Dec 2024; v2 Jul 2025), "Classifying Stein's groups."** Classification
   of Stein groups (PL bijections of an interval with prescribed slope and breakpoint groups) as
   topological full groups, via H¹-rigidity, when the slope group is f.g. and the additive group has
   rank ≥ 2.
   - Relevant lane: bh-linear-fields (Thompson-like groups).
6. **Ionin–Semidetnov, arXiv:2608.29219 (Aug 2026), "On Some More Problems from the Kourovka
   Notebook"** (LLM-assisted, checked by the authors). It settles Kourovka 14.85, 19.94, 16.11,
   17.47, 17.32 and others. None concerns BH or embeddings into simple groups.
   - Relevant lane: bh-kourovka, as bookkeeping, so these aren't re-attacked.
   - The companion arXiv:2609.04275 (explicit matrix in SL_2(F[X^±,Y^±]) \ E_2) is already cited
     once on main.

## 2. Already on main (confirmed current; listed so lanes don't re-fetch)

- **Nyberg-Brodda, arXiv:2606.27408:** Olshanskii's germ representation a ↦ 2x, b ↦ 2^x of the
  Baumslag–Gersten group is NOT faithful. The kernel word is [a,t] with t = s a s^{-1},
  s = b d b^{-1}, d = c^{-1} a c, c = b a b^{-1}. This answers **Kourovka 17.99 negatively**. It is
  already read in `research/artifacts/one-relator-weinbaum-gate-and-berlai-calibration-2026-08-30.md`
  §10. bh-kourovka should list 17.99 as solved by Nyberg-Brodda.
- **Almeida–Dantas–Oliveira-Tosti, arXiv:2609.01868:**
  - For non-torsion contracting G satisfying their condition (Ω), V_m(Z^d ≀_X G) is f.p. with
    finite abelianization, and Z^d ≀_X G embeds in an f.p. simple group (their Thm D). This is
    **infinite abelian lamps**, beyond main's finite-lamp closure
    `bh-type-a-class-closed-under-permutational-lamp-wreaths`.
  - It also shows PSL_2(Z[1/p]) is transitive self-similar for p ≥ 3, and strongly self-similar for
    p = 2 (Thm B).
  - Already cited 33 times on main.
- **Bilich–Hazrat–Nam, arXiv:2512.09241:**
  - The first Weyl algebra embeds in no unital Steinberg algebra, in particular in no L_K(m,n)
    (char 0).
  - Leavitt path algebras of finite (L)-graphs embed in L_K(1,2).
  - Already cited in `boone-higman-audit-2026-08-17.md` and in the Leavitt host artifacts.
- **Voronetsky, arXiv:2507.04519v3:** Schur multipliers of root-graded Steinberg groups. The
  A_ℓ-graded (linear, arbitrary associative ring) statement is van der Kallen–Stein's:
  - St_N(A) is centrally closed for N ≥ 5, and St_4 has an explicit multiplier (his Prop.
    `a3-schur`).
  - His introduction stresses that linear Steinberg groups over arbitrary associative rings "are not
    necessarily central extensions of the elementary groups". That supports keeping
    `k2-central-in-steinberg-groups-of-leavitt-resolvent-ring` OPEN rather than assuming centrality.
- **Others:**
  - Hyde–Skipper–Zaremsky 2605.20564: the Stein group F_{2,3} does not embed in V, via action graphs.
  - Bodart–D'Angeli–Perego–Rodaro 2608.02111: a graph characterization of subgroups of V.
  - Jaspars 2608.01168; Lorrain 2608.03813: the Dehn function of V is at most n^6.
  - Fournier-Facio–Zaremsky 2607.21727: Higman's rope trick never gives FP_3.
  - Kochloukova 2603.14556: residually finite GBS groups are self-similar.
  - Llosa Isenrich–Schesler–Wu 2510.01952; Sauer–Schesler 2605.30163; Palmer–Wu 2510.16879;
    Brothier–Seelig 2512.18943; Bruce–Li–Takeishi 2512.14324.
  - All are cited on main.

## 3. Screened, low relevance (not in main; no action)

- Aramayona–Domat–Leininger 2609.08849: surface Houghton groups are finite index in asymptotically
  conformal modular groups; type F_{n-1}, not FP_n.
- Gundelach 2602.18197: an embedding version of Rubin's theorem.
- Golan 2609.14702: finiteness properties of closed subgroups of F.
- Lodha 2503.13523: just-infinite quotients of f.g. subgroups of F, PL(I) and the piecewise
  projective group are virtually abelian.
- Hill–Kwak–Udall–West 2508.21264: graph Houghton groups.
- Yanagawa 2609.01996: model theory of G-fields.
- Kegel–Li 2609.10461: small undecidable groups.
- Dong–Rauzy 2609.15378: the torsion-freeness problem for matrix groups.
- Castellano–Fariña-Asategui 2609.17410: t.d.l.c. simple groups.
- Gray–Linton 2607.07496: rewriting for graphs of free groups.
- Soroko–Vaskou 2604.27526: R_∞ for generalized Higman groups.
- The Baumslag–Gersten Diophantine papers 2608.01983 and 2607.24189.

## 4. Open questions in recent preprints that a lane could take

- Nyberg-Brodda 2606.27408: is ⟨2x, 2^x⟩ (germs at ∞) finitely presented? Its abelianization is Z.
- Almeida–Dantas–Oliveira-Tosti 2609.01868:
  - does Z ≀_X PSL(Z[1/2]) embed in an f.p. self-similar group?
  - which A ≀_X G embed in a self-similar group whose Nekrashevych commutator subgroup is f.p.?
- Aramayona–Domat–Leininger 2609.08849: Cantor-surface versions of their finite-index theorem.
- Matte Bon–Nekrashevych–Zheng 2607.13776: their commensurating-action classification, as input
  to FW-based host exclusions.

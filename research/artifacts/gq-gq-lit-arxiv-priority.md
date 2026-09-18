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

## 5. Follow-up for the coordinator (2026-09-17): nV hosts and contracting RSGs

Asked: what is known about distorted cyclic subgroups, BS(1,2) and SL_3(Z) inside 2V/nV (Zaremsky list
2.7, 2.19), and has anyone asked whether a contracting rational similarity group can contain (Q,+)?

**Distortion in nV.** The only published fact found is Callard–Salo, arXiv:2208.00685, imported as
`brin-thompson-mv-contains-a-distortion-element`: for m >= 2, mV has an element with |f^N| = O(log^4 N).
- This is polylogarithmic. BS(1,2) needs an element with |a^N| = O(log N), since a^{2^k} = t^k a t^{-k}.
  So the Callard–Salo element does not give BS(1,2), and no source found either embeds BS(1,2) in some nV
  or excludes it.
- The one exclusion paper, arXiv:2209.11982, is WITHDRAWN.
- In Cairn: `bs12-embeds-in-brin-thompson-2v` is OPEN. The necessary condition
  `bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets` is ESTABLISHED (elementary, not
  independently reviewed). Search artifacts: `bs12-2v-search-2026-09-13.md`,
  `bs12-2v-survivors-2026-09-13.md`.
- For GL_n(Q), BS(1,2) ≤ Aff(Z[1/2]) ≤ GL_2(Q). So **any nV route to G needs BS(1,2) ≤ nV first.**
  That is exactly this open node.

**SL_3(Z) in nV.** No source found. It is Zaremsky 2.19(c)/(d) (GL_n(Z) in some mV, or in 2V), open in the
graph (`zaremsky-2-19c-...`, `zaremsky-2-19d-...`). It is coupled to 2.7: SL_3(Z) ≤ mV would make kV fail
the Haagerup property for every k >= m. Whether 2V is a-T-menable is open (`zaremsky-2-07-...`).
Known inside 2V:
- every RAAG (Salo, arXiv:2103.06663, via the topological full group of the full shift, which embeds
  in 2V; this refutes Belk–Bleak–Matucci Conjecture 1.7);
- Z_2 ≀ Z and A ≀ G for groups with unique-move actions (same paper);
- Q (Kojima–Sheng, arXiv:2603.18410v3);
- a distortion element (Callard–Salo).

Nothing found on nilpotent non-abelian groups (H_3(Z)) in nV. The Cairn node
`heisenberg-in-nv-forces-drift-free-central-element` (established, not reviewed) is the only input.

**Contracting RSGs and (Q,+).** Not asked anywhere I found.
- BBMZ arXiv:2309.06224 §1.3 poses six questions. None concerns which groups (abelian, divisible, Q) lie
  in contracting RSGs. Question 1.1 asks whether every non-elementary hyperbolic group is a contracting
  RSG.
- BHM arXiv:2407.03149 and Belk–Matucci arXiv:2405.10234 pose no such question.
- Remarks, not checked against sources:
  - Contracting *self-similar* groups are residually finite, so O1 excludes them.
  - *Full* contracting RSGs contain V_{Γ,E}, so they are not residually finite, and O1 is silent.
  - O3 (Q ⊄ V, via Higman's finitely-many-roots theorem) has no published analogue for RSGs.
  - Belk–Bleak arXiv:1405.0982 transfer undecidability of the torsion problem from 2V to the rational
    group R, which suggests 2V ≤ R and hence Q ≤ R. The abstract does not state the embedding verbatim.
    R is not finitely generated, so this says nothing about contracting RSGs.
- **The question looks unasked.** A lane could land it as an OPEN claim ("some full contracting RSG
  contains (Q,+)") with O3's root argument as the first test.

## 6. Priority check for gq-ring-fp-simple (2026-09-17): finitely presented simple ring of characteristic 0

Asked: is it known that a unital ring, finitely presented over Z, can be simple of characteristic 0?
Equivalently (node `fp-simple-ring-of-characteristic-zero-exists`), does Q embed in a finitely presented
simple ring? The candidate is `leavitt-resolvent-ring-is-fp-simple-of-char-zero` (aaf4b1279).

**Verdict: no source found stating it, either way.** This is a bounded search: web and arXiv only, no
MathSciNet or zbMATH, and the Dniester Notebook and the Kharlampovich–Sapir survey (IJAC 1995) were not
read. What was found:
- **Over a field K, finitely presented as K-algebras.** Leavitt algebras L_K(1,n) are simple and finitely
  presented. For K = F_p this gives finitely presented simple rings over Z of characteristic p. For K = Q,
  L_Q(1,n) is finitely presented over Q but is not a finitely generated ring.
- **Finitely generated but not finitely presented.** Bokut, "Embeddings into simple associative algebras",
  Algebra i Logika 15 (1976) 73–90: every countably generated algebra over a countable field embeds in a
  two-generated simple algebra. So finitely generated simple rings containing Q exist. Finite
  presentation is not addressed.
- **Finitely presented but not simple.** Belyaev, "Subrings of finitely presented associative rings",
  Algebra i Logika 17 (1978) 627–638, gives a Higman embedding theorem. A secondary source says it covers
  algebras over a field that is a finite extension of its prime subfield.
- **Weak Boone–Higman.** Evans–Mandelberg–Neff (Logic Colloquium '73, 1975) embed an algebra with solvable
  word problem in a simple algebra inside a finitely presented algebra. Survey arXiv:2306.16356v3 §3 lists
  it for "rings of characteristic p".
- None of these gives finite presentation and simplicity at once in characteristic 0. The survey's
  restriction to characteristic p fits with the characteristic-0 case being unrecorded. Treat the result
  as possibly new, **pending an expert check with MathSciNet**, since it could be folklore (for example
  via algebraic Cuntz–Pimsner rings, Carlsen–Ortega).

**Hand check (gq-lit-arxiv) of item 1 of the node: Q ⊆ R_L.** It uses only the defining relations.
- From N s_1 = s_1(N+1) and N s_2 = 0, induction gives N s_1^(m-1) s_2 = (m-1) s_1^(m-1) s_2.
- So (N+1) s_1^(m-1) s_2 = m s_1^(m-1) s_2. Multiplying by A on the left gives
  m·A s_1^(m-1) s_2 = s_1^(m-1) s_2.
- Hence m·(t_2 t_1^(m-1) A s_1^(m-1) s_2) = t_2 t_1^(m-1) s_1^(m-1) s_2 = 1.
- The Fock-type model on Q^(X) is a nonzero representation, so R_L ≠ 0. So R_L is a nonzero finitely
  presented ring that is a Q-algebra.

Simplicity (item 2) is what needs the referees. It was not checked here.

## 7. Priority check for gq-steinberg-q (2026-09-17): unstable K_2, Leavitt pairs, fp Kazhdan overgroups

The node is `leavitt-pairs-embed-sl-n-q-in-steinberg-groups` (b9dd69f0a). Its claim: in any ring S ⊇ Q
with a binary Leavitt pair, St_N(Q) → St_(6N+1)(S) has kernel exactly K_2(N,Q), so SL_N(Q) ≤ St_(6N+1)(S).
This is a bounded web and arXiv search, with no MathSciNet.

**(i) Does a Leavitt pair kill unstable K_2 at a finite rank?** No source found for the claim as stated.
- **Stable vanishing is known.** Ara–Brustenga–Cortiñas, *K-theory of Leavitt path algebras*
  (arXiv:0903.0056, Münster J. Math. 2009), give a long exact sequence that makes K_*(L_K(1,2)) vanish for
  regular K. The graph records it as `ara-cortinas-leavitt-tensor-k-theory-vanishes`.
  - Flasque and cone rings (Karoubi, Gersten, Wagoner) have vanishing K-theory, also only stably.
- **Nearest unstable result.** Khanh, arXiv:2609.08428v1 (2026-09-08), Theorem 5.4: for R = L_{F_2}(1,2)
  and every r ≥ 3, "the canonical map φ_r: St_r(R) → GL_r(R) is an isomorphism". So K_2(r,R) = 0 and
  E_r = GL_r at rank 3, but only for the F_2 Leavitt algebra itself, with no statement for other fields.
  - Its Lemma 5.2, "j_m(N_m(B)) is central in St_(m+1)(B)" for m ≥ 3, is the analogue of the lane's
    room lemma (a).
  - This is the closest neighbour, and the lane should cite it. The lane's statement is different:
    killing the image of K_2(N,Q) inside St(S) for an arbitrary S ⊇ Q with a pair, at rank 6N+1.
- **Status.** The rank-6N+1 transfer looks unrecorded. Credit risk: the doubling and block-expansion
  trick is the standard way to show K-theory of properly infinite rings is trivial. So the contribution
  is the explicit unstable bound. Keep it OPEN until the referees report.

**(ii) A finitely presented Steinberg-group overgroup of GL_n(Q)?** No source found. Mikaelian's announced
explicit overgroup (§2) is an HNN and amalgam construction, not a Steinberg group.

**(iii) Q inside a finitely presented Kazhdan group: KNOWN, by combining known results.**
- Chatterji–Kassabov, arXiv:2601.22907, Theorem 3 (already imported as
  `chatterji-kassabov-normal-generator-embedding`): every finitely generated recursively presented G, with
  any g ≠ 1, embeds in a finitely presented property (T) group Γ = ⟨⟨g⟩⟩.
- Apply it to G = T̄ ⊇ Q (finitely presented, Belk–Hyde–Matucci). That puts Q in a finitely presented
  Kazhdan group.
- GL_n(Q) embeds in a 2-generated recursively presented group (Higman–Neumann–Neumann; survey
  Corollary 3.4 proof). So GL_n(Q) ≤ Γ too, finitely presented, Kazhdan, and normally generated by a chosen
  element. Γ is not simple and not explicit.
- **Their construction** is a ring construction:
  - G sits in EL_3(Z[G̃]) through diagonal matrices;
  - Lemma 4 builds a finitely generated ring extension L in which a chosen r generates the unit ideal;
  - Shalom's theorem supplies a finitely presented Kazhdan cover, and the presentation of a finitely
    presented M is then added.
  - They do not control K_2. This is exactly where the lane's Steinberg result could add something: a
    *Steinberg-group* overgroup St_m(S), with S finitely presented, which is itself finitely presented and
    Kazhdan (`steinberg-finite-presentation-and-kazhdan-theorem`).

## 8. Priority check for gq-deep-free-1 (2026-09-17): one Steinberg group containing every GL_n(Q)

The node is `one-steinberg-group-contains-every-gl-n-q` (27d360184). Its claim: SL_(4m)(Q) ≤ St_4(S) for every
m, where S ⊇ Q has a Leavitt pair. With S = D (6 generators, 7 relations), St_4(D) is one finitely presented
group containing every GL_n(Q). This is a bounded web and arXiv search, with no MathSciNet.

**(i) Existence of one finitely presented group containing every GL_n(Q): classical, not explicit.**
- GL_∞(Q) = ⋃_n GL_n(Q), and also ⊕_n GL_n(Q), are countable with solvable word problem.
- So by Higman–Neumann–Neumann plus Higman's theorem, each embeds in a finitely presented group. The
  survey's Corollary "every countable, computably presented group embeds into a finitely presented group"
  (§2, `cor:InfinityGeneratedHigman`) gives exactly this.
- By Chatterji–Kassabov Theorem 3 (`chatterji-kassabov-normal-generator-embedding`) the host can also be
  taken Kazhdan and normally generated by any chosen element. Their Theorem 1 does this explicitly for
  SL_∞(Z).
- So the lane must not claim that "a single finitely presented group contains every GL_n(Q)" is new.
  What can be new is an **explicit, natural** one: a Steinberg group over a small explicit ring.

**(ii) Explicit overgroups of GL_n(Q) (Problem 2.7 / Kourovka 14.10(c)).**
- The only prior item found is Mikaelian's *announcement* (arXiv:2507.04347 v1 2025-07-06, v8 2026-06-03,
  §1.4; §2 above). It gives an explicit finitely presented, 2-generator Γ_n for each n, via an explicit
  Higman algorithm, with the construction in an unseen reference [41].
- So the lane cannot claim "first explicit". It can claim a different and arguably *natural* construction,
  and one group for all n at once, which that announcement does not claim.
- The survey's standard for "natural" is the Belk–Hyde–Matucci T̄. Whether St_4(D) meets it is a judgement
  for experts. The write-up should say so.

**(iii) Ingredients: classical, and should be cited as such.**
- Leavitt (1962): a ring of module type (1,2) satisfies S ≅ S^n and M_n(S) ≅ S for all n ≥ 1. So
  GL_n(Q) ≤ GL_n(S) ≅ S^× for every n is folklore once S ⊇ Q has a Leavitt pair. The repo already states it
  for R_L (`leavitt-resolvent-ring-is-fp-simple-of-char-zero`, item 3).
  - The lane's addition is the passage from E or GL to the **Steinberg** group, which is finitely presented
    when S is (`steinberg-finite-presentation-and-kazhdan-theorem`, n ≥ 4). Finite presentation of
    S^× or E_n(S) is not known.
- Its step (a), St_4(M_k(Q)) ≅ St_(4k)(Q) for a field, rests on known centrality and universality: surjective
  stability for K_2 (Voronetsky arXiv:2004.08551, citing earlier work) and Kervaire's central closedness
  for n ≥ 5.
- Nearest unstable-over-Leavitt result: Khanh arXiv:2609.08428 Theorem 5.4 (St_r = GL_r over L_{F_2}(1,2)
  for r ≥ 3). Cite it.
- Overlap with `leavitt-pairs-embed-sl-n-q-in-steinberg-groups` (lane gq-steinberg-q, rank 6N+1) is
  already recorded in distinct_from. The two lanes should compare step (b), the "scalar blocks multiply
  K_2 by N" argument, against that node's doubling argument.

**Verdict.** No prior art found for SL_(4m)(Q) ≤ St_4(S) for all m, nor for any explicit Steinberg-group
overgroup of GL_n(Q). Existence of a finitely presented overgroup of all GL_n(Q) is classical, and an
explicit per-n overgroup is announced by Mikaelian. Keep the node OPEN pending the three referees. Also
review `finitely-presented-divisible-ring-engine` (D ⊇ Q, finite presentation), which the claim relies on.

## 9. Priority checks for the coordinator (2026-09-17): ring envelopes, Q in U(L_Z(1,2)), stated problems

Bounded web and arXiv search. No MathSciNet. The full texts of Evans–Mandelberg–Neff and the
Kharlampovich–Sapir survey are paywalled (ScienceDirect and World Scientific refuse automated access).

**(1) `char-zero-representable-rings-embed-in-fp-simple-rings` and `rational-function-fields-embed-in-fp-simple-rings`
(36d65161f).** The claims: finitely generated subrings of M_n(F), F a field of characteristic 0, and
Q(t_1..t_k), embed in finitely presented simple rings.

**No prior finitely presented simple envelope found in characteristic 0.** What exists:
- **Finitely generated simple envelopes, not finitely presented.**
  - Bokut, Algebra i Logika 15 (1976) 73–90: every countably generated algebra over a countable field
    embeds in a two-generated simple algebra.
  - Bokut–Chen–Mo (arXiv:0908.1992): the same for Ω-algebras and differential algebras.
  - Alahmadi–Alsulami–Jain–Zelmanov, arXiv:1703.08734 (Trans. AMS 372, 2019): matrix wreath products give
    embeddings into finitely generated Jacobson radical, nil and primitive algebras. No finitely presented
    simple envelope.
- **Finitely presented, not simple.** Belyaev, Algebra i Logika 17 (1978) 627–638: a Higman theorem for rings.
- **Weak form.** Evans–Mandelberg–Neff (Logic Colloquium '73, 1975): a simple algebra inside a finitely
  presented algebra. The survey lists it for "rings of characteristic p".
- **Finitely presented simple algebras over a field** are classical, but only as K-algebras:
  - Leavitt L_K(1,n);
  - the Weyl algebra A_1(Q) = Q⟨x,y | xy − yx = 1⟩, simple in characteristic 0;
  - Nekrashevych algebras of contracting self-similar groups, which Steinberg–Szakács (arXiv:2008.04220,
    Math. Ann. 2022) prove "are finitely presented", with an algorithm listing the field characteristics
    for which they are simple.
  - In characteristic p these give finitely presented simple rings over Z. In characteristic 0 they are
    presented over Q, not finitely generated as rings, and the repo's claims need more: a finite
    presentation over Z containing Q or Q(t).
- **Credit risk.** The Weyl and Nekrashevych families show that "finitely presented over K and simple" is
  classical. The claims are only new for presentations over Z. Say "finitely presented as a ring (over Z)"
  in every statement.

**(2) `integral-leavitt-unit-group-contains-q` (double-refereed).** The claim: (Q,+) ≤ ⟨V, 1 + x_01 y_00⟩ ≤ U(L_Z(1,2)).
- **No prior art found.** V ≤ U(L_K(1,2)) by permutation units is standard (Nekrashevych, Brin, and the
  Leavitt-path literature, e.g. arXiv:2504.01363 on Higman–Thompson groups in Leavitt path algebras).
- Recent unit-group papers do not discuss divisible subgroups, roots of unipotent units, or Q:
  - Khanh–Thanh arXiv:2607.10351 (matrix generators for L_K(1,d)^×; over a finite field, finite
    presentability of L_d^× is equivalent to finite generation of unstable K_2(n, L_d));
  - Hai–Khanh arXiv:2503.18558 (free subgroups in characteristic 0);
  - Khanh arXiv:2609.08428.
- Nearest group-level analogues: Q ≤ T̄ ≤ VA (Belk–Hyde–Matucci) and Q ≤ nV, n ≥ 2 (Kojima–Sheng
  arXiv:2603.18410v3).
- **Novelty plausible on this bounded search.** The node says "Novelty not searched"; it could now say
  "bounded search, no prior art found".

**(3) Is "Q embeds in a finitely presented simple ring" or "a finitely presented simple ring of characteristic 0 exists" a stated problem?**
**Not found as a stated problem anywhere I could read.**
- Survey arXiv:2306.16356v3 §3 mentions EMN only for "rings of characteristic p" and poses no ring question.
- Kourovka (arXiv:1401.0300v46) is about groups. The GL part of 14.10 is a group question.
- The Dniester Notebook could not be read. A problem there cannot be ruled out; it is the most likely
  home for such a question, given the Novosibirsk school (Bokut, Belyaev).
- Zelmanov's *Some open problems in the theory of infinite dimensional algebras* (J. Korean Math. Soc.
  2007) was not read. Its known items (nil Jacobson radical of finitely presented algebras, PI images of
  d-generator d²/4-relator algebras) are different.
- The Kharlampovich–Sapir survey (IJAC 1995) was not read.
- **Recommendation:** don't call it an "open problem". Present it as the characteristic-0 case of the
  algebra Boone–Higman question (`algebra-boone-higman-conjecture`), for the single input Q. The survey's
  characteristic-p framing of EMN supports this reading. Check the Dniester Notebook (4th edition, 1993)
  and the Kharlampovich–Sapir survey before any write-up.

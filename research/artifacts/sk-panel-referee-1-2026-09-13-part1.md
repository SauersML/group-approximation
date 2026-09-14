# sk-panel-referee-1, part 1: hostile referee report (group theory and correctness)

- Lane sk-panel-referee-1 (a Claude Code agent, not human review), 2026-09-13.
- Read:
  - main's note at 5b1890ce6c (revision 1, 292 lines, md5 8e04b341…);
  - the frozen disk copy;
  - `sk/drafts/rev2-decisions.md`;
  - the drafts `sk/drafts/sk-draft-minimal/minimal.tex` (19:21) and `sk/drafts/sk-draft-ring/sk-draft-ring.tex` (19:25);
  - the Stepanov page images, pp. 2150–2153 of the Springer PDF (`/projects/standard/hsiehph/sauer354/un-stepanov/stepanov.pdf`);
  - the lane artifacts sk-stable-rank-a/b, sk-universal-embedding-a, sk-generators, sk-open-4, and sk-review-1 parts 1–5.
- Standard: Annals / Inventiones / JEMS.

## 0. Verdict
- **Correctness: no ERROR.** I re-derived every step of the simplicity, LEF and word-problem arguments in main's revision 1 and in both drafts.
- **The one blocker is credit.** The introduction says "The new step is simplicity" (main l.59). But simplicity already follows from Stepanov's Theorem 4.4 once a two-line dimension count supplies his condition (b); see §1. A referee who knows the normal-structure literature will find this at once.
- **As a paper:** a correct, short answer to a well-known question (Brown 2001, Ozawa 2003, Pestov 2008). Every ingredient exists in some form: (T) is EJZ, the finite models are periodic approximation, simplicity is Stepanov-type normal structure. The contribution is the choice of one ring for which all three apply. That is enough for a very good journal. §4 lists what would make it astonishing.

## 1. Blocker: simplicity is covered by Stepanov 1997, Theorem 4.4

**Statement, read from the page images** (J. Math. Sci. 95 (1999), p. 2151–2152, n ≥ 3 throughout):
"4.4. Theorem. Assume that for any proper two-sided ideal I in R, the following conditions hold: (a) [GL(n,R,I), E(n,R)] = E(n,R,I); (b) for any a ∈ GL(n,R), there exist b ∈ E(n,R/I) and α ∈ (R/I)^n (α ≠ 0) such that α_i = (u^b α)_j = 0 for some i, j ∈ {1,…,n}, where u = ρ_I(a) is the image of a in GL(n,R/I). Then the normal structure of GL(n,R) is standard."
The proof (p. 2152) ends: "F is contained in the center of GL(n,R) and H ≤ C(n,R,I)", where I is the ideal associated with H.

**Specialization to a simple ring R.**
- The only proper ideal is 0, and (a) at I = 0 reads {1} = {1}.
- The proof applies (b) to R̄ = (R/I)/I^⊥(a) with a noncentral. In a simple ring I(a) = R, so I^⊥(a) = 0 and R̄ = R. So (b) is needed for R alone.
- Conclusion: every subgroup of GL_n(R) normalized by E_n(R) is central or contains E_n(R). If H contains a nontrivial transvection t_ij(ξ), its associated ideal is R.

**Condition (b) for R = LC(X,F_q) ⋊_T Z holds by pair dependence** (sk-stable-rank-b, `amenable-crossed-products-meet-stepanov-condition-b`; I re-derived it):
- Let p = Σ_{|j|≤w} p_j u^j and q = Σ q_j u^j. Choose a nonempty clopen U on which every p_j, q_j is constant on each T^kU, k ∈ [−w, 3w] (finitely many locally constant functions).
- Put r = Σ_{0≤i≤2w} ρ_i u^i e_U and s = Σ σ_i u^i e_U with ρ_i, σ_i ∈ F_q.
- Since u^k e_U = e_{T^kU}u^k, pr + qs = Σ_{k=−w}^{3w} (Σ_{i+j=k} ρ_i p_j(k) + σ_i q_j(k)) e_{T^kU} u^k.
- The monomials e_{T^kU}u^k are independent (distinct powers of u). So pr + qs = 0 is 4w+1 linear equations in 4w+2 unknowns, and a nonzero solution exists. Then (r,s) ≠ 0.
- For a ∈ GL_3(R), take b = 1 and α = (0, r, s)^T with p = a_12, q = a_13. Then α_1 = 0 = (aα)_1.

**Consequence.** With R simple (6 lines), every normal subgroup of EL_n(R_X) is central or everything, for every q and n ≥ 3. That is the note's simplicity theorem.
- Status: the sk-stable-rank-b routes `subshift-elementary-group-simple-stepanov-proof` and `amenable-crossed-product-gl-normal-structure-is-standard-proof` are unreviewed.
- This report checks Theorem 4.4's wording and scope, and the count. It does not re-check every line of Stepanov's printed proof.

**Required fix (credit, not mathematics).** Keep the direct proof: it is self-contained and gives the finite simple group picture. Replace main l.59–62:
```latex
Medynets~\cite{GM}. The new step is simplicity. A nontrivial normal
subgroup contains a nontrivial commutator lying in a finite simple
group $\GL_d(\F_2)$ acting on a clopen tower, so it contains this group
and with it an elementary matrix.
```
with
```latex
Medynets~\cite{GM}. Simplicity also follows from Stepanov's theorem on
the normal structure of $\GL_n$~\cite[Theorem~4.4]{Stepanov}, since any
two elements $p,q$ of the ring satisfy $pr+qs=0$ with $(r,s)\ne0$, by a
dimension count on one cylinder. Our proof is direct: a nontrivial
normal subgroup contains a nontrivial commutator lying in a copy of the
finite simple group $\GL_d(\F_2)$ over a clopen tower, so it contains
this group and with it an elementary matrix.
```
- Cost: +3 lines. The reader learns the literature already covers the step, and trusts nothing new.
- The Matui sentence that follows stays.
- The same fix applies to sk-draft-minimal, which dropped Stepanov altogether, and to sk-draft-rich/general if they copy l.59.

## 2. Line-level fixes to main (revision 1, 5b1890ce6c)
- **F1, l.59–62:** §1 (credit).
- **F2, l.111–112.** "By minimality every word of X occurs in $x$". The argument needs occurrences inside $x_{[0,\infty)}$: forward orbits are dense in a minimal system. sk-draft-minimal l.107–108 already has "occurs in $x_{[0,\infty)}$". Adopt it.
- **F3, l.130–132.** Images are invertible because φ_ℓ(g)φ_ℓ(g^{-1}) = φ_ℓ(g g^{-1}) = I once ℓ is large. Say so in half a line; the phrase "and of their inverses" hints at it but does not state it.
- **F4, l.155.** "Since the sets $T^aV$ are disjoint" means pairwise disjoint for |a| ≤ w. sk-draft-minimal l.151–154 has the cleaner convention-free version: ε_ab = u^a e_V u^{-b}, and e_V u^c e_V = 0 for 0<|c|≤2w. Adopt it.
- **F5, §2 l.201–212.** The letter n is the word length there, while the theorem uses EL_n. Use m for the word length.
- **F6, l.180–181.** The level J "of $N$~\cite{Stepanov}" cites Stepanov only for a word. sk-draft-minimal l.175–181 ends without the level ideal:
  - e_pl(re_V) = [e_pq(r), e_ql(e_V)] and e_pq(re_Vs) = [e_pl(re_V), e_lq(s)];
  - 1 is a sum of products re_Vs, since 1 = 1−∏(1−e_{T^aV}) and each e_{T^aV} = u^ae_Vu^{-a}.

  I checked both commutators and the expansion. It is shorter and needs no citation. Adopt it together with F1.
- **Checked and correct, no change:**
  - the small-set existence and the scalar step (c ∈ LC(X,F_2) unit ⇒ c = 1);
  - the matrix units ε_ab and ψ multiplicative and injective;
  - k − I_3 = (ghg^{-1} − h)h and k^{-1} − I_3 = h(ghg^{-1} − h) ∈ ψ(M_d);
  - I + ψ(A) invertible ⇒ I_d + A invertible;
  - the transvection commutator for p = q;
  - the level-ideal closure;
  - the finite-model period argument;
  - D_ℓ well defined, and PD_ℓP^{-1} = D_ℓ(f∘T^{-1});
  - injectivity through disjoint cyclic supports;
  - the Sturmian arcs, the ones count and the continued-fraction degrees;
  - "finitely presented LEF ⇒ RF".

## 3. Drafts (phase 2, partial) and ranking

**sk-draft-ring (351 lines): correct, and the strongest statement.** Checked:
- Lemma normal:
  - the annihilated s outside the commuting subgroup;
  - tρ = tI_n from 1 ∈ F;
  - z = Y_qm c t ≠ 0 by simplicity;
  - e_ml(ct)ρ = ρ + ctE_ml;
  - v = I + Y ctE_ml;
  - (v^{-1})_ll a unit, since v and v^{-1} are column-l matrices;
  - [e_bq(1), v] = e_bl(z(v^{-1})_ll).
- Lemma lef, including the quotient by a finite central Z (ψ(Z) is a subgroup centralizing ψ(F), and the map is injective through injectivity on FF).
- "R infinite" from local annihilation with F = R.
- Simplicity and the centre of R_X; local annihilation for R_X (it needs only X infinite, no freeness); the ultraproduct embedding.
- Fixes:
  - (i) F2 applies (l.226–227).
  - (ii) Framing. The abstract and first theorem lead with a new definition, and a reader remembers G_X, not local annihilation. Put Theorem main first and the ring theorem second, or make the ring theorem a lemma.
  - (iii) The credit at l.78–80 (Stepanov Lemma 4.3 method) is fair. Local annihilation and Stepanov's (b) are different hypotheses; whether one implies the other is open (un-stepanov-credit).
  - (iv) §1's Theorem 4.4 remark should still appear for R_X.

**sk-draft-minimal (291 lines): correct, and the best reader experience.** Checked:
- the level-free ending (F6);
- the Brown paragraph: infinite simple ⇒ ICC (a nontrivial FC-centre would be all of G, and an f.g. FC group has finite derived subgroup); L(G)⊗̄R is separable and McDuff; M ⊂ R^ω ⇒ M⊗̄R ⊂ R^ω;
- ε_ab = u^ae_Vu^{-b}, and fu^a = u^a(f∘T^a).

Fixes:
- (i) Restore Stepanov at the credit sentence (§1).
- (ii) Its Origin paragraph (l.229) predates main's current wording ("Codex (OpenAI) shortened an earlier version, and Claude revised this one"). Rebase.
- (iii) MSC 16S35 was dropped; the paper is about a crossed product ring, so restore it.
- (iv) The `\smallskip` paragraph l.183–192 mixes Brown's bridge and the EL_n remark. Split them, and move the bridge next to "sofic and hyperlinear".
- (v) F5.

**sk-draft-general:** only partA existed at review time, so it is not reviewed. **sk-draft-rich:** empty.

**Ranking now:**
1. sk-draft-minimal plus fixes (i)–(v).
2. sk-draft-ring. Stronger, but framed around a definition, and +59 lines over main.
3. Main revision 1, superseded by minimal's ending and Brown paragraph.

**Best combination.** Use minimal's skeleton with the ring draft's Lemma normal in place of the constant-tower section:
- Lemma normal plus the local-annihilation check is about 40 source lines, against the tower section's 51.
- It covers every F_q and n ≥ 3, and uses neither the simplicity of GL_d(F_2) nor the binary unit trick.
- That is decision item 13, and on correctness grounds I support it.

## 4. What would make this astonishing (group theory)
- **A1. Theorem E: every f.g. residually finite group embeds in an infinite f.g. simple Kazhdan LEF group** (sk-universal-embedding-a, 3bcc003284; unreviewed). I checked the outline:
  - Lemma 2 (doubling makes left multiplication even; Ore; Δ ≤ ∏Sym(Ω_n) is RF);
  - Lemma 3 (unique non-constant coset D_m(y), equivariance, freeness at every point);
  - Lemma 4 (at most 2|W| < d_{M+1} bad classes);
  - diag(a,a^{-1})diag(b,b^{-1})diag((ba)^{-1},ba) = diag([a,b],1), so diag([a,b],1,1) ∈ E_3.

  Synergy: in the ring architecture, local annihilation over any Δ needs only X infinite, simplicity of R needs minimality and topological freeness, and LEF needs Lemma 4's window models. So the Δ-version costs about 15 lines on top of a ring lemma. Kionke–Schesler already have the version without (T). This is the strongest group-theory corollary available.
- **A2. G_X is a marked limit of the finite simple groups SL_{3m}(F_2), with a uniform Kazhdan constant** (quotients of EL_3 of a free algebra; Kassabov 2007 credit; the reviewed node `finite-simple-groups-converge-to-simple-kazhdan-group`). One paragraph, and the most memorable one-line strengthening of "LEF".
- **A3. All finite fields and n ≥ 3** (ring draft).
- **A4.** One sentence on why EL and not GL: the half-orbit index maps GL_n(R_X) onto Z and kills EL_n, so GL_n is neither simple nor Kazhdan (`crossed-product-gl-n-has-infinite-cyclic-index-quotient`, unreviewed). A referee will ask. Optional.
- **Not for the note:** two-generation (open), rigidity (open), MF of C*_r (famous), f.p. versions (open; the questions sentence suffices).

## 5. Firewalls for future revisions
- diag(a,a^{-1},1) is not a homomorphism on noncommuting units. Any embedding text uses diag(a,1,1) on derived subgroups.
- The binary unit trick (LC(X,F_2)^× = {1}) fails over F_q. An F_q statement must use local annihilation, the roots e_ij(e_Cu), or Stepanov.
- Never write "n = 2 loses (T)"; it is false for subshifts with a finite cyclic factor.
- Theorem E's tower proof needs freeness at every point (Lemma 3). The local-annihilation route needs only X infinite plus a simple ring.

## 6. Phase 2 status
- Reviewed: main revision 1, minimal.tex (19:21) and sk-draft-ring.tex (19:25).
- Pending: sk-draft-general (partA only), sk-draft-rich (empty), minimal-nocor.tex.
- Resume this lane when those land.

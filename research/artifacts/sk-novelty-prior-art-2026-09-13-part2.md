# Novelty of the simple Kazhdan sofic group note (part 2): technique credit, the Turing corollary, novelty statements

Lane `sk-novelty`, 2026-09-13. Continues part 1 (e8c3931be3). Line numbers refer to the disk version of 16:46
(`$SK/manuscript-disk-1646.tex`).

**New tag.** PT = passage read in the PDF text layer. The arXiv PDF was fetched on MSI and extracted with `gs txtwrite`
into `/scratch.global/sauer354/sk/sk-novelty/{matui,gm15}.txt`. The extracted line numbers are given, and the math
symbols are as extracted.

## 4. Technique credit for the simplicity step (l.154–221)

### 4.1 Matui 2006
H. Matui, *Some remarks on topological full groups of Cantor minimal systems*, Internat. J. Math. 17 (2006), no. 2,
231–251, doi:10.1142/S0129167X06003448 (Crossref via the fetch tool); arXiv:math/0404117v3.

**Verbatim (PT).**
- §3, AF setting (l.337–342): "The symmetric group S_{h(v)} has the normal subgroup A_{h(v)}, and so G_m has the normal
  subgroup H_m isomorphic to ⊕_{v∈V_m} A_{h(v)}." Then: "**Lemma 3.4.** In the above setting, the commutator subgroup
  D(G) equals to the union ∪H_m. Furthermore, D(G) is simple if the Bratteli diagram B is simple, or equivalently R is
  minimal."
- **Theorem 4.9** (l.559–586): "Let (X,ϕ) be a Cantor minimal system. The commutator subgroup D([[ϕ]]_0) is simple."
  The proof:
  - "Take a nontrivial element γ ∈ N."
  - "Choose a clopen neighborhood U of y which does not intersect with ϕ(U) and does not contain ϕ(y), γ(y), ϕ^{-1}γ(y)
    and ϕ^k(x) with |k| ≤ l+1."
  - σ is defined as ϕ on U, ϕ^{-1} on ϕ(U), and the identity elsewhere.
  - "From the construction, we infer that the commutator σγ^{-1}σγ belongs to ker sgn ∩ [[ϕ]]_x = D([[ϕ]]_x)."
  - "Besides, on account of σγ^{-1}σγ(y) = … = ϕ(y), the commutator σγ^{-1}σγ is not the identity. Then using Lemma 3.4
    shows that N contains D([[ϕ]]_x)."
- **Theorem 5.4** (l.698): finite generation of D([[ϕ]]_0) for minimal subshifts. The statement was completed through
  the fetch tool, not the text layer.

**Comparison with the note.**

| The note | Matui, Theorem 4.9 |
|---|---|
| h = e_ij(s), with s supported on a clopen C whose translates up to 2w+3 are disjoint (l.178–187) | σ supported on U ∪ ϕ(U), with U small and away from finitely many points |
| k = [g,h] ≠ 1 lies in I + M_3(B_m(U)), the corner over a finite tower (l.194–201) | σγ^{-1}σγ ≠ 1 lies in D([[ϕ]]_x), a union of alternating groups on Kakutani–Rokhlin towers (Lemma 3.4) |
| simplicity of GL_d(F_2) gives H_W ≤ N (l.217–221) | simplicity of D([[ϕ]]_x) gives D([[ϕ]]_x) ≤ N |
| the level ideal and simplicity of R give N = G (l.223–227) | minimality over the base points x gives N = D([[ϕ]]_0) |

**Verdict.**
- **The localization pattern is PRIOR.** A commutator with an element of small clopen support lands in a simple group
  living on towers. Matui 2006 does this for full groups; the commutator trick for homeomorphism groups is older
  (Higman, Epstein; recalled, not checked).
- **The matrix version for LC(X,F_2) ⋊ Z is NEW (bounded):**
  - corners M_{2m+1}(LC(U,F_2)) over towers, with the absorption (1);
  - the finite simple group GL_d(F_2) on a tower, and its generation by the transvections e_pq(E_ab(W));
  - the level ideal.
  No normal-structure theorem for EL_n over these rings was found (part 1 §1.2).

### 4.2 Stepanov 1997
A. V. Stepanov, J. Math. Sci. 95 (1999) 2146–2155; Zap. Nauchn. Sem. POMI 236 (1997). Read in full by un-novelty
(R: P).
- Theorem 4.4, with Lemmas 4.1 and 4.3, gives standard normal structure from linear-dependence conditions. Transvections
  are extracted from matrices with a zero-divisor entry.
- That is the extraction step of the Lean route `local-annihilation-makes-projective-el-simple`
  (`un-stepanov-credit-2026-09-13.md` §3). It is not the note's step: the note uses the finite simple group GL_d(F_2)
  and never Lemma 4.3.
- So l.61–62 ("an explicit elementary-matrix extraction argument, in the normal-structure tradition described by
  Stepanov") credits a tradition whose central lemma the proof does not use.
- Stepanov remains a fair source for the standard description of normal subgroups (§1.6(3), E(n,R,I) ≤ H ≤ C(n,R,I)).
  In the note that description belongs to the level-ideal step (l.223–227).

## 5. The word-problem corollary (l.229–262)

### 5.1 Grigorchuk–Medynets 2015/2018
R. Grigorchuk, K. Medynets, *Presentations of topological full groups by generators and relations*, J. Algebra 500
(2018) 46–68, doi:10.1016/j.jalgebra.2016.10.027 (Crossref via the fetch tool); arXiv:1508.04454.

**Verbatim (PT).**
- Abstract (l.12–15): "We show that the word problem in a topological full group is solvable if and only if the
  language of the underlying subshift is recursive."
- Theorem 1.1(3) (l.88–90): "The group G'_T has decidable word problem if and only if L(Ω) is recursive." The setting
  (l.47–53) is a minimal subshift (Ω,T) over a finite alphabet, with G'_T the commutator subgroup of its topological
  full group.
- Corollary 3.7 (l.637–642): for w = w_0⋯w_{n−1}, n ≥ 4, "w ∈ L(Ω) iff" an explicit iterated commutator of generators
  σ[·] "= 1 in G'_T". It is the counterpart of the note's lower bound (l.242–249), where a cylinder word gives an
  element that is trivial iff the word is illegal.

**Verdict.**
- The decidability form of "word problem versus language" is PRIOR for derived topological full groups of minimal
  subshifts.
- The degree-level equivalence for G_X is routine given the coefficient tables of R (l.240–242).
- As stated, for infinite simple Kazhdan LEF groups, it is NEW (bounded).

### 5.2 Every Turing degree; continuum many
- **Every degree as the word-problem degree of a finitely generated group:** classical (W). Not traced to a primary
  source here.
- **Every degree for finitely generated simple groups:** no source found, within three searches.
  - R. J. Thompson, *Embeddings into finitely generated simple groups which preserve the word problem*, Word Problems II
    (1980) 401–441, concerns solvable word problems (W).
  - Kuznetsov: a recursively presented simple group has solvable word problem (R). So the nonzero degrees in the note
    come from groups that are not recursively presented, which is consistent with the note.
- **Every degree for infinite simple Kazhdan LEF groups (the corollary):** NEW (bounded).
- **The Sturmian facts (l.251–256)** are classical (Morse–Hedlund; Lothaire ch. 2). The interleaving trick (l.257–260)
  is folklore.
- **Continuum many isomorphism classes (l.233–234).**
  - Finitely generated LEF groups: PRIOR. Bradford–Dona, *Topological full groups of minimal subshifts and quantifying
    local embeddings into finite groups*, Ergodic Theory Dynam. Systems 43 (2023) 1492–1510, arXiv:2106.09145 (A):
    "exhibit a continuum of finitely generated LEF groups which may be distinguished from one another by their LEF
    growth".
  - Property (T) groups: PRIOR (Ioana–Tucker-Drob, 2512.04531, A).
  - Infinite simple Kazhdan groups without LEF: not located (part 1 §1.1).
  - Infinite simple Kazhdan LEF groups: NEW (bounded). It is a routine corollary once the family exists, in agreement
    with `un-novelty-2026-09-13-part2.md` §4.3.

## 6. Novelty statements: what the note may claim, and what it must not

**May claim (NEW within the bound of part 1 §0).**
1. **Theorem 1.** The first infinite simple Kazhdan groups that are LEF, hence sofic and hyperlinear. This is a
   positive answer to Brown 2001 §11 Question 7, Ozawa 2003 and Pestov's Open question 9.1.
2. **Implied, not printed in the disk note.**
   - The first infinite simple Kazhdan MF groups: LEF ⇒ MF, as imported in the Palomar route from
     Carrión–Dadarlat–Eckhardt.
   - The first infinite LEF Kazhdan groups with no nontrivial finite quotient (R: ex-novelty (c)).
3. **Corollary.** Continuum many infinite simple Kazhdan LEF groups, with every Turing degree realized by their word
   problems.
4. **The matrix localization** over clopen towers of LC(X,F_2) ⋊ Z, as the simplicity step.

**Must credit, or must not claim as new.**
- (T): EJZ.
- Simplicity and centre of R: Clark–Edie-Michell, Steinberg, BCFS.
- Periodic approximation: GM 2014.
- The localization pattern of the simplicity proof: Matui 2006.
- The link between word problem and language: GM 2015/2018, at the level of decidability.
- Infinite finitely generated simple LEF groups as such: already known, since derived topological full groups of
  minimal subshifts are simple (Matui, Thm 4.9), finitely generated (Matui, Thm 5.4) and LEF (GM 2014, Thm 2.6). They
  are amenable (Juschenko–Monod), so Kazhdan is the new ingredient.

## 7. Bound of part 2
- Matui and GM15 were read in the text layer at the quoted passages only, not end to end.
- Crossref records came from `api.crossref.org` through the fetch tool.
- Not checked: the Higman/Epstein origin of the commutator trick, the Bezuglyi–Medynets simplicity proof, and a
  primary source for "every Turing degree for f.g. groups".
- The Juschenko–Monod bibliographic data in the proposal is recalled and needs a Crossref check.

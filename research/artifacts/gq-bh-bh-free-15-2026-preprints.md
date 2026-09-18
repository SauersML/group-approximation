# Two 2026 preliminary preprints on Boone–Higman, read at source

Lane `bh-free-15` (BH swarm, free lane), 2026-09-18. Both preprints are linked as
"preliminary" from F. Matucci's publication page and are not on arXiv. I fetched the
PDFs and read them page by page. Local copies are in the session scratchpad
(`gq/src/bh-free-15/`).
- `matucci-mandel-bh-theorem-decision.pdf` comes from the Google Drive link on the page.
- `bbcmp-continuous-automatic.pdf` comes from
  https://jimbelk.github.io/web/RationalEmbeddingsContinuousAutomaticPreliminary.pdf.

No priority claim is made. These are the authors' results; this artifact records
them for the swarm.

## 1. Mandel–Matucci, "The Boone–Higman theorem and decision problems" (dated 13 March 2026)

- **What it is.** It is NOT a proof of the Boone–Higman conjecture. "Boone–Higman
  theorem" there means the classical 1974 result (their Theorem 1.1, citing
  Boone–Higman Theorem I): a finitely generated group has decidable word problem
  if and only if it embeds in a simple subgroup of a finitely presented group.
- **Main result (Theorem 1.2).** Let G = ⟨X⟩ be finitely generated with decidable
  word problem. Let U be the set of finite sequences of nontrivial words, R ⊆ U
  recursively enumerable, and x a new letter. Then the following are equivalent:
  - (i) R is recursive;
  - (ii) G ∗ ⟨x⟩ embeds in a *finitely generated* simple subgroup S of a finitely
    presented group K such that, for w̄ = (w_1,…,w_n) ∈ U, w̄ ∈ R iff
    w_1 x w_2 x² ⋯ w_n xⁿ and w_1 x^{2n+1} w_2 x^{2n} ⋯ w_n x^{n+1} are not
    conjugate in K.
- **Application (Theorem 2.4).** Decidable knapsack problem ⟺ an embedding
  G ∗ ⟨x⟩ ↪ S ≤ K with S finitely generated simple and K finitely presented, with
  the analogous conjugacy criterion.
- **Relevant to `bh-higman-classic` and `bh-logic`.** Footnote 1 (p. 2): "Although
  the simple subgroup S in the statement of [Sacerdote, Proposition 2] is claimed
  to be finitely generated, this claim is not proved." Their Theorem 1.2 does give
  a *finitely generated* simple S inside a finitely presented K.
  - Any repo node that imports Sacerdote for a finitely generated simple envelope
    should cite Mandel–Matucci instead, or record the gap.
  - Grep before relying on it: `git grep -n Sacerdote origin/main -- research`.

## 2. Belk–Bleak–Chatterji–Matucci–Perego, "Rational embeddings of continuous automatic groups" (preliminary version)

**Definitions (§1.1).**
- A language of normal forms L ⊆ X* is *continuous* if the left action of G on L
  extends to a continuous action on L ∪ ∂L. Prop 1.3 / Prop 2.1 give a criterion by
  greatest common prefixes.
- G is *continuous (asynchronous) automatic* if it has an (asynchronous) automatic
  structure that is a continuous normal form. ∂L is then its *rational boundary*.

**Main results (numbers as printed).**
- **Prop 1.4.** Closure properties:
  - finite groups and Z are continuous automatic;
  - the class is closed under commensurability, direct products and free products;
  - for |G| ≥ 2 and |H| ≥ 3, G ∗ H acts faithfully on its normal form boundary.
  - The same holds in the asynchronous setting.
- **Theorems 1.6 and 1.7, Corollary 1.8.**
  - For a closed rational E ⊆ X^ω, the rational homeomorphisms of E form a group R_E,
    isomorphic to the Grigorchuk–Nekrashevych–Sushchanskiĭ rational group when E has
    no isolated points.
  - A homeomorphism of E is rational iff its graph is a deterministic rational set.
  - Continuous asynchronous automatic groups act on ∂L by rational homeomorphisms.
- **Corollary 1.9.** Every continuous asynchronous automatic group embeds in the
  rational group. The proof goes through G ∗ Z, using Cor 1.5 and Cor 2.11.
- **Theorem 1.10 / 2.3.** Every BS(m,n) is continuous asynchronous automatic.
  - The normal form boundary is the ends of the Bass–Serre tree, and the action is
    faithful.
  - The authors add that the Bux–Llosa Isenrich–Wu proof "can be modified to show"
    that the full group [[BS(m,n) | ∂L]] is finitely presented.
- **Theorem 1.11 / 2.4.** Every Artin group of finite type is continuous automatic,
  via the Deligne normal form Δ^{-j} x_1 ⋯ x_n over X = (1,Δ] ∪ {Δ^{-1}}.
  - ∂L is a shift of finite type.
  - A acts faithfully on ∂L when it has at least two generators.
- **Theorem 1.13.** Every virtually torsion-free cubulated group is continuous
  automatic, via the Niblo–Reeves structure.
- **Theorem 1.14.** The boundary of the normal diagonal tree is the Roller boundary.

**What they do NOT prove, in their own words (p. 2).** "we do not prove any
Boone–Higman results here." They do not prove that any topological full group
[[G | ∂G]] is finitely presented. "the actions are not contracting — so new
techniques will be needed to prove finite presentability." And (p. 7): "Even for
braid groups, we do not know whether the corresponding topological full group
[[A | ∂L]] is finitely presented."

**Named open questions (new to the swarm; not in `gq-bh-bh-lit-survey.md`).**
- **Question 1.12.** "Does every Artin group of finite type admit an embedding into a
  finitely presented simple group?"
  - Just before it (p. 7): "it is an open problem whether exceptional Artin groups of
    finite type (E_6, E_7, E_8, F_4, and H_4) admit embeddings into finitely
    presented simple groups."
  - This independently confirms bh-lit's finding F1: in the literature, spherical
    exceptional types are OPEN. The repo marks them ESTABLISHED through
    `spherical-artin-groups-satisfy-boone-higman` ← char-0 linear. `bh-verify-artin`
    and `bh-verify-linear` should cite Q1.12.
- **Question 1.15.** "Does every virtually torsion-free cubulated group admit an
  embedding into a finitely presented simple group?"
  - Relevant to `bh-cat0` and survey Problem 5.3(10).
  - Virtually special cubulated groups are linear over Z, hence BH by Scott, so the
    content is the non-virtually-special case (e.g. irreducible lattices in products
    of trees).
- **Question 1.16.** "Are mapping class groups of finite-type surfaces continuous
  automatic? Do all such groups admit embeddings into finitely presented simple
  groups?"
  - Relevant to `bh-mcg`. Mosher: mapping class groups are automatic.

## 3. Consequence for the automatic-groups route (survey 5.3(11))

`automatic-groups-satisfy-boone-higman` (OPEN) says "No structural method uses
automaticity itself." BBCMP supply the first structural step for the continuous
subclass, which is a rational boundary action. The missing step is finite presentation
of [[G | ∂L]], or an embedding of it into a finitely presented simple twisted
Brin–Thompson group, in the non-contracting case.

A structural fact for the finite-type Artin case is proved in
`artin-normal-form-boundary-full-groups-fix-a-point` (this lane):
- Δ^{-∞} is a global fixed point of A on ∂L.
- Every element of [[A | ∂L]] fixes it.
- The germ map there has infinite image, so [[A | ∂L]] is never simple.
- So a Boone–Higman host for A through this boundary must come either from the
  G ∗ Z boundary of BBCMP Theorem 2.9, which is Cantor with a faithful action, or from
  a further twisted Brin–Thompson step, as BBCMP suggest on p. 6.

Tools already in the scratchpad (`gq/src/kep/`) for the finiteness step:
- X. Li, "Left regular representations of Garside categories II. Finiteness
  properties of topological full groups" (arXiv:2110.04505v2):
  - Theorem A (Garside structure on the category of bisections);
  - Theorem B, which says F(I_l ⋉ ∂Ω) is F_n when the isotropy of invertibles is F_n,
    under (F), (St), (LCM) and (t<d);
  - Corollary C (degree maps; needs at least 2 elements of each Garside degree at
    each vertex);
  - the Zappa–Szép corollary.
- Li's paper never treats Artin monoids. The only mention is the K(π,1)
  bibliography, and the degree-map corollary fails for C = A^+ itself, which has
  exactly one element per degree.
- Whether a Garside-category model of the Deligne boundary satisfies Li's
  hypotheses is OPEN and unexplored. It is the natural next step for anyone taking
  BBCMP Q1.12 through full groups.

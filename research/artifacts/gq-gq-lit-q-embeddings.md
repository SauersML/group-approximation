# Known explicit embeddings of (Q,+) into finitely presented groups: mechanisms (lane gq-lit-q-embeddings, 2026-09-17)

Target context: `gl-n-q-embeds-in-fp-simple-group` (GL_n(Q), n >= 2, in a finitely presented simple group) and
Problem 2.7 of the Belk–Bleak–Matucci–Zaremsky survey (an explicit, natural finitely presented group containing
GL_n(Q)). This artifact records, for every known explicit embedding of (Q,+), what the construction is, **which
ingredient supplies divisibility**, and whether it can reach Q^n, Aff(Q) = Q ⋊ Q^x, U_3(Q) or GL_2(Q).

## 0. Sources and method

Read on 2026-09-17 through arXiv abstract pages, arXiv HTML pages, and the ar5iv HTML rendering. No PDF was read
locally, and there was no MathSciNet or zbMATH access. The raw PDF of arXiv:2005.02036 could not be parsed by the
fetch tool, and a first summary produced from it was unreliable, so it was discarded. Every quotation below comes
from an HTML rendering and is marked as a quotation.

| Paper | Versions seen | Status here |
|---|---|---|
| Belk–Hyde–Matucci, *Embedding Q into a finitely presented group*, arXiv:2005.02036, Bull. AMS 59 (2022) 561–567 | v1 2020-05-05 … v4 2022-03-28 | read (ar5iv): statements, key proofs |
| Belk–Hyde–Matucci, *Finite germ extensions*, arXiv:2407.03149 | v1 2024-07-03 | abstract only (lane gq-lit-hosts owns the theorems) |
| Kojima–Sheng, *On subgroups of Brin–Thompson groups nV*, arXiv:2603.18410 | v1 2026-03-19, v2 2026-04-20, v3 2026-05-23 | abstract; HTML v3 main theorems and a summary of the construction |
| Mikaelian, *On a problem on explicit embeddings of the group Q*, IJMMS 2005(13), 2119–2123 | — | abstract only |
| Mikaelian, *On explicit embeddings of Q into finitely presented groups*, arXiv:2310.10536 | v1 2023-10-16, v2 2023-10-17 | abstract; ar5iv (presentation of Q, overall structure) |
| Mikaelian, *An explicit algorithm for the Higman Embedding Theorem*, arXiv:2507.04347 | v1 2025-07-06 … v8 2026-06-03 | abstract; HTML v8 §§1.3–1.4 |
| Mikaelian, arXiv:2002.09728 (Higman operations), arXiv:2308.10532 (talk summary) | — | abstracts only |
| D. L. Johnson, *Embedding some recursively presented groups*, Groups St Andrews 1997 in Bath, Vol. 2, LMS LN 261 (1999) 410–416 | — | not read (paywalled); known only through the quotation in §4 |

## 1. Belk–Hyde–Matucci: Q ≤ T̄ (arXiv:2005.02036)

### 1.1 The group

> "T̄ consists of all homeomorphisms f:ℝ→ℝ that satisfy the following conditions: (1) The homeomorphism f is
> piecewise-linear, with finitely many breakpoints on each compact interval. (2) Each linear portion of f has the
> form f(x)=2ⁿx+d, where n∈ℤ and d is a dyadic rational. (3) Each breakpoint of f has dyadic rational coordinates.
> (4) The homeomorphism f commutes with the translation x↦x+1."

> "Let PL₂(ℝ) denote the (uncountable) group of all piecewise-linear homeomorphisms of ℝ that satisfy conditions
> (1) through (3) for elements of T̄ given in the introduction."

So **T̄ is the centralizer of z = (x ↦ x+1) in PL₂(ℝ)**. It is a central extension of Thompson's T by ⟨z⟩ ≅ Z.

### 1.2 Finite presentation

> "T̄ is an explicit group of homeomorphisms of the real line, which has a presentation with two generators and
> four relators (see Remark 3 below)."

> "T̄ = ⟨a,b | a⁴=b³, (ba)⁵=b⁹, [bab,a²baba²]=[bab,a²b²a²baba²ba²]=1⟩"

This is derived from the Lochak–Schneps presentation of T (two generators, five relators; corrected in their
reference [8, Proposition 1.3]) together with the central extension.

### 1.3 Statements

> **Theorem 1.** "The group T̄ has continuum many different subgroups isomorphic to ℚ, all of which contain the
> center of T̄."
>
> **Corollary 2.** "The automorphism group of Thompson's group F has a subgroup isomorphic to ℚ."
>
> **Lemma 6.** "Let g be an element of PL₂(ℝ) without fixed points and let n≥2. Then there exist infinitely many
> different f∈PL₂(ℝ) such that fⁿ=g."
>
> **Lemma 7.** "Let m≥1 and let g∈T̄ so that gᵐ=z. Then for every n≥2 there exist infinitely many different f∈T̄
> so that fⁿ=g."
>
> **Proposition 8.** "The group T̄ has continuum many subgroups isomorphic to ℚ."
>
> **Proposition 13.** "Every subgroup of T̄ isomorphic to ℚ contains the center of T̄."

### 1.4 The divisibility mechanism

**Roots in the flexible ambient group (Lemma 6).** The proof builds an n-th root of a fixed-point-free g on one
fundamental domain [0, g(0)] and spreads it by g:

> "Choose dyadic rationals 0 = p₀ < p₁ < ⋯ < pₙ = g(0), and for each 1 ≤ i < n choose a Thompson-like
> homeomorphism fᵢ: [pᵢ₋₁, pᵢ] → [pᵢ, pᵢ₊₁]. Let fₙ: [pₙ₋₁, pₙ] → [pₙ, g(p₁)] be the homeomorphism
> gf₁⁻¹f₂⁻¹⋯fₙ₋₁⁻¹, and let f ∈ PL₂(ℝ) be the homeomorphism that agrees with fᵢ on each [pᵢ₋₁, pᵢ] (1 ≤ i ≤ n)
> and satisfies f(x) = gᵏfg⁻ᵏ(x) for each x ∈ [gᵏ(0), gᵏ⁺¹(0)] with k ≠ 0."

**Roots land in the finitely presented subgroup automatically (Lemma 7).** The centralizer trick:

> "Note that g cannot have any fixed points, since these would also be fixed points of z. Therefore, by Lemma 6,
> there exist infinitely many f ∈ PL₂(ℝ) such that fⁿ = g. Any such homeomorphism commutes with z since fᵐⁿ = z,
> and therefore every such f lies in T̄."

**The tower (Proposition 8).**

> "To obtain an embedding of ℚ into T̄ it suffices to find a sequence {sₙ}ₙ∈ℕ of elements of T̄ such that s₁ has
> infinite order and sₙⁿ=sₙ₋₁ for all n≥2. Such a sequence can be defined recursively by letting s₁=z and then
> repeatedly applying Lemma 7 to find, for each n≥2, an element sₙ∈T̄ such that sₙⁿ=sₙ₋₁."

So divisibility comes from three things together:
1. an **uncountable, flexible ambient group**, PL₂(ℝ), in which every fixed-point-free element has roots of every
   order, built on a fundamental domain;
2. a **finitely presented subgroup defined as a centralizer**, T̄ = C(z), which contains every root of every
   power of z for free, since a root of a power of z commutes with z;
3. the **central element z** as the bottom of the tower, s₁ = z.

### 1.5 Rigidity: every Q in T̄ goes through the centre (Proposition 13)

Why Q is not in T, and how z is forced:

> "Higman proved that elements of Thompson's group V of infinite order do not have roots of arbitrarily large
> orders. It follows that ℚ does not embed into V, and hence ℚ does not embed into T, either."

> "Since f and z commute it follows that (fz⁻¹)ⁿ = 1, and since T̄ is torsion-free we conclude that fz⁻¹ = 1,
> and therefore A contains z."

Here A ≅ Q is the subgroup. A → T is not injective, so A contains some zⁿ ≠ 1, and divisibility plus
torsion-freeness give z ∈ A. **Consequence (§6 and the node `aff-q-does-not-embed-in-aut-thompson-f`):** T̄ holds
only one "line" of divisibility, and that line is central. So it contains no Q², no U_3(Q), and no Q normalized by
an element scaling it.

### 1.6 Brin's group A = Aut₊(F), and the simple hosts

> "Brin has proven that T̄ embeds naturally into the automorphism group of Thompson's group F. Specifically, Brin
> proved [5, Theorem 1] that Aut(F) has an index-two subgroup Aut₊(F) which is isomorphic to the group of all
> homeomorphisms of ℝ that satisfy conditions (1), (2), and (3) above and agree with elements of T̄ in
> neighborhoods of −∞ and ∞."

> "Brin also showed [5, Theorem 1] that this group Aut₊(F) fits into a short exact sequence
> 1 → F → Aut₊(F) → T × T → 1, and it follows easily that Aut(F) is finitely presented. Indeed, Burillo and
> Cleary have computed an explicit finite presentation for Aut(F) in [4]."

> **Remark 4 (opening).** "In addition to the above results, we have obtained an explicit embedding of T̄ and hence
> an embedding of ℚ into a finitely presented simple group T𝒜, verifying the Boone-Higman conjecture in the case
> of ℚ. We have also obtained an explicit finitely presented simple group V𝒜 that contains all countable abelian
> groups."

The group V𝒜 is the one of *Finite germ extensions* (arXiv:2407.03149, abstract: "we describe a specific
2-generated, F_∞ simple group VA of homeomorphisms of the Cantor set that contains every countable abelian group").
By the survey (§4.3), VA contains all countable abelian groups because Q ≤ T̄ ≤ A ≤ VA, Q/Z ≤ V ≤ VA, and
⊕_ω VA ≤ VA by disjoint supports. **Divisibility in VA is exactly BHM's T̄ mechanism, multiplied by disjoint
supports.**

## 2. Kojima–Sheng: Q ≤ nV for n ≥ 2 (arXiv:2603.18410)

**Abstract (v3), verbatim.** "We prove that the Brin-Thompson group $nV$ is torsion locally finite for $ n \geq 1$
which is known only when $n = 1$, and $nV$ contains continuum many copies of the additive group of the rationals
$\mathbb{Q}$ for $n \geq 2$ which is known to be false for the $n = 1$ case."

The comments field of v3 reads: "The second claim has been upgraded, 18 pages, 9 figures, Section.5 is deleted."
An earlier version gave only the dyadic rationals Z[1/2] and "elements of infinite order admitting roots with
arbitrary large order". Cite **v3** for Q.

**Main theorems (HTML v3).**
- Theorem 1.1: "nV is torsion locally finite for n≥1".
- Theorem 1.2: "For n≥2, the Brin-Thompson group nV contains continuum many copies of the additive group of the
  rationals ℚ sharing the subgroup isomorphic to ℤ."

**Mechanism.** This is a summary of the HTML page, not verbatim. Check it against the source before relying on
details.
- They build an ascending chain of infinite cyclic groups ⟨s_1⟩ < ⟨s_2⟩ < ⋯ in 2V, where s_k is a root of s_{k−1}
  of order k. The page speaks of "a root of s_{k−1} of order k!", matching the presentation of Q by generators
  1/k!.
- The roots are built from two-dimensional dyadic "block" pictures. A vertical subdivision of the blocks makes
  room for a root, and a horizontal scaling plus a finite-order rotation of the block labels closes it up. The
  construction is iterated with nested block patterns L_{1,2,…,k}.
- **Where dimension 2 is used.** In V, Higman's theorem bounds the orders of roots of an infinite-order element.
  In 2V the second coordinate gives the room to subdivide that 1D rigidity forbids.

**Features relevant to GL_n(Q).**
- Like BHM's Proposition 13, the copies of Q share one infinite cyclic subgroup. It is not stated that **every**
  copy of Q in 2V meets a fixed Z, and 2V has trivial centre, so no "central line" rigidity is known here.
- 2V contains ⊕_ω 2V (disjoint supports), so Q^(ω) ≤ 2V follows from Theorem 1.2.
- 2V is finitely presented (Brin, Hennig–Matucci) and simple (Brin; survey §4.4). So Q ≤ 2V is a second
  embedding of Q into a finitely presented simple group, after BHM's TA and VA.

## 3. Mikaelian: combinatorial explicit Higman embeddings

### 3.1 IJMMS 2005: Q into a 2-generator (finitely generated, not finitely presented) group

Abstract: "Answering a question of de la Harpe and Bridson in the Kourovka Notebook, we build the explicit
embeddings of the additive group of rational numbers ℚ in a finitely generated group G. The group G in fact is
two-generator, and the constructed embedding can be subnormal and preserve a few properties such as solubility or
torsion freeness."

This is the survey's reference [Mik] ("Higman's construction can be carried out explicitly (see [Mik])"). The
target group is **finitely generated, not finitely presented**.

### 3.2 arXiv:2310.10536 (2023): Q into explicit finitely presented groups 𝒬 and T_𝒬

Abstract: "Explicit embeddings of the group $\mathbb{Q}$ into a finitely presented group $\mathcal{Q}$ and into a
$2$-generator finitely presented group $T_{\mathcal{Q}}$ are suggested."

- **Input presentation (quoted from ar5iv).** "ℚ=⟨x₁,x₂,…|xₖᵏ=xₖ₋₁, k=2,3…⟩". Here x_k corresponds to 1/k!.
- **Step 1.** Embed this recursive presentation in a 2-generator recursively presented group, by Mikaelian's
  universal-words method (arXiv:2002.09433).
- **Step 2.** Encode that group's relators as a recursively enumerable set 𝒯 of integer sequences. Prove that the
  subgroup A_𝒯 = ⟨a_f : f ∈ 𝒯⟩ of a free group is **benign**, by an explicit chain of Higman operations (the ar5iv
  page names ζ₁, τ, ω₂, σ⁻¹, §§4–7).
- **Step 3.** Higman's benign-subgroup machinery (amalgams, HNN extensions, Mikaelian's ∗-constructions) turns
  that into explicit finite presentations. The ar5iv page reports 98 generators for 𝒬 in §9.1. That count is not
  re-checked here.

Mikaelian's own summary of prior attempts (quoted from ar5iv): "However, our main aim of embedding of Q into a
finitely presented group continued to elude us also".

### 3.3 arXiv:2507.04347 (2025–26): the explicit Higman algorithm, and the GL(n,Q) announcement

Abstract (excerpt): "We propose an algorithm which for any recursive group $G$, given by its effectively
enumerable generators and recursively enumerable relations, outputs an explicit embedding of $G$ into a finitely
presented group directly written by its generators and defining relations. … The constructed finitely presented
group can even be chosen to be $2$-generator. This algorithm has already been applied, for example, to the
additive group of rational numbers $\mathbb Q$ …"

§1.4 (HTML v8), verbatim:
- "Find an explicit and "natural" finitely presented group Γₙ and an embedding of GL(n,ℚ) in Γₙ."
- "We would like to announce that, as another application of Algorithm 1.1, an explicit embedding of GL(n,ℚ) into
  some finitely presented Γₙ reflecting this question is suggested."
- "Moreover, that group Γₙ can even be 2-generator [41]."

§1.3 (HTML v8), verbatim: "The steps of Algorithm 1.1 have been applied for the group ℚ in [39]: a finitely
presented group 𝒬, and a finitely presented 2-generator group T𝒬 with the embeddings φ:ℚ→𝒬 and ψ:ℚ→T𝒬 are
explicitly given in sections 9.1 and 9.2 in [39]."

(Lane gq-lit-arxiv reports that [41] is not posted as of 2026-09-17; see
`research/artifacts/gq-gq-lit-arxiv-priority.md`.)

### 3.4 The divisibility mechanism

**None beyond the input.** Divisibility is written into the relators x_k^k = x_{k−1}, and the machinery transports
any recursive presentation into a finitely presented group.
- This is universal: it applies verbatim to Q^n, Aff(Q), U_3(Q) and GL_n(Q), and §1.4 announces GL(n,Q).
- It yields no simplicity. Amalgam and HNN constructions are far from simple.
- It yields no "naturality": the group depends on a coding of 𝒯 through Higman operations.
- For G (simplicity) it adds nothing beyond Higman–Clapham. For G' it at best settles the "explicit" half, and
  only once [41] appears.

## 4. Johnson and Higman: the question

D. L. Johnson (Groups St Andrews 1997, published 1999) worked on explicit embeddings of recursively presented
groups. As quoted by Mikaelian (arXiv:2310.10536, ar5iv): "Our main aim, of embedding in a finitely presented group
the additive group of rational numbers continues to elude us". Mikaelian adds: "The task of finding an explicit
embedding of that type for Q goes back to Graham Higman himself". The survey (§2) says the same: "Higman was for many
years interested in finding a more explicit and natural example of a finitely presented group that contains Q
[Johnson]". Johnson's paper was not read here (paywalled), and **no Johnson construction of Q in a finitely
presented group is known to this lane**.

De la Harpe's version, quoted by Mikaelian: "We can also record the well-known problem of finding a natural and
explicit embedding of Q in a finitely-presented group". Bridson–de la Harpe, Kourovka 14.10: "Find an explicit and
'natural' finitely presented group Γ and an embedding of the additive group of the rationals Q in Γ."

## 5. Divisibility engines, side by side

| Engine | Where | What makes roots exist | Why the roots are in the f.p. group | Simple host |
|---|---|---|---|---|
| E1. Centralizer of a flexible element | BHM, T̄ = C_{PL₂(ℝ)}(z) | fundamental-domain roots of fixed-point-free elements in the uncountable PL₂(ℝ) (Lemma 6) | a root of a power of z commutes with z (Lemma 7) | TA, VA (BHM) |
| E2. Two-dimensional room | Kojima–Sheng, Q ≤ nV, n ≥ 2 | subdividing a second coordinate: nested dyadic block patterns | constructed directly as tables of nV | nV itself |
| E3. Relators | Mikaelian (and Higman) | the input relators x_k^k = x_{k−1} | benign subgroups via Higman operations | none |
| E4. Disjoint supports | VA ⊇ ⊕_ω VA, nV ⊇ ⊕_ω nV | inherited | inherited | VA, nV |

Only E3 is indifferent to the group being embedded. E1 and E2 are geometric. They produce **abelian** divisible
subgroups, and in T̄ (E1) only one central line of them.

## 6. Reach: Q^n, Aff(Q), U_3(Q), GL_2(Q)

"Excluded" means proved impossible. The proofs are in node `aff-q-does-not-embed-in-aut-thompson-f` (lane proof,
not independently reviewed) unless another source is named.

| Host | Q^n (n ≥ 2) | Aff(Q) | U_3(Q) | GL_2(Q) | GL_n(Q), n ≥ 3 |
|---|---|---|---|---|---|
| V, T, F | excluded (Q ⊄ V, Higman) | excluded | excluded | excluded | excluded |
| T̄ | **excluded** (every Q ≤ T̄ contains the centre, Prop. 13) | **excluded** | **excluded** (contains Q²) | **excluded** | excluded |
| Aut(F) ⊇ Brin's A = Aut₊(F) | not decided here (§7, spark S2) | **excluded** | excluded (O4, via index 2) | **excluded** | excluded |
| VA | yes (⊕_ω Q ≤ VA, survey §4.3) | excluded (O4) | excluded (O4) | excluded (O4) | excluded (SL_3(Z), survey Remark 4.12; also O4) |
| 2V, nV (n ≥ 2) | yes (Kojima–Sheng + disjoint supports) | open (O4 does not apply: nV has distorted cyclic subgroups; see `bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets` and root Attempts item 11) | open | open | open (see `gl-3-z-in-no-nv-via-cnd-transversal`) |
| Mikaelian's explicit Higman groups | yes, in principle | yes, in principle | yes, in principle | announced (arXiv:2507.04347 §1.4, no construction yet) | announced |

**Update (2026-09-17, after landing).** Root obstruction O4 (2688d4128; Burillo–Felipe, arXiv:2605.09763v1,
unrefereed) settles the VA row: VA contains no group with distorted cyclic subgroups, and BS(1,2) ≤ Aff(Q),
the Heisenberg group ≤ U_3(Q). So VA and all its subgroups (V, T̄, Brin's A) omit Aff(Q), U_3(Q) and GL_n(Q) for
every n ≥ 2. The T̄ and Aut(F) exclusions above have a proof independent of O4. The Q² exclusion for T̄ is not
implied by O4. Correction received from lane gq-va-affq.

**Reading of the table.**
1. Both geometric engines produce divisibility only along **abelian** lines. GL_2(Q) needs a Q that is
   normalized by an element scaling it (the torus acting on a root group), and U_3(Q) needs non-central Q's whose
   commutators land in a central Q.
2. T̄ and Brin's A fail exactly there. Every Q in T̄ is forced through the centre, and every Q in A is seen
   faithfully by one of the two end-germ maps A → T̄.
3. So a host for GL_2(Q) needs a divisibility engine that **commutes with a dilation**: an element d and a root
   tower s_k with d s_k d^{-1} = s_k^{λ}. E1 cannot supply this, because d does not centralize z. It is untested
   for E2.
4. For every n ≥ 2, VA, V and every subgroup of them are excluded (O4; for n ≥ 3 also O2). The hosts left are twisted Brin–Thompson groups,
   nV, Röver–Nekrashevych-type groups with non-RF germs, and new constructions.

## 7. Sparks (ideas not pursued by this lane; free to adopt)

- **S1 (E1 with a dilation: the commensurator of ⟨z⟩).** Replace the centralizer T̄ = C(z) by the commensurator
  Comm(⟨z⟩) in PL₂(ℝ): the dyadic PL homeomorphisms h with h(x + a) = h(x) + b for some integers a, b ≥ 1. It
  contains T̄ and x ↦ 2x, and x ↦ 2x conjugates z to z². Questions:
  - Can root towers be chosen compatibly with the dilation, d s_k d^{-1} = s_k^2, which would give BS-type
    divisibility and Aff(Z[1/2]-ish)-structure?
  - Is some finitely generated subgroup finitely presented?

  Natural owners: gq-tbar-lift-n or gq-pp-lift.

  **Status.** Answered negatively for Aff(Q) by `commensurating-end-germ-groups-omit-aff-q` (780e84702; lane
  proof, rests on arXiv:2605.09763v1). No finitely generated subgroup of the germ group Comm_inf contains
  Aff_K(Q) = Q ⋊ K for any non-finitely-generated K ≤ Q^x_{>0}. That covers Aff(Q), GL_2(Q), SL_2(Q),
  PSL_2(Q), and GL_n(Q), SL_n(Q), B_n(Q) for n ≥ 2. Q ⋊_a Z for a single dilation a is still open there.
- **S2 (Q² in Brin's A by half-line supports).** Build BHM's root tower on (0, ∞) only: start from an element equal
  to z near +∞ and to the identity on (−∞, 0]. Run Lemma 6 on its support (each root has the same support, Step 0
  of the proof node). Then mirror on (−∞, 0). Commuting copies with disjoint supports would give Q² ≤ Aut₊(F).
  One check is still needed: that roots of an element equal to z near +∞ agree with a T̄-element near +∞. They
  commute with it there, so this looks right. Relevant to gq-q-in-germs and gq-va-affq.
- **S3 (E2 and dilations).** In 2V the baker's-map-type elements exchange scales between the two coordinates. Is
  there d ∈ 2V with d s_k d^{-1} = s_k^2 for a Kojima–Sheng tower? That would put Z[1/2]-type affine divisibility,
  and possibly Aff(Q), in a finitely presented simple group. Natural owner: gq-bt-kojima.

  **Status.** Root Attempts item 11 records that `BS(1,2) ≤ nV` needs a drift-free infinite-order base
  (D(a) = kD(a) when a ~ a^k), so Kojima–Sheng towers over elements of V never give its translation subgroup.
- **S4 (Problem 2.7).** E3 (Mikaelian) settles "explicit" once [41] appears. "Natural" is still open and is where
  the geometric engines matter. A natural answer for GL_2(Q) must avoid T̄ and Aut(F) (§6).

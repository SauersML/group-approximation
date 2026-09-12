# Kun–Thom, arXiv:2608.06222v1 — source-verified statement record

G. Kun and A. Thom, *Nonsofic wreath products of residually finite groups*,
arXiv:2608.06222, submitted 6 August 2026.

Provenance of this record: the statements below were read on **2026-08-14**
directly from `https://arxiv.org/abs/2608.06222` (abstract) and
`https://arxiv.org/html/2608.06222v1` (full text). They are transcribed
verbatim. An independent earlier fetch of Theorem 4.1 (2026-08-08) is
recorded in `notes/NOTEPAD.md` and agrees word for word; the abstract
independently paraphrases Theorems A and E, which corroborates both.

**Trust surface.** This is an external, unrefereed preprint eight days old at
the time of transcription, and it is not kernel-checked anywhere in this
repository. Every claim in this graph that rests on it inherits that
surface, and it should be re-verified against any later version. This is the
same class of risk that the withdrawal of arXiv:2510.17003 illustrated.

## Abstract (verbatim)

> This work builds on the breakthrough of OpenAI in finding the first
> nonsofic group. We analyze the underlying proof mechanism and find further
> applications. Let Γ<G be such that {g∈G:gΓg⁻¹≤Γ} generates G as a group,
> and suppose that both Γ and G have property (T). If Γ is not normal, then
> the generalized wreath product (⊕_{G/Γ}ℤ/2ℤ)⋊G is nonsofic. These
> hypotheses hold for explicit pairs of elementary groups over polynomial and
> Laurent polynomial rings, in which both groups are residually finite and
> Kazhdan.

## Definition — infranormal (verbatim)

> For a subgroup Γ<G, the set P_Γ={g∈G:gΓg^{-1}≤Γ} is a semigroup, called the
> compression semigroup of Γ. We call Γ an infranormal subgroup of G if P_Γ
> generates G as a group.

## Theorem A (verbatim)

> Let Γ be an infranormal but not normal subgroup of G, and suppose that both
> Γ and G have Kazhdan's property (T). Then (ℤ/2ℤ)≀_{G/Γ}G is not sofic.

## Theorem B (verbatim)

> Let G be a sofic group with Kazhdan's property (T), and let Γ≤G be an
> infranormal subgroup with Kazhdan's property (T). Then C_G(Γ) is normal in G.

## Theorem C (verbatim)

> Let Γ be an infranormal subgroup of G, and suppose that both Γ and G have
> Kazhdan's property (T). If G↷(X,μ) is a sofic p.m.p. action, then the
> fixed-point algebra L^∞(X)^Γ is G-invariant.

## Corollary D (verbatim)

> Under the assumptions of Theorem C, suppose in addition that Γ is not normal
> in G. If (K,κ) is a nontrivial standard probability space, then the
> generalized Bernoulli action G↷(K,κ)^{G/Γ} is not sofic.

## Theorem E (verbatim)

> Let q be a prime power and let r,d≥3. Put R₊=𝔽_q[x₁,…,x_d] and
> R=𝔽_q[x₁^{±1},…,x_d^{±1}], and let SL_d(ℤ) act on R by monomial
> substitutions. Then Γ=EL_r(R₊) and G=EL_r(R)⋊SL_d(ℤ) are residually finite
> Kazhdan groups, Γ is infranormal but not normal in G.

## Theorem 4.1 (verbatim)

> Let Γ be an infranormal subgroup of G, and suppose that both Γ and G have
> Kazhdan's property (T). If σ:G→𝒮_𝒰 is a sofic representation, then
> C_{𝒮_𝒰}(σ(Γ)) is normalized by σ(G).

## Definition of a sofic p.m.p. action, as used by C and D (verbatim fragments)

> A p.m.p. action G↷(X,μ) is sofic if there are finite sets Y_n and an
> embedding Θ:L^∞(X)⋊G→∏_{n→𝒰}M_{|Y_n|}(ℂ)

> D_{𝒰}=∏_{n→𝒰}(D_{Y_n},tr)⊆∏_{n→𝒰}(M_{|Y_n|}(ℂ),tr) for the diagonal tracial
> ultraproduct.

> The crossed product below is the von Neumann crossed product, and an
> embedding is a unital trace-preserving ∗-embedding.

This is Păunescu's notion. Păunescu, *On sofic actions and equivalence
relations*, arXiv:1002.0605, Definition 1.4 (verbatim, read 2026-08-14):

> An action α of a countable group G on a standard Borelian space (X,ℬ,μ) is
> called *sofic* if the crossed product L^∞(X)⋊_α G embeds in
> Π_{k→ω}M_{n_k}(ℂ) such that L^∞(X)⊂Π_{k→ω}D_{n_k}(ℂ) and
> G⊂Π_{k→ω}P_{n_k}(ℂ).

with Notation 1.2: `P_{n_k}⊂M_{n_k}` is the subgroup of **permutation**
matrices, and the following sentence: *"So for an action to be sofic instead
of simply hyperlinear we want that the unitaries implementing the action, to
be permutation matrices."*

## Table of contents (verbatim)

> 1. Introduction
> 2. Sofic actions and expander decompositions
> 3. Fixed-point algebras and nonsofic actions
> 4. Normalization of permutation centralizers
> 5. Nonsofic wreath products and examples

## What the paper does NOT contain

Checked by keyword search of the full HTML: the paper makes **no** claim
about hyperlinearity of the wreath product, and **no** claim about Connes
embeddability of its group von Neumann algebra. It contains no
operator-norm / MF content. The only occurrence of "Connes" is inside a
bibliography entry for an unrelated reference.

## Adjacent statements verified from source on 2026-08-14

Used by `coordinate-action-not-sofic` and by the toolkit verdicts in
`hyperlinear-wreath-model`. Each was read in the authors' own arXiv e-print
source.

**Gao–Kunnawalkam Elayavalli–Patchell**, *Soficity for group actions on sets
and applications*, arXiv:2401.04945, *Res. Math. Sci.* (2025).

Theorem A (= Theorem 3.6), verbatim:

> Let G, H be sofic groups, α: H ↷ X be a sofic action. Then the generalized
> wreath product G ≀_α H is sofic.

Theorem 3.8, verbatim:

> Let (M, τ) be a Connes-embeddable tracial von Neumann algebra, H be a
> hyperlinear group, α: H ↷ X be a sofic action. Then the generalized wreath
> product M ≀_α H is Connes-embeddable. In particular, if G, H are hyperlinear
> groups and α: H ↷ X is a sofic action, then the generalized wreath product
> G ≀_α H is hyperlinear.

Definition 2.1(5), verbatim (their finitary notion of a sofic action on a
**set**; note it carries no injectivity/separation clause on φ):

> α is called *sofic* if for all finite subsets F ⊆ G, E ⊆ X, and ε > 0, there
> exists a finite set A and a map φ: G → Sym(A) which is unital,
> (F, ε)-multiplicative, and an (F, E, ε)-orbit approximation of α.

Definition 2.1(3), verbatim:

> For finite subsets F ⊆ G, E ⊆ X, and ε > 0, φ is called an (F, E, ε)-*orbit
> approximation of* α if there exists a finite set B and a subset S ⊆ A s.t.
> |S| > (1 − ε)|A| and for each s ∈ S there is an injective map π_s: E ↪ B
> s.t. π_{φ(g)s}(x) = π_s(α(g⁻¹)x) for all s ∈ S, g ∈ F, x ∈ E, whenever
> φ(g)s ∈ S and α(g⁻¹)x ∈ E.

**Hayes–Sale**, *Metric approximations of wreath products*, arXiv:**1608.02610**
(the id 1601.xxxxx used elsewhere is wrong), *Ann. Inst. Fourier* 68 (2018)
423–455. Theorem 1.3, verbatim:

> Let G, H be countable, discrete groups and assume that H is sofic. Then:
> (i) If G is sofic, then so is G ≀ H,
> (ii) If G is hyperlinear, then so is G ≀ H,
> (iii) If G is linear sofic, then so is G ≀ H,
> (iv) If G is weakly sofic, then so is G ≀ H.

**Scope, verified:** this covers only the **standard/restricted** wreath
product. The paper fixes `G ≀ H = ⊕_H G ⋊ H` immediately before Theorem 1.1.
Permutational wreath products appear only as an internal approximation
device (their Definition 2.7, prefaced verbatim by *"We will use permutational
wreath products in our approximations"*), and there is no theorem with a
hypothesis on a general action `H ↷ X`. Hayes–Sale therefore says nothing
about the Kun–Thom candidate.

**Alekseev–Bradford**, *Sofic actions, halo products, and metric
approximations of groups*, arXiv:2601.18742 (27 Jan 2026; unrefereed).
Corollary 5.2, verbatim:

> Let 𝒞 be one of the following: (a) The class of sofic groups; (b) The class
> of 𝕂-linear sofic groups, for 𝕂 a field; (c) The class of hyperlinear
> groups; (d) The class of weakly sofic groups. Let Γ, Δ ∈ 𝒞, and let
> β : Γ ↷ Δ be a sofic 𝒞-action by automorphisms. Then Δ ⋊_β Γ ∈ 𝒞.

Their Theorem 4.18, attributed in their own text to Theorem 1.7 of the
companion Gao–Kunnawalkam Elayavalli–Patchell graph paper, verbatim:

> If X = (V,E) is a graph; Γ is a sofic group, and Γ ↷_α X is a
> vertex-transitive action by graph automorphisms such that the stabiliser of
> a vertex is amenable, then α is a sofic action. In particular ..., any
> action of a sofic group on a set, with all point-stabilisers being amenable
> subgroups, is a sofic action.

**Brown–Dykema–Jung**, *Free entropy dimension in amalgamated free products*,
arXiv:math/0609080, *Proc. LMS* (3) 97 (2008) 339–367. Corollary 4.5,
verbatim:

> Let ℳ₁*_Bℳ₂ be the amalgamated free product of tracial von Neumann algebras
> ℳ₁ and ℳ₂ over a hyperfinite von Neumann algebra B, and assume each ℳᵢ has
> separable predual and is embeddable in R^ω. Then ℳ₁*_Bℳ₂ is embeddable in
> R^ω.

**Gao–Junge**, *Relative embeddability of von Neumann algebras and amalgamated
free products*, arXiv:2012.07940, introduction, verbatim — this is the record
that the non-hyperfinite case is **open**:

> However, the problem of given M and N embeddable, whether ∗_N M is
> embeddable as well remains open, and we, in this paper, investigate some new
> conditions under which this would hold.

## Corrections to earlier repo beliefs, established by this verification pass

Three statements used elsewhere in the corpus do not survive source contact.
They are recorded here so they are not re-imported.

- **Elek–Lippner**, *Sofic equivalence relations*, arXiv:0906.3619, contains
  **no** theorem that the orbit equivalence relation of an arbitrary p.m.p.
  action of a sofic group is sofic. Its four theorems are the
  orbit-equivalence invariance of soficity, `𝒩(ℛ) ↪ R^ω` for sofic `ℛ`, the
  measurable determinant conjecture, and one treeable example. The only
  positive existence statement is Proposition 7.1, verbatim: *"The Bernoulli
  shift of a sofic group is sofic."* — Bernoulli shifts only.
- **Elek–Szabó**, arXiv:math/0408400 (*Math. Ann.* 332 (2005)), contains **no**
  crossed product at all; the strings `crossed`, `rtimes`, `L^\infty` do not
  occur in its source. Its R^ω result is Theorem 2, verbatim: *"All countable
  sofic groups are hyperlinear."* Its "essentially free" is a Tarski-type
  condition on a finitely additive measure on a **set**, not a condition on a
  p.m.p. action. Any citation of Elek–Szabó for `L^∞(X)⋊G ↪ R^ω` is wrong;
  the correct pin is Păunescu.
- **Becker–Lubotzky**, *Group stability and property (T)*, arXiv:1809.00632,
  proves **non**-stability, not a characterization of flexible HS-stability.
  Theorem 1.3, verbatim: *"(i) If Γ is sofic and has Property (T), then it is
  not 𝒫-stable, unless it is finite. (ii) If Γ is hyperlinear and has Property
  (T), then it is not HS-stable, unless it is finite."* Flexible stability
  appears there only as a proposed definition in a "further research"
  subsection, in the permutation setting, with no HS analogue and no theorem.
  The flexible-HS-versus-hyperlinearity result is **Dogon**, arXiv:2211.10492
  (*Math. Z.* 2023) — abstract read, theorem statements **not** read, so any
  use of Dogon still needs its own verification pass.

## Source pass 2026-08-15 (late): the previously untranscribed definitions

Fetched the arXiv v1 PDF again and read pages 3–6 and 9–11 directly.  This
closes the hole flagged by `normal-closure-fixes-gamma-fixed-algebra`: the
definition of "sofic representation" and of the ambient objects is now
transcribed.

**Definition 2.1, verbatim.**  *"A homomorphism σ : G → 𝒮_𝒰 is a sofic
representation if tr(σ(g)) = 0 for every g ≠ 1.  For H ≤ G, let D_𝒰^{σ(H)}
be the algebra of all f ∈ D_𝒰 satisfying σ(h)fσ(h)^{-1} = f for every
h ∈ H."*  Here (§2 opening) 𝒮_𝒰 = Π_{n→𝒰} Sym(Y_n) for a sequence of
finite sets, permutations identified with permutation matrices, tr the
normalized trace, and D_𝒰 = Π_{n→𝒰}(D_{Y_n}, tr) the diagonal tracial
ultraproduct.  So "sofic representation" = homomorphism with vanishing
fixed-point fraction for every nontrivial element — exactly normalized
Hamming distance 1 to the identity — and D_𝒰^{σ(H)} is the fixed algebra
as used downstream.

**Definition 2.2, verbatim.**  *"A p.m.p. action G ↷ (X,μ) is sofic if
there are finite sets Y_n and an embedding
Θ : L^∞(X) ⋊ G → Π_{n→𝒰} M_{|Y_n|}(ℂ) such that Θ(L^∞(X)) ⊂ D_𝒰 and
Θ(u_g) ∈ 𝒮_𝒰 for every g ∈ G."*  (Embedding = unital trace-preserving
*-embedding; the crossed product is the von Neumann crossed product.)

**Lemma 2.3, verbatim.**  *"With the preceding notation,
D_𝒰^{σ(H)} = Π_{n→𝒰} D(𝒬_n)."*  — for H with property (T), after the
o_𝒰(|Y_n|) edge edit of the ultrafilter form of Kun's expander
decomposition ([13, Theorem 1], quoted on p. 4: "if H has property (T),
then one can change o_𝒰(|Y_n|) edges so that the graphs become disjoint
unions of graphs with a uniform positive Cheeger constant"), where 𝒬_n is
the resulting component partition.  The fixed algebra IS the block
algebra.

**Proposition 3.1, verbatim.**  *"Let Γ be an infranormal subgroup of G,
and assume that both Γ and G are finitely generated.  Let σ : G → 𝒮_𝒰 be
a sofic representation.  Assume that the generator graphs of both σ|_Γ
and σ admit, after o_𝒰(|Y_n|) edge changes, decompositions into
components with uniform positive Cheeger constants.  Then
σ(g)D_𝒰^{σ(Γ)}σ(g)^{-1} = D_𝒰^{σ(Γ)} for every g ∈ G."*  For Γ and G
both Kazhdan the decomposition hypothesis is automatic by the quoted
ultrafilter form of Kun's theorem, and finite generation follows from
(T).  Note this gives the **fixed-algebra invariance directly**, one
level below Theorem 4.1's centralizer normalization: consumers needing
only invariance of D_𝒰^{σ(Γ)} (e.g. the two-point refutation) may cite
Proposition 3.1 + [13, Theorem 1] and avoid the doubling bridge entirely.

Consequence for `two-point-data-yields-invariant-projection`: its tensor
construction produces σ with **zero** fixed points for every g ≠ 1 at
every ultrafilter-large n, so tr(σ(g)) = 0 holds on the nose and σ is a
sofic representation verbatim under Definition 2.1.  The "strongest
standard reading" caveat recorded earlier is now unnecessary — the
definitional ambiguity is resolved and the construction satisfies the
paper's actual definition exactly.

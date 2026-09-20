# Cairn, nonhyperlinearity, and the ordinary Baum–Connes problem

Research/integration date: 20 September 2026.
Target: reduced assembly with trivial coefficients for countable discrete
groups. **The ordinary counterexample root remains OPEN.** No ordinary
assembly kernel or cokernel class is constructed by this integration.

## Provenance and trust boundary

This integrates the user-supplied report *Cairn, nonhyperlinearity, and
the Baum–Connes problem: Proofs, additional deductions, and the exact
remaining obstruction*. Its stated source snapshot is
`group-approximation-main (1).zip`, SHA-256
`ea0fa7cbdcdf97212971b1f3c547e304e4eb147d1ccf532fd6528cd077192b40`.
That hash and the report's 156-path archive audit are supplied provenance,
not a claim that this integration reran the archive extraction or read
40,000 Markdown files. Work here used the current checkout, its canonical
nodes and artifacts, and bounded primary-source checks described below.
The report's original statement that its archive was not modified refers
to that earlier audit; this integration deliberately modifies Cairn.

“Written proof” below means a deduction justified in the linked text.
“Imported” means a named literature input. “Cairn-established” is a
derived repository status, not a Lean certificate or independent referee
verification. Jihao Liu's fresh September 20 internality manuscript,
Andreas Thom's conditional normalization, the universal-lattice
property-(T) theorem and Khanh's finite-presentation theorem retain their
separate attribution and mathematical review boundaries. No new
independent verification of their full analytic proofs is claimed.

## New deductions and canonical consumers

| Supplied report | Integrated claim or correction | Proof / consumer |
|---|---|---|
| 3.2–3.3 | [Native strict Kazhdan compression pair](../leavitt-native-strict-kazhdan-compression-pair.md) | [Native matrix artifact](leavitt-direct-normalization-obstruction-2026-09-20.md), now with x_12(e) outside uLu⁻¹ |
| 3.4 | Existing [triviality of all binary Leavitt tracial images](../binary-leavitt-tracial-ultraproduct-images-are-trivial.md) gets a native proof route | [Explicit normal-generation route](../leavitt-trivial-images-via-native-commutators.md); no simplicity input |
| 4.1–4.3 | Existing [torsion-free nonhyperlinear cd≤3 construction](../fp-torsion-free-nonhyperlinear-group-of-cd-at-most-three.md) now uses the rank-four pair | [Rips-double artifact](torsion-free-nonhyperlinear-rips-double-2026-09-20.md); no nine-leaf prerequisite |
| 4.4 | [All finite Ollivier–Wise Rips doubles satisfy coefficient BC](../rips-doubles-satisfy-bc-with-coefficients.md) | Hyperbolic vertex groups and [tree permanence](../bcc-passes-from-tree-vertex-stabilizers.md), independently of normalization |
| 4.4–5.1 | [The same fp torsion-free nonhyperlinear witness satisfies coefficient BC](../fp-torsion-free-nonhyperlinear-bcc-group-exists.md) | Explicit killed word, cd≤3, positive assembly; trace range ℤ and no nontrivial scalar projections |
| 6.4 | Congruence spectral trace divides by quotient order alone | [Kun–Thom artifact](bc-kun-thom-trace-test-2026-09-12.md), canonical formula and ordinary root corrected together |
| 8–10 | [Product traces kill rank-invisible K₀](../bernoulli-product-traces-kill-rank-invisible-k0.md) | [Complete product-trace proof](bc-bernoulli-product-traces-2026-09-20.md), including complex-contour approximation |
| 10.1–10.5 | [Finite cylinder formula](../bernoulli-product-traces-have-finite-cylinder-form.md) and [wreath trace range](../prime-lamp-wreath-trace-range-is-host-plus-z-inverted-p.md) | Locality, relative traces and the host splitting; no assembly assumption |
| 12.2 | Exact-completion agreement does not establish ordinary assembly | [BGW scope correction](../bgw-trivial-coefficient-agreement-is-open.md) |
| 12.4 | [Exact host-and-tail assembly defects](../bernoulli-assembly-defects-split-into-host-and-tail.md) | Partial assembly, injectivity and the finite-pattern retraction |

The [ordinary BC root](../baum-connes-counterexample-group-exists.md),
[nonhyperlinear root](../non-hyperlinear-group.md),
[Liu integration guide](liu-cairn-integration-2026-09-20.md), and Bernoulli
comparison/frontier nodes link these results. Existing propositions are
reused rather than cloned under new names.

## The report's existing deductions and exact surviving obligations

1. **Problem and trace conventions (Sections 1–2).** Ordinary assembly is
   μ_G:K_*^G(Ebar G)→K_*(C*ᵣG), not maximal assembly or assembly with an
   arbitrary coefficient. K-theory pairs with τ_G⊗Tr_n; hyperlinear models
   use Tr_d/d. Universal internality preserves the specified matrix sizes
   and does not turn coordinate lifts into exact representations. The
   [current analytic acceptance and Thom bypass](liu-section-six-acceptance-and-thom-bypass-2026-09-20.md)
   is retained, separately from Liu's stronger single-model Section 7.
   The [Kun–Thom lamp obstruction](../kun-thom-lamp-wreath-is-not-hyperlinear.md)
   uses the two distinct cosets γ₀tΓ and tΓ: their product lamp is killed
   by normalization, while the x₁⁻¹x₂ coefficient proves coset distinction.
   Compactness gives a finite obstruction but no numerical tolerance.

2. **Leavitt and Rips (Sections 3–4).** The native compressor has upper-left
   conjugation block sAt+eI, so strictness never uses an inverse for s.
   The elementary normal-generation chain kills the entire tracial image.
   The Rips preimage pair is Kazhdan by extension, its edge group is finitely
   generated, and the word (ht)₂(t⁻¹h⁻¹t)₁(t⁻¹)₂ is reduced and nontrivial.
   Finite presentation of the edge group is not required. Its Bass–Serre
   resolution gives only cd≤3. The positive assembly result excludes this
   double as a counterexample even if a fresh analytic input is revised.

3. **Trace and completion obstructions (Sections 5–6).**
   [Assembly image traces](../lueck-surjective-assembly-traces-lie-in-lambda-g.md)
   belong to Λ_G=ℤ[|F|⁻¹:F finite]. Every finite group embeds in the
   Leavitt unit group, so its ring is ℚ and rational traces cannot refute
   assembly. Characteristic-two ring idempotents do not become complex
   group-algebra idempotents; a finite faithful trace forbids proper
   isometries. Infinite-subgroup Kazhdan projections vanish in the reduced
   algebra, finite averages are assembly classes, and translation-invariant
   ghosts or compact operators in an infinite reduced group algebra are
   zero. Quasi-regular representations of nonamenable subgroups are not
   reduced representations. Acyclicity neither handles torsion centralizers
   in proper equivariant homology nor computes analytic K-theory.

   The [Kun–Thom exact denominator ring](../kun-thom-actor-finite-subgroup-ring-equals-z-inverted-p.md)
   is ℤ[1/𝒫] with 𝒫={p}∪{prime divisors of q^k−1, k≤r}∪{ℓ≤d+1}.
   For q=2,r=d=3 it is ℤ[1/42]. The [algebraic-idempotent proof](../kun-thom-actor-algebraic-idempotents-pass-trace-test.md)
   uses support-separating finite quotients and Dirichlet prime avoidance;
   finite-spectrum projections are therefore excluded. Supports in
   [assembly-positive subgroups](../bc-kun-thom-gap-labels-on-bc-subgroups-pass-trace-test.md)
   are excluded as well. A surviving spectral candidate needs a genuine
   reduced spectral gap and a nonalgebraic projection whose unnormalized
   trace leaves the ring. Finite models need not share the regular gap,
   and the localization ring is not closed under real limits.

4. **Module route (Section 7).** The existing
   [K-inexactness criterion](../k-inexact-module-triple-refutes-trivial-coefficient-bc.md)
   is a complete implication. For X=V̂, Z=V₀^⊥, I=C₀(X\Z), choose
   y∈ker(K_j(C(X)⋊ᵣG)→K_j(C(Z)⋊ᵣG)) outside the image of K_j(I⋊ᵣG).
   If μ_A is surjective, lift y to x. If μ_B is injective, naturality
   kills the image of x, topological half-exactness lifts x from I, and
   naturality puts y in the forbidden image. Amenable-kernel partial
   assembly transfers this alternative to V⋊G and (V/V₀)⋊G.
   The [missing module triple](../some-nonexact-group-has-a-k-inexact-module-triple.md)
   remains open. Nonexactness at the algebra level is insufficient;
   arbitrary compact coefficient spaces are not automatically abelian
   dual actions. Equivariantly split quotients give no defect. Invariant
   full-support Haar measure excludes a wandering nonempty open set.

5. **Bernoulli ranks and tails (Sections 8–10).** The cylinder map must be
   stabilized because cylinders overlap. Pattern stabilizers are trivial
   for torsion-free hosts. Finite-configuration ranks prove injectivity;
   finite-block Combes–Thomas decay and integer mixed differences give
   finite pattern expansions without a growth assumption. Every K₀ class
   splits into its finite cylinder component and a virtual rank-invisible
   part. The decreasing-tail intersection does not vanish by increasing
   inductive-limit continuity. Product traces now kill that remainder.
   For infinite torsion-free G, τ_(C_p wr G)(K₀)=τ_G(K₀)+ℤ[1/p].
   This excludes the proposed new Haar detector, not the extra K-classes.

6. **CND support and HLS (Section 11).** The existing
   [no-lift theorem](../hls-ghost-class-never-lifts-to-the-bernoulli-full-shift.md)
   is retained with its Tu/going-down imports and hypothesis (M): a
   finitely generated torsion-free word-metric host, isometrically embedded
   fixed-degree uniform expanders of increasing sizes and unbounded girth
   (and the separation convention in the canonical statement). The
   first-support-point function gives a proper CND action on the hereditary
   CND-support shift. Its coefficient assembly and cylinder comparison are
   isomorphisms. Boundary supports are CND by the large-girth tree argument.
   Boundary injectivity and topological half-exactness make a boundary-zero
   cylinder class lift from a direct sum of compact-algebra K₀ groups;
   its marked ranks are eventually zero. Locality transfers this to every
   full-shift class. The HLS rank-one class therefore cannot lift.
   Rank-invisible virtual classes and odd classes restrict to zero on CND
   support. This does not prove they come from the complementary open
   crossed product without a reduced-exactness theorem.

7. **Other routes (Section 12).** The [higher-Kazhdan criterion](../reduced-higher-kazhdan-projection-kk-witness-proof.md)
   needs a finite (n+1)-skeleton, an isolated zero in the reduced C*-spectrum
   of Δ_n, and β_n^(2) outside Λ_G for the **same group**. A von Neumann
   kernel dimension alone does not give that C*-projection. The
   exact-completion factorization μ_r=q_*μ_E only yields a disjunction
   when q_* fails; positivity of μ_E is additional data needed to select
   ordinary failure. The BEW erratum's surviving scalar-quotient lemma
   uses literal ℂ, not an arbitrary algebra denoted C.

Thus the three concrete missing objects remain a K-inexact module triple,
a nonzero Bernoulli virtual/odd remainder, or a reduced projection with a
forbidden trace and justified algebra membership. These are sufficient
routes, not an exhaustive classification of all possible counterexamples.

## Source ledger and bounded external checks

The source labels here match the supplied report. Rechecking a theorem's
statement does not mean re-proving it or checking an entire paper.

| Report references | Source and role | Integration check |
|---|---|---|
| R1 / C1 | [Higson–Lafforgue–Skandalis](https://vlafforg.perso.math.cnrs.fr/files/counterex.pdf), coefficient/coarse counterexamples | Existing repository boundary retained; no ordinary counterexample imported |
| R2 | [Lafforgue, arXiv:1201.4653](https://arxiv.org/abs/1201.4653), hyperbolic coefficient assembly | Abstract/theorem scope rechecked 2026-09-20 |
| R3 | [Oyono-Oyono, DOI](https://doi.org/10.1023/A:1012786413219), tree permanence | Statement cross-checked in [Lück–Reich](https://him-lueck.uni-bonn.de/data/bcsfinal.pdf) and [Flores–Pooya–Valette](https://arxiv.org/html/2212.09557v2); original full proof not independently re-read |
| R4–R5 / C2 | [Liu manuscript](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf) and [Thom](https://andreasthom.github.io/pdf/nonhyperlinear.pdf) | Existing internality acceptance and Thom-bypass chain retained; stronger single-model interface remains separate |
| R6 / C5 | [Khanh, arXiv:2609.08428v1](https://arxiv.org/html/2609.08428v1), Theorem 6.1 | Primary source accessed; finite presentation remains a separate import |
| R7 / C20 | [Ollivier–Wise, math/0409203](https://arxiv.org/pdf/math/0409203), Theorem 1.1 and Section 2.1 | Primary PDF accessed; finite graphical construction and existing dimension audit retained |
| R8 / C6–C11 | [Lück–Reich, math/0402405](https://arxiv.org/abs/math/0402405) and the repository trace citation routes | Existing finite-subgroup ring and torsion-free integrality inputs retained |
| R9 / C12–C13 | [Chabert–Echterhoff](https://ems.press/content/serial-article-files/25880), partial assembly and topological half-exactness | Existing named import used with amenable-kernel hypotheses |
| R10 | [Meyer, arXiv:2508.05726v2](https://arxiv.org/html/2508.05726v2) | Rechecked the counterexample to the stronger normal-subgroup-only extension claim |
| R11 / C14–C16 | [Chakraborty–Echterhoff–Kranz–Nishikawa, arXiv:2210.09209](https://arxiv.org/abs/2210.09209) | Abstract checked; existing weak-K-equivalence and going-down inputs retained with their hypotheses |
| R12 / C17 | [Baum–Guentner–Willett, Section 6](https://arxiv.org/html/1311.2343v3), Tu's action theorem | Existing CND-support artifact is the explicit import boundary |
| R13 / C19 | [Buss–Echterhoff–Willett, Appendix A](https://arxiv.org/pdf/1804.02725v3) | Rechecked the withdrawal of Proposition 4.4 and Corollaries 4.5–4.8 and the open comparison |
| R14 / C18 | [Li–Nowak–Pooya, arXiv:2006.09317](https://arxiv.org/abs/2006.09317) | Primary source entry checked; existing conditional gap/trace criterion retained |
| R15 | [Nishikawa–Petrosyan, arXiv:2509.15070v2](https://arxiv.org/html/2509.15070v2) | Existing hyperbolic finite-outer-wreath theorem used with outside group trivial; not confused with C_p wr G |

A bounded freshness check also accessed the Fields Institute's
[July 30, 2026 talk page](https://www.fields.utoronto.ca/talks/There-are-no-known-counter-examples-to-Baum-Connes-conjecture).
No checked source supplies an ordinary counterexample. This is not a
claim that a finite search proves the absence of every possible new paper.
The product-trace proof is supplied as a deduction, without a claim of
historical novelty. The separately supplied Library comparison is not
treated as independently fetched during this integration.

## Validation

Graph checks validate source schema, references and derived statuses;
they are not mathematical proof certificates. The integration validation
receipt records the actual commands, scoped dependency status and any
repository-wide failures. No Lean build is claimed for these written
research changes. The ordinary root and the missing module/Bernoulli
existence inputs must remain OPEN after integration.

[Validation receipt](bc-nonhyperlinearity-validation-2026-09-20.json): the
exact tracked-main graph plus this integration passed schema, reference,
duplicate, link and status checks (8 new claims, 10 new routes). The
positive Rips assembly dependency cone excludes internality/normalization.
Standard working-tree `check --changed` encountered unrelated concurrent
source errors; `preview` hit the existing incomplete-baseline reader error.
The receipt distinguishes those failures from the passing candidate check.
The frontier was generated from the validated candidate graph.

## Further attempt integrated

The subsequent [general-closure attempt](Cairn_Baum_Connes_General_Attempt.md)
adds amenable-kernel trace factorization, the tracial GNS radical, exact
localization of a module defect in the liftable quotient kernel, the
all-bounded-positive-trace obstruction, a torus counterexample to
trace-to-K-theory vanishing, and the faithful-trace embedding restriction.
Its proof nodes and equivalent open input are connected to the module
route; its [separate receipt](bc-general-closure-validation-2026-09-20.json)
records their checks. The original ordinary root stays OPEN.

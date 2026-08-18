# Literature verification record — eight 2026 preprints not previously in the corpus

Compiled 2026-08-18 while wiring the private-neighbour result
(`research/artifacts/kun-thom-private-neighbour-2026-08-18.md`).  Every entry
below was checked against `arxiv.org/abs/<id>` on 2026-08-18: the identifier
resolves, and the title, authors and dates recorded here are the ones the
abstract page shows.  Abstracts are quoted from that page.  No entry here was
read in full; where a *body* statement is used downstream it is marked
**BODY-READ** with the source of the transcription, and where only the
abstract was read the downstream use is confined to what the abstract states.
Nothing in this file is a proof; routes cite it as a citation import, in the
sense of `kun-thom-nonsofic-wreath-citation`.

None of these identifiers appeared anywhere in `research/`, `docs/` or
`notes/` before this file.

---

## [GKM26] arXiv:2607.29571 — Gao, Kunnawalkam Elayavalli, Mj

*Strongly converging unitary representations for extensions by exact groups.*
David Gao, Srivatsav Kunnawalkam Elayavalli, Mahan Mj.  Submitted 31 July
2026.

> We prove the existence of strongly converging unitary representations in
> various new settings of countable groups, in particular, arising as
> extensions by exact groups: semidirect products with amenable groups;
> generalized wreath products with abelian base; graph wreath products;
> various free-by-cyclic groups including Gersten's group; and general
> Bernoulli shift crossed products on C*-algebras.

**BODY-READ** (HTML render of v1, 2026-08-18), the three statements used
downstream:

* *Definition 2.6.*  "An action of a countable group `G` on a simplicial
  graph `Γ` is said to be **residually finite** if, for each finite subset
  `F ⊂ G` and `W ⊂ V`, there exists a finite graph `Θ`, a finite set `A`, a
  group homomorphism `φ : G → Sym(A)`, and, for each `a ∈ A`, a graph
  embedding `π_a : (W, E|_{W×W}) ↪ Θ` s.t.
  `π_{φ(g)a}(v) = π_a(α(g^{-1})v)`" for the specified conditions.
* *Theorem 1.2.*  Generalized wreath products `G ≀_I L` with `G` residually
  finite abelian and `L` exact PMF/PFF are PMF/PFF, for any transitive
  `L ↷ I` **with separable stabilizers**.
* *Theorem 1.5.*  For `(A,φ)` an MF unital exact C*-probability space, `L` an
  exact MF group and `L ↷ I` transitive **with separable stabilizers**, the
  generalized Bernoulli shift crossed product `(⊗_I A) ⋊ L` is MF.

**Used downstream by** `marked-graph-action-not-residually-finite` (the
Definition 2.6 hypothesis is refuted for every marked Kun--Thom invariant
graph) and by `lamp-coordinate-collision-obstruction` (their finite-quotient
mechanism identifies coordinates; the two-moment computation shows that is
fatal even in `2`-norm).  What is **not** claimed anywhere: that their
theorems are wrong, or that they were ever asserted to cover the Kun--Thom
pair.  The pair fails their hypotheses; the theorems stand.

**Positive lesson.**  Their extension/crossed-product upgrade separates two
tasks cleanly — ambient equivariant finite-dimensional approximation of the
base action, then assembly into the crossed product — and it is the *first*
that is missing here.  Effort spent on crossed-product assembly for the
minimal graph is therefore misplaced; the missing object is a genuinely
quantum, non-coordinate equivariant model of the base action, after which
machinery of this kind would do the assembly.

---

## [Gal26a] arXiv:2603.24743 — Galindo

*Splitting of Clifford groups associated to finite abelian groups.*  César
Galindo.  v1 25 Mar 2026, v2 11 Aug 2026.

> The Clifford group associated with a finite abelian group fits into an
> extension of the symplectic group by the underlying phase space.  We prove
> that this extension splits as a semidirect product if and only if the order
> of the underlying abelian group is not divisible by four.  The obstruction
> to splitting is controlled entirely by the 2-primary component and vanishes
> precisely when this component is trivial or cyclic of order two.  This
> confirms a conjecture of Korbelář and Tolar, extending their cyclic result
> to arbitrary finite abelian groups.

**Used downstream by** `finite-clifford-symplectic-section-obstruction`,
with `A = (ℤ/2)^n`: `|A| = 2^n` is divisible by four exactly when `n ≥ 2`, so
the qubit Clifford extension is nonsplit for every `n ≥ 2`.  Only the
abstract's iff-criterion is used.

---

## [KT26] arXiv:2606.08215 — Korbelář, Tolar

*Structure of Clifford groups of composite finite quantum systems.*  Miroslav
Korbelář, Jiří Tolar.  Submitted 6 June 2026.  Abstract: for configuration
space `ℤ_{n_1} ⊕ ⋯ ⊕ ℤ_{n_k}` with `N = n_1⋯n_k`, the Clifford group and the
projective Clifford group are natural semidirect products exactly when `N` is
not divisible by four.  Recorded as the independent multipartite confirmation
of the same divisibility threshold; [Gal26a] is the general statement and the
one cited.

---

## [Gal26b] arXiv:2606.21751 — Galindo

*Representation theory of projective Clifford groups via isocategoricality.*
César Galindo.  v1 19 June 2026, v2 10 Aug 2026.  The projective Clifford
group `C(A)` of a finite abelian `A` is isocategorical to the affine
symplectic group `ASp(A)`; matching parametrisations of irreducible
characters and conjugacy classes with coinciding character tables; explicit
bases for tensor-power commutants of the projective Weil representation,
indexed by symplectic orbits.

**Used downstream** only as the source of a *diagnostic distinction*, not of
a theorem: a finite Clifford microstate carries two separate defects — the
phase-space-valued factor set of the extension `1 → V_A → C(A) → Sp(V_A) → 1`
and, after choosing projective Clifford elements, the scalar Weil multiplier
of the unitaries representing them.  Isocategoricality does **not** split the
extension (a tensor equivalence of representation categories does not
preserve a chosen multiplication of lifts), and nothing downstream assumes it
does; it supplies a split comparison object for character/trace statistics of
the defect.

---

## [Jeo26] arXiv:2608.14487 — Jeong

*Flattening and asymptotic orthogonalization of completely positive maps.*
Yoonje Jeong.  Submitted 14 Aug 2026.

> Let `M` be a II₁ factor, `N` a tracial von Neumann algebra, and
> `Φ : M → N` a subtracial completely positive map.  For an irreducible II₁
> subfactor `P ⊆ M`, we characterize when `Φ` exhibits a flattening property
> under conjugation by unitaries in `P`.  To be specific, we show that the
> failure of a Pimsner-Popa type inequality for `E_P ∘ Φ* ∘ Φ` is the precise
> obstruction, equivalently characterized by left weak mixing of a naturally
> associated `P`-`N` bimodule.  As an application, we obtain an asymptotic
> orthogonalization result generalizing a result of Popa.

**Used downstream by** `ccr-hard-instance-subfactor-reducible` as the reason
that claim is worth recording: the irreducibility hypothesis is exactly what
the hard (CCR) instance fails.  No statement of the paper is disputed.

---

## [GKE26] arXiv:2604.14106 — Gao, Kunnawalkam Elayavalli

*Toeplitz exactness for strong convergence.*  David Gao, Srivatsav
Kunnawalkam Elayavalli.  v1 15 Apr 2026, v3 22 Apr 2026.

> We prove a new "Toeplitz exactness" theorem for strong convergence.  This
> is a machine to upgrade strong convergence in the general setting of
> C*-correspondences, and has several applications.

Assembly/upgrading machinery, not a source of initial finite-dimensional
models.  Recorded as context: it would shorten the passage from base models
to HNN/amalgam/crossed-product strong models *if* such base models existed,
which is precisely the missing object.  Strong convergence is in any case
above what Q3.4 needs.  No downstream claim depends on it.

---

## [CC26] arXiv:2607.15100 — Caspers, Chen

*Strongly convergent matrix models for q-Gaussian algebras.*  Martijn
Caspers, Enli Chen.  Submitted 16 July 2026.  Finite-dimensional random
matrix models for finite q-Gaussian families for `|q| < √2 − 1`: normalized
sums of graph-product semicirculars over an Erdős--Rényi graph satisfy the
q-Toeplitz relations with vanishing operator-norm error, uniform strong
convergence via ultraproducts, then quantitative tensor-GUE replacement by
finite matrices.  Applications: the C*-algebra of a finite q-Gaussian family
is MF, and the BDF extension semigroup is not a group in that range.

Recorded as **methodological** evidence only: a randomized graph +
Clifford-twist + ultraproduct + finite-matrix-replacement architecture can
achieve strong finite-dimensional approximation.  No estimate of theirs is
imported; their interaction model is random and unconstrained, whereas
`S_min` is deterministic, of infinite degree, and must carry a group action.
No downstream claim depends on it.

---

## [Shl26] arXiv:2606.28648 — Shlyakhtenko

*Failure of Strong Convergence of Matrices with Fermionic Entries.*  Dimitri
Shlyakhtenko.  Submitted 26 June 2026.

> Let `Q^{(k)}_N` be an `N×N` matrices with entries satisfying CAR,
> normalized to have variance `1/√N` with respect to the trace of the CAR
> algebra.  We show that, although the operator norm of the real part of an
> individual matrix `Q^{(k)}_N` converges as `N → ∞` to the semicircular
> limit, the family of matrices does not converge to the free probability
> limit strongly.  In fact, even the operator space structure of the linear
> spans of the real and imaginary parts of `Q^{(k)}_N`'s, `k = 1,…,M`, does
> not converge to the semicircular limit.

Recorded as a warning against a naive "replace scalar entries by CAR
entries" strong-convergence route.  It is **not** an obstruction to Connes
embeddability, which needs only tracial/`2`-norm microstates; read together
with [CC26] the lesson is that engineered randomized Clifford models can work
strongly while naive fermionic substitution need not.  No downstream claim
depends on it.

---

## [Neu54] B. H. Neumann

*Groups covered by finitely many cosets.*  Publ. Math. Debrecen **3** (1954),
227--242, DOI `10.5486/PMD.1954.3.3-4.07`.  A group is not the union of
finitely many cosets of subgroups of infinite index.  Used for convenience in
Lemmas 6 and 7 of the private-neighbour artifact; Section 5 there replaces it
by an explicit finite-box count, so no downstream claim rests on it.

---

## Keep the targets apart

Several of these papers aim at MF or at strong convergence.  The separation
branch of `q3-4-resolved` needs only hyperlinearity, i.e. Connes
embeddability, i.e. normalized `2`-norm microstates.  The distinction decides
how each entry should be read:

* [Shl26] is a failure theorem for **strong** convergence and is not a CE
  obstruction;
* [GKM26]'s finite-quotient method is MF/strong, but its *coordinate*
  mechanism fails tracially too — that is
  `lamp-coordinate-collision-obstruction`, and it is a genuine CE-level
  obstruction to that architecture;
* [Gal26a] is an exact algebraic nonsplitting and says nothing about whether
  the cocycle is negligible after direct-sum `2`-norm averaging.

So the next attack should optimise for normalized `2`-norm and treat strong
convergence as a bonus, not a requirement.

## Search result, not a theorem

This sweep found no primary source through 2026-08-18 claiming a proof that
every hyperlinear group is sofic, nor exhibiting a proved hyperlinear
nonsofic group.  That is a statement about what this search returned; it is
consistent with `q3-4-resolved` being open, and it is not evidence about the
literature as a whole.

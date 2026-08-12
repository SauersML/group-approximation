# Provenance and claim boundary for the `(TT)/T` paper

This file is a publication gate.  It separates mathematical inputs, internal
reproofs, and candidate new results.  A manuscript claim may not be stronger
than the corresponding row below.  In particular, "proved in Lean" never
means "discovered here."

## Established work that receives no novelty claim

### Mimura: `(TT)/T`, relative rigidity, and globalization

Masato Mimura introduced property `(TT)/T` and proved the relevant rigidity
technology in:

* M. Mimura, *Property (TT) modulo T and homomorphism superrigidity into
  mapping class groups*, arXiv:1106.3769.
* M. Mimura, *Rigidity theorems for universal and symplectic universal
  lattices*, doctoral thesis.

The following are Mimura's results or proof architecture, not ours.

1. The definition of `(TT)/T` as boundedness of Hilbert-space
   quasi-cocycles after removing the invariant part.
2. The normalized-set/Kazhdan/bounded-generation globalization method.
3. `(TT)/T` for commutative universal lattices.
4. Most importantly for priority, thesis Proposition 9.2.8 states that, for
   the free associative ring
   `A = Z⟨x₁, ..., x_k⟩`, the pair
   `E_m(A) ≥ E_{m-1}(A)` has relative `(TT)/T` for `m ≥ 3`; it also states
   relative `(FF_{L_p})/T` for `m ≥ 4`.

Consequently the paper must **not** claim that relative quasi-cocycle rigidity
for noncommutative universal lattices was previously unknown.  The Lean
development reconstructs the Hilbert-space argument internally to eliminate
a literature premise; that is verification and proof independence, not
theorem novelty.

There are two evident typographical slips in the sources, neither affecting a
theorem:

* thesis Definition 8.3.4 says "cocycle" where the surrounding definitions,
  equivalence with `(FF_H)/T`, and the published paper all require
  "quasi-cocycle";
* paper Theorem 5.1 calls the generating subset `U` but condition (iii) once
  says `P`; its proof uses `U`.

These are editorial corrections, not mathematical counterexamples.

### Ershov--Jaikin-Zapirain: property `(T)`

M. Ershov and A. Jaikin-Zapirain, *Property (T) for noncommutative universal
lattices*, arXiv:0809.4095, prove property `(T)` for elementary groups over
finitely generated associative rings in the relevant ranks.  The present Lean
library internally reconstructs the characteristic-two rank-three estimate it
uses.  The paper must credit Ershov--Jaikin-Zapirain for the theorem and may
describe the internal proof only as an independent quantitative
formalization/reproof.

### Purely infinite rings and Leavitt algebras

The sandwich property

`a ≠ 0 -> ∃ x y, x * a * y = 1`

is not introduced here.  Ara--Goodearl--Pardo, *Purely infinite simple rings*,
arXiv:math/0111066, Theorem 1.6, characterize a simple purely infinite ring by
this property together with exclusion of division rings.  The converse must
not be quoted without its simplicity/non-division hypotheses.

Leavitt self-similarity and the relevant `K`-theory are established subjects.
In particular, neither matrix self-similarity nor `K_1(L_2)=0` is a novelty
claim of this paper.  The Lean proofs provide an explicit internal route to
the exact algebraic hypotheses.

### Nonsoficity

The nonsoficity of the binary Leavitt elementary groups belongs to the prior
nonsofic-group work reproduced and formalized elsewhere in this repository.
Any combined statement "nonsofic and `(TT)/T`" is explicitly labeled a
corollary combining that theorem with the new rigidity result.  It is never
presented as a new proof of nonsoficity.

## Candidate contributions of the paper

These are the only results currently eligible for an originality claim, and
even these claims remain provisional pending direct specialist confirmation.

1. **Strong root estimate.**  The rank-four Lean argument bounds a
   quasi-cocycle on the root subgroup `X₀₃` for every unitary
   representation, without assuming absence of invariant vectors.  This is
   stronger than relative `(TT)/T`.  Before submission it must be exposed as
   a theorem whose Lean type contains no no-invariant-vector premise.
2. **Strong-division coordinate-block factorization.**  If every nonzero
   `a` admits `xay = 1`, then `GL_n(R)` has width at most `2n + 6` with
   respect to elementary transvections together with one fixed coordinate
   copy of `GL_{n-1}(R)`.  This is not described as bounded elementary
   generation.
3. **Four-hypothesis synthesis theorem.**  For a nontrivial ring `R`, the
   current exact hypotheses are:
   * a finite free `F_2`-algebra surjects onto `R`;
   * `R` carries a binary Leavitt family;
   * `R` has single-sandwich division;
   * every `diag(u,1)` lies in `E_2(R)`.

   Under these assumptions, `E_n(R)` has `(TT)/T` for every `n ≥ 3`.
   The paper may not abbreviate these assumptions to "purely infinite
   simple" or "binary self-similar" alone.
4. **Binary Leavitt specialization.**  The unconditional theorem
   `E_n(L_{F_2}(1,2))` has `(TT)/T` for `n ≥ 3` is a candidate new theorem.

No sentence may use "first", "previously unknown", or "new" for items 1--4
without a documented final literature search and, preferably, a direct query
to specialists in noncommutative universal lattices and `(TT)/T`.

## Required one-to-one Lean surface

Before the manuscript is frozen, it must have one declaration per numbered
paper result:

1. the no-`/T` root theorem;
2. the `Fin n` coordinate-block factorization with the literal `2*n+6`
   width;
3. the explicit four-hypothesis ring-class theorem;
4. a finite-type-algebra wrapper, if the manuscript uses that formulation;
5. the binary Leavitt all-ranks theorem;
6. the separately imported nonsofic-plus-`(TT)/T` corollary.

The first five belong to a rigidity-only file.  The sixth belongs to a
separate corollary file so that nonsoficity does not enter the dependency
closure of the rigidity theorem.  Every declaration is included in the axiom
audit and its elaborated type is recorded for manuscript comparison.

## Submission wording

Safe abstract wording is:

> We prove an explicit coordinate-block factorization for general linear
> groups over rings with the single-sandwich property and combine it with a
> quantitative root-subgroup quasi-cocycle estimate.  This yields property
> `(TT)/T` for elementary groups over a class of finite-type
> characteristic-two self-similar rings, including the binary Leavitt
> algebra.  The quasi-cocycle framework and globalization method are due to
> Mimura, property `(T)` for noncommutative universal lattices is due to
> Ershov--Jaikin-Zapirain, and the ring-theoretic inputs come from the theory
> of purely infinite and Leavitt algebras.

This wording deliberately avoids a priority claim until the final specialist
audit is complete.

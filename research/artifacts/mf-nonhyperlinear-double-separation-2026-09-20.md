# MF does not imply hyperlinear: source audit and same-witness deduction

Date: 2026-09-20. This is a written mathematical audit, not a Lean proof
or a claim of external human refereeing. The analytic nonhyperlinearity
input is the named Cairn Liu-Thom chain; this note does not independently
reverify Liu's full analytic proof.

## 1. What was checked at the primary sources

Tatiana Shulman, [*The MF property for amalgamated free products*,
arXiv:2603.13564v3](https://arxiv.org/html/2603.13564v3), dated 31 August
2026, defines group MF in Definition 3 by a faithful unitary map into a
matrix **operator-norm** corona. Her Theorem 10 applies to a separable
MF C-star algebra A and any C-star subalgebra C, using the same inclusion
in both copies; the full symmetric amalgam is MF. Theorem 16 in the body
is the general compatible-corona-embedding criterion (the introduction's
"Th. 20" forward reference remains stale even in v3). These statements,
Definition 3, and the symmetric-inclusion convention were checked in v3.
Theorem 10 itself is an external mathematical import here, not reproved.
Neither it nor Definition 3 asserts that the canonical group trace is an
MF trace. In particular we do not read an arbitrary MF-group double
permanence assertion into the C-star theorem.

Gabor Kun and Andreas Thom, [*Nonsofic wreath products of residually
finite groups*, arXiv:2608.06222v3](https://arxiv.org/html/2608.06222v3),
Theorem E, supplies residual finiteness of the entire monomial actor
G=EL_r(R) rtimes SL_d(Z) and its polynomial subgroup, for every prime
power q and r,d>=3. The displayed statement was checked at the primary
source, with the semidirect-product actor included. It is not an appeal
to false general closure of residual finiteness under extensions.

For nonhyperlinearity we use the existing family claim
`kt-q2-double-is-not-hyperlinear`, which credits **Jihao Liu**,
[*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf),
Theorem 1.2 / 6.7, and **Andreas Thom**,
[*A conditional construction of a nonhyperlinear group and the centralizer
problem*](https://andreasthom.github.io/pdf/nonhyperlinear.pdf),
Theorems 1.2–1.3. Liu's internality supplies the missing analytic input;
Thom supplies the conditional normalization/double mechanism. The pairs
are Kun-Thom's. The earlier profinite-regular group-embedding proof is
recorded in `notes/WEAK_MF_NONSOFIC_DOUBLE.md`; it is not Liu's argument.
This note claims no literature priority for the combined separation.

## 2. The faithful group bridge, without a trace sleight of hand

Let G be any countable residually finite group and Gamma any subgroup.
Choose decreasing finite-index normal subgroups N_n with intersection 1.
The regular representations of G/N_n give an injective homomorphism rho
from G into the unitary group of a matrix norm corona. Indeed every
nonidentity g is eventually nontrivial in the quotient, where its regular
permutation unitary is uniformly separated from the identity in norm.
Let A=C*(rho(G)) and C=C*(rho(Gamma)). A is separable MF.

An ultralimit of the normalized finite regular traces gives a trace tau
on A with tau(rho(g))=0 for g!=1. Therefore its GNS representation sends
rho(g) to the left regular unitary lambda_G(g), and extends to a
surjective star homomorphism A -> C*_r(G). This does not assert that tau
is faithful on A.

Shulman makes B=A *_C A MF. The two group inclusions give a homomorphism
i:D=G *_Gamma G -> U(B). To check its injectivity, represent the two
copies of C*_r(G) on l2(D) by the two vertex inclusions. Each is faithful:
the restriction of the regular representation of D to either G is a
multiple of the regular representation of G, by coset decomposition.
The maps A -> C*_r(G) -> B(l2(D)) agree on C because they agree on every
rho(gamma). The universal property thus produces B -> B(l2(D)) whose
composition with i is exactly lambda_D. Since lambda_D is injective
on the abstract group, so is i. This also gives the normal-form argument
without requiring a finite-quotient separation of Gamma from g outside it.

We have proved that every countable RF symmetric group double is MF.
The crucial completion is B, not C*(D) or C*_r(D). A canonical trace
exists on B by pulling back the regular trace of D through this map, but
it need not be a trace obtainable from matrix models. Quotients of an MF
C-star algebra need not be MF. Neither invalid inference is used.

## 3. Same witness, then finite presentation and surjunctivity

Set q=2 and let r,d>=3. Take the polynomial subgroup and Laurent actor
from Kun-Thom Theorem E, with the standard monomial action and the same
polynomial inclusion into both vertex copies. Section 2 makes its double
D MF; the existing Liu-Thom family premise makes this very D
nonhyperlinear. This proves `kt-doubles-are-mf-but-not-hyperlinear`.

At r=6,d=3 the group is exactly the D_6 already identified by
`fp-surjunctive-nonhyperlinear-group-exists`. The independent artifact
`fp-surjunctive-nonhyperlinear-double-audit-2026-09-20.md` proves its
finite presentation using the entire rank-six Steinberg kernel over the
three-variable Laurent ring, not just a stable image. Its surjunctivity
uses the exact fold, injective on each vertex group. Those are separate
existing premises; this audit checks equality of all parameters, actor
action and edge maps rather than redoing their structural proofs.
Thus one specified group has all four properties: finitely presented,
surjunctive, MF, nonhyperlinear.

This is stronger than mere existential nonhyperlinearity but is not a
new proof of Liu's internality. The comparison with Shulman's theorem
shows why the stronger operator error norm does not contradict the
negative averaged-norm result: separation may live in negligible rank.

## 4. An actual new conclusion for the model-selection problem

For any countable nonhyperlinear group D, there is a nonidentity word w
that every homomorphism into a tracial matrix ultraproduct kills. To
see this, suppose instead that each w survives somewhere. Lift that
homomorphism on successively larger finite windows. The nonzero
2-norm of its image of w supplies a fixed positive trace gap, so w is
elementwise tracially visible. The accepted
`hyperlinear-elementwise-visibility` criterion would make D hyperlinear.

For the doubles here, D nevertheless admits faithful norm-corona
models. In *every* such model, and indeed every operator-norm
asymptotic representation phi_n on exhausting windows, this fixed w
satisfies ||phi_n(w)-1||_2 -> 0. Any subsequence on which the distance
stayed positive would, along a free ultrafilter, give a tracial model
in which w survived. Unitary Cauchy-Schwarz then gives tr(phi_n(w))->1.
This is an all-model no-go, unlike identity-padding examples that only
spoil one chosen realization of an otherwise hyperlinear group.

More generally, let i:D->U(A) be faithful with A MF. An MF trace on A
provides a trace-preserving map to a tracial matrix ultraproduct, so it
annihilates the nonzero positive element
(i(w)-1)*(i(w)-1), where the first factor denotes the adjoint.
Consequently no MF trace on A is faithful. We do **not** claim that A
has no faithful arbitrary trace: MF algebra structure alone does not
make every trace an MF trace. The regular trace on the completion in
section 2 is precisely where the missing matrix-trace structure matters.

This conclusion supplies an immediate research correction: arbitrary
model selection cannot rescue a universal MF-to-hyperlinear converter.
Both universal profiles
`mf-hs-defect-gap-profile` and `mf-trace-gap-defect-ratio-models` are
false, since their already-proved phase-cancelled amplifiers would make
every word of this D visible. Their conditional amplification arguments
remain valid tools for a restricted class or a particular compiler.
The group-specific task is to construct a trace seeing each word, not
merely a faithful norm representation or a regular trace on an MF
completion. The latter two already coexist with this obstruction.

## 5. Graph interfaces and boundaries

- The separation claim is a source-owned `refuted_by` of
  `mf-implies-hyperlinear` and the two universal rate-profile claims.
- The route `compiler-branch-hyperlinear-from-mf-implies-hyperlinear`
  is thereby invalidated through its false universal prerequisite.
  The particular `mf-compiler-positive-branch-is-hyperlinear` claim
  is **not** refuted: extra structure might still prove that branch.
- `regular-mf-symmetric-doubles-are-regular-mf` concerns a regular
  trace on an MF completion, not necessarily an MF trace. It is not
  contradicted by this argument and is not invalidated here.
- These deductions introduce no numerical Hilbert-Schmidt gap, no
  assertion that the commuting-lamp wreath itself is MF, and no
  separation of hyperlinear groups from sofic groups.

No builds or mathematical code were run locally. Source statements and
written arguments were inspected read-only. Cairn compilation and any
tests belong to the coordinating agent's bounded MSI validation batch.

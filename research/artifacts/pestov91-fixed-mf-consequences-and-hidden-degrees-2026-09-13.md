# A fixed MF consequence operator with arbitrary hidden computational degree

2026-09-13. Written deductions conditional on the cited repository theorems;
not new Lean formalizations or a claim of global novelty.

Propositions E--H were proposed in Section 6 of the user-supplied memorandum
*One paper: simple Kazhdan groups and the structure of MF approximation*.
The memorandum identifies its source ZIP by SHA256
`4016b82e3a9a603aae0d8e8307ae695a608c2c484a758976321f5c0398416150`.
This note checks their deductions against the current repository proofs,
strengthens F to both semidecision directions and G to a topological
embedding, and adds the exact ordinary/MF
consequence comparison in Section 5. It does not certify that ZIP or rerun
the memorandum's reported audits.

## Inputs and the fixed marking

Use the [fixed-quotient construction](pestov91-fixed-quotient-arbitrary-complexity-2026-09-13.md).
Let alpha=sqrt(2)-1, D={-j alpha mod 1:j in Z}, and beta range over
A=(0,1)\D. Put Q=EL_6(LC(Y_alpha,F_2) crossed Z), L=SL_infinity(F_2).
The input theorem supplies

    1 -> L -> H_beta --pi_beta--> Q x Q -> 1,
    Rad_MF(H_beta)=L,              deg_T WP(H_beta)=deg_T beta.

The endpoint groups are infinite simple Kazhdan LEF groups. The
[seam normal-lattice theorem](pestov91-seam-normal-lattice-2026-09-13.md)
supplies the five normal subgroups 1,L,N_-,N_+,H_beta and says every
proper quotient is LEF. Each H_beta has the same three marking formulas
(c,t,w), of orders 7,2,2, on its binary interleaving Z_beta.

Write F=F(c,t,w) and lambda_beta:F->H_beta. The recurrent binary
components are the two fixed systems C_i, i=0,1, obtained by interleaving
y in Y_alpha with the constant phase i and including both shift
alignments. Restricting u,u^-1,p, and hence c,t,w, to C_i is independent
of beta. The two parity corners identify the corresponding EL_3 groups
with Q. Fix these identifications once. Consequently

    pi_beta lambda_beta = bar_lambda:F -> Q x Q              (1)

is one fixed marked epimorphism. Abstractly isomorphic quotients alone
would not suffice for (1); the common coefficient functions and markings
are essential. Write supp(v)={i:bar_lambda(v)_i != 1}.

## 1. E: the same polynomial MF consequence operator

For a finite list R of words and an output word v, let MC_beta(R,v)
mean that every MF-target homomorphism from H_beta killing R kills v.
Put S(R)=union_{r in R} supp(r). Then, for every allowed beta,

    MC_beta(R,v) iff supp(v) is contained in S(R).             (2)

**Proof.** Every MF-target homomorphism factors through pi_beta. In a
product of nonabelian simple groups the normal closure of a set is the
product of precisely its nontrivial coordinate projections. Indeed a
nontrivial coordinate a has a nontrivial commutator with some element
of that coordinate group, since its center is trivial. This places a
nontrivial coordinate-supported element in the normal closure; simplicity
then gives that whole factor. Thus the normal closure of bar_lambda(R)
is the product of the factors in S(R).

The quotient is the product of the remaining Q factors, hence LEF and
MF. It detects every element not in this normal closure, proving (2).
More specifically, if (2) fails, either of the fixed endpoint maps with
i in supp(v)\S(R) is already a counterexample. Thus just two fixed maps
provide all counterexamples needed for these consequence queries.

Here is a direct polynomial algorithm in total **expanded** input length,
without an intercept oracle or a translation to a different coding.
For an endpoint phase i and a binary window length N, enumerate the
Sturmian words of length ceil((N+1)/2), interleave each with constant
phase i, and retain the length-N windows starting at alignments 0 and 1.
This enumerates exactly L_N(C_i). It has O(N) words. The rotation cuts
and comparisons lie in Q(sqrt(2)), with O(log N)-bit integer data, so
enumeration has polynomial bit cost.

For a word of length ell, evaluate its nine Laurent coefficient tables
on those windows with N=2ell+1, retaining all degrees -ell,...,ell.
Appending one marking letter costs O(ell) field operations per window,
so ell updates on O(ell) windows cost O(ell^3) field operations.
Uniqueness of crossed-product normal forms makes this an exact endpoint
identity test. The
[finite-window algorithm](pestov91-finite-normal-control-2026-09-13.md),
Section 4, supplies the evaluation rule; its implementation's
`window_normal_form` routine uses exactly this marking. Take supports,
form S(R), and apply (2). No part of this procedure reads beta. The
bound is not in compressed-word DAG size.

The existing `SeamGraph` executable uses a different block coding. It
must not be passed these interleaved words as though its marking agreed;
the endpoint-language enumeration just specified is the required one.

With R empty, this gives a single polynomial test for radical membership
in every H_beta. It does not test identity inside the radical. The same
consequence operator results if targets are restricted to LEF groups:
the counterexample endpoint itself is LEF. In contrast every homomorphism
to a finite group is trivial, by the input theorem, so actual finite
targets make every consequence query true. Local finite models must not
be confused with homomorphisms to finite groups.

## 2. F: recursive presentability forces a computable intercept

The following are equivalent for beta in A:

1. beta is computable;
2. H_beta has decidable word problem;
3. H_beta admits a recursively enumerable presentation;
4. identity words of H_beta in the marking (c,t,w) are computably enumerable;
5. nonidentity words in that marking are computably enumerable.

**Proof.** The input degree theorem gives 1 iff 2. Enumerate all identity
words as relators to get 2 implies 3. An r.e. presentation enumerates
proofs of identities. Express c,t,w as fixed finite words in its named
generators to obtain 3 implies 4. This argument also allows a computable
countable presentation alphabet. It requires existence of the finite
translations, not a uniform algorithm finding them from a presentation.

For 4 implies 1 use the uniform cylinder witnesses from the
[marked-subshift theorem](pestov91-marked-subshift-encoding-2026-09-13.md):
a binary word b is forbidden in Z_beta exactly when its effectively
compiled root word W_b is the identity. Thus forbidden binary words are
computably enumerable. Section 3 of the fixed-quotient construction
decides tagged-word occurrence by a finite disjunction of binary
occurrence tests, with an intercept-independent recognizability bound.
Negating that disjunction gives a finite conjunction of forbidden-word
tests. Hence forbidden tagged words can also be semidecided.

For n>=1 consider all 2^n tagged words (a,0)(v_0,1)...(v_(n-1),1),
where a is the fixed left-hand seam bit. Exactly one occurs: the unique
phase transition identifies the seam and forces v to be the first n
right-hand itinerary bits. Dovetail the nonoccurrence semidecisions until
2^n-1 candidates have been rejected. The remaining candidate computes
that prefix. The itinerary-to-intercept reconstruction in the input
theorem then computes beta. No running-time bound is claimed here.

Also 2 implies 5. Conversely, 5 enumerates occurring binary words, since
W_b is nonidentity exactly when b occurs. The finite-disjunction decoder
then semidecides tagged occurrence. Among the 2^n candidate seam prefixes,
dovetail these positive tests until the unique occurring candidate is
found. This again computes every itinerary prefix and hence beta, proving
5 implies 1. This additional direction does not require rejection tests.

In particular the noncomputable members do not provide recursively
presented examples with undecidable word problem. Within this family,
semidecidability of either identity or nonidentity forces decidability.
For noncomputable beta the word problem is neither c.e. nor co-c.e., even
when its Turing degree contains a c.e. set. Having a given Turing degree
is not the same assertion as being a c.e. representative of that degree.

## 3. G: a marked embedding with every degree dense

The map beta -> (H_beta;c,t,w) is a topological embedding of A with its
relative usual topology into the space of three-marked groups. For
each Turing degree d, the members with word-problem degree d are dense
in this image.

**Proof.** At an allowed beta, any specified finite itinerary prefix is
locally constant, since beta avoids the finitely many relevant cuts.
The fixed-quotient note transfers prefix agreement to agreement of any
prescribed finite binary language, and the marked-subshift theorem
transfers that to bounded relation tables. This proves continuity.

The converse is slightly stronger than the memorandum's continuity
claim. A prescribed finite itinerary prefix can be recovered by the
finitely many unique-seam queries and finite binary tests above. Each
binary test is a single finite relation test W_b. Agreement on sufficiently
many marked relations therefore forces agreement on that prefix. The
interval constraints from itinerary prefixes shrink to beta. Thus, for
each neighborhood of beta, some finite relation neighborhood forces the
intercept into it. This proves continuity of the inverse on the image.
It also proves injectivity: identical marked relations give identical
itineraries and hence identical intercepts.

Every nonempty relative interval in A contains a real of every Turing
degree. For the computable degree choose a rational interior point:
the nonzero cuts in D are irrational. For a noncomputable degree use an
invertible rational affine map to place a representative inside a
rational subinterval. This preserves the degree and cannot hit a cut,
because every cut is computable. The input word-degree theorem proves
the asserted density.

Consequently any finite relation neighborhood realized by this family
contains examples of every word-problem degree, with the same marked MF
quotient and the same consequence operator (2). This is relative density
in this family, not in the entire space of Kazhdan groups. It does not
assert that different intercepts give different unmarked isomorphism types.

## 4. H: the MF, amenable and locally finite radicals coincide

For every single-seam group H with infinite simple Kazhdan endpoint
groups, not just the fixed-slope family,

    Rad_MF(H)=Rad_am(H)=Rad_lf(H)=L.                         (3)

Here Rad_am denotes the largest amenable normal subgroup; Rad_lf denotes
the largest locally finite normal subgroup, whose existence in this
case is part of the assertion.

**Proof.** L is locally finite, amenable and normal. Each endpoint Q_i is
nonamenable: amenability gives almost invariant vectors in the regular
representation, while property (T) gives a nonzero invariant vector,
which would force the discrete group to be finite. Since Q_i is infinite
simple, it has no nontrivial amenable normal subgroup. The two coordinate
images of any amenable normal A in H are amenable and normal in Q_i,
so are trivial. Hence A<=L. Every locally finite normal subgroup is
amenable and is also contained in L. This proves both maximalities;
the input exact MF-radical theorem gives the remaining equality.

No corresponding equality for all dynamical crossed-product groups,
or characterization of MF groups by their amenable radicals, is asserted.

## 5. A further deduction: the exact gap from ordinary consequences

Let OC_beta(R,v) mean membership of lambda_beta(v) in the normal closure
of lambda_beta(R), equivalently consequence under all group-target maps.
Then

    OC_beta(R,v) iff
      v=1 in H_beta,                         if all r in R equal 1;
      supp(v) is contained in S(R),          otherwise.       (4)

**Proof.** In the first case the normal closure is trivial. Otherwise
the five-element normal lattice says it contains L, so the correspondence
theorem and the coordinate normal-closure calculation identify it with
pi_beta^-1(product_{i in S(R)} Q_i). This proves (4).

Combining (2) and (4) gives the exact discrepancy:

    MC_beta(R,v) and not OC_beta(R,v)
      iff every premise is already the identity in H_beta
          and 1 != lambda_beta(v) belongs to L.               (5)

Thus imposing any genuinely nontrivial relation makes ordinary and MF
consequences coincide for that premise set: the quotient is already LEF.
Deciding whether the premises are genuinely nontrivial can itself carry
all the computational difficulty.

The full ordinary normal-consequence decision set has Turing degree
deg_T beta. Its lower bound is the word problem, using R empty. Its
upper bound follows from (4), a word-problem oracle, and the fixed
polynomial endpoint tests. Therefore every Turing degree occurs for
ordinary consequence while MF consequence remains one fixed polynomial
language. This conclusion strengthens the memorandum's comparison with
the word problem without changing the construction.

## Verification and dependence

The arguments here check the deductions from the stated seam, marking,
word-degree and finite-window inputs. They do not independently verify
the full analytic obstruction or simplicity proofs on which those inputs
depend. The polynomial bound is a proof about the specified algorithm,
not an empirical complexity estimate. The density and presentability
arguments are not claims of an effective presentation of all members.
Cairn receipts, when attached, certify dependency checks only.

## Cairn receipt

Cairn 2.13.1 checked the ten new claim/route nodes against base
`519394f6fa43a224e240b535a4e1aa25dde6ae87` on MSI in 41.103 seconds.
Check and preview both returned zero; all five targets were ESTABLISHED,
with no baseline or current graph errors. The graph contained 10,724
claims and 10,933 routes. The archive runner applied the upstream deletion
manifest as well as additions and modifications, preserving the removal
of the unrelated relative-K1 proof route. The
[receipt](pestov91-memo-deductions-cairn-receipt-2026-09-13.json) records
the delta and runner hashes. This paragraph, the receipt, and an editorial
wording correction were added after the check; the checked claim and
route bodies were unchanged. No Lean build or exhaustive verification of
the infinite theorems was run.

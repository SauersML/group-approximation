# After Liu: precise remaining approximation frontiers

Date: 2026-09-20. Written deductions and research interfaces, not Lean
certification or an assertion that the open targets below are solved.
Jihao Liu's internality theorem and Andreas Thom's conditional
normalization/double mechanism provide the new nonhyperlinear inputs.
The ring compression calculations and compiler arguments are separate
Cairn premises. No priority claim is made for the combinations.

## 1. Recognition: replace the universal shortcut with an exact host task

The MF/nonhyperlinear double refutes a universal conversion from MF group
models to hyperlinear models. It does not refute hyperlinearity of the
particular positive branch of the finite-presentation compiler. Nor is
that positive-branch property necessary for every possible proof of
recognition hardness: another compiler could work.

For every finite seed code d and positive index e in INF, the actual
compiler has an embedded bridge Q_e(d) in its Higman host H_e(d), and
a positive embedding of Q_e(d) into P=F_2 x F_2. The new target asks
that there exist a descending separating finite-quotient chain of P
whose pulled-back kernels J_n have the required action models. Namely,
`compiler-higman-coset-chain-is-sofic` asks for sofic set-action models
of H_e(d)/iota(J_n) for every n, every seed d and every positive e.
The chain may depend on d,e; it need not be selected algorithmically.

**Seed-quantifier correction (independent review, 2026-09-20).** The
old Rice proof said the compiler's positive output was seed-independent
because the recursive switch collapses to the trivial group. That
inference is unsupported: effective Higman receives a presentation,
and identical abstract bridge groups need not give identical hosts or
ropes. The new claim `mf-compiler-is-uniform-in-finite-seeds` records
only joint computability in d,e, the seed embedding on FIN, and the
existing MF proof on INF. Its route retains d through the arbitrary
seed switch, Mikhailova benign witness and special rope-HNN argument.
No new approximation permanence theorem is imported.

Uniformity here concerns the output presentation code, not a global
computable map of seed generators into every output. On FIN the seed
embedding uses a tail copy after the last switch event, whose cutoff
cannot be selected computably on all indices. This respects
`fp-inf-fin-compiler-uniform-seed-map-firewall-2026-08-26.md`.

The Rice criterion now fixes the SAME forbidden seed d in its two
hypotheses: that seed fails the property, and every R_e(d) on INF has
it. Uniformity over all d is a sufficient stronger positive hypothesis,
and is now explicit in the open hyperlinear and host-chain targets.
Proving one old fixed-seed family hyperlinear is not enough to replace
the negative seed by an arbitrary nonhyperlinear group. The historical
seed-independence language in older artifacts is superseded here.

The existing conditional theorem
`higman-host-coset-soficity-makes-compiler-rope-sofic` turns those exact
models into each actual sofic compiler rope R_e(d). Sofic implies hyperlinear. The
new route `compiler-hyperlinear-from-host-coset-chain` thus provides a
sufficient route to the positive branch without the refuted universal
MF premise. Its pre-existing host theorem remains a written, unreviewed
input; this note identifies its interface rather than certifying every
step of that theorem anew.

The first constructive test is to follow the finite coset colors through
the actual Higman embedding steps. Abstract embeddability of Q_e into P
does not suffice: switching to P only on positive indices would require
deciding INF. Ordinary Higman embedding preserves neither residual
finiteness nor the needed relative approximation information.

A unitary-only alternative remains weaker and potentially easier:
produce models of each actual R_e with a dimension/defect rate or an
HS defect/word-gap profile satisfying the existing conditional
amplification lemmas. Those lemmas survive the refutation of their
universal hypotheses. An arbitrary trace on an MF completion is not
automatically an MF trace, and a hyperlinear representation need not
factor through a particular chosen MF completion. Neither equivalence
should be assumed in selecting a positive-branch model.

### A useful conditional dichotomy

Taking the existing uniform compiler, locally-indicable-rope theorem,
and recognition reduction as inputs, either:

1. every positive rope R_e(d), for every finite seed d, is hyperlinear,
   giving the recorded finite-
   presentation Pi-zero-two completeness consequence; or
2. some actual R_e(d) is a finitely presented, locally indicable MF
   group that is not hyperlinear.

The hypothesis and its negation partition the cases, but their useful
consequences need not be exclusive: recognition hardness could hold by
another construction even in case 2. This is not an equivalence between
hardness and branch hyperlinearity, or a proof that case 2 occurs.
The large uniform compiler and recognition machinery remain named
premises, not silently discharged by Liu.

Local indicability in this dichotomy uses the structural argument
below for every retained seed parameter, not an identification of
the resulting groups. Its proof only needs the stated Bass-Serre data
and the positive bridge B3(1), which hold for all d on INF.

The local-indicability argument has a concrete Bass--Serre explanation.
The first rope retracts onto a finite product of free groups, with free
kernel, since the retraction is injective on its vertex group. The
second rope projects onto the first; its kernel has trivial edge
stabilizers and vertex stabilizers that are conjugates of the positive
bridge, a subgroup of F_2 x F_2. It is a free product of such groups
and a free group. Local indicability is closed under these free products
and extensions. In particular no nontrivial finitely generated Kazhdan
group embeds in a positive rope. This explains why copying the known
Leavitt subgroup obstruction into that branch is not an available test.

## 2. Rank approximation: the most obvious unitary lift fails

The target `leavitt-el3-rank-models-over-finite-fields-are-trivial` is
still open. One cannot transfer Liu's Hilbert-space internality theorem
merely by representing finite-field matrices as permutations of vectors.

Here is the exact obstruction to that first transfer attempt. For
A in GL_d(F_q), let r=rank(A-I), and let P_A be the permutation matrix
of its action on all q^d vectors. Then

    normalized_trace(P_A) = q^(-r),
    ||P_A-I||_2^2 = 2(1-q^(-r)).

The fixed-vector space has dimension d-r, proving both formulas.
For a rank-one transvection with d tending to infinity, normalized
rank distance is 1/d and tends to zero, but the squared HS distance is
the fixed positive number 2(1-1/q). Thus the vector-permutation map
does not even respect the zero-distance equivalence relation needed for a homomorphism
of rank ultraproducts into tracial matrix ultraproducts. Fourier
conjugation cannot fix this, since it preserves normalized trace.

This rules out this particular functor, not every possible unitary
lift or every rank-metric obstruction. A separate existing counterexample
`kazhdan-group-rank-models-admit-no-expander-decomposition` already
rules out obtaining finite-field block rounding from property (T)
alone. A viable new lemma must use the joint compressor/elementary-root
relations beyond property (T). The remaining concrete test is the
two-root identity recorded in
`rank-models-of-el3-satisfy-the-two-root-identities`, not a substitution
of rank for HS norm in an analytic inequality.

Failure in characteristic two is not failure in every characteristic.
The foundational class distinctions are in Arzhantseva--Paunescu,
[*Linear sofic groups and algebras*](https://arxiv.org/abs/1212.6780).

## 3. Hyperbolicity: an unchanged compression certificate cannot transfer

The new root `nonhyperlinear-hyperbolic-group` is open. A nonhyperlinear
quotient does not make a hyperbolic cover nonhyperlinear. Likewise the
known torsion-free double with cohomological dimension at most three
has not been shown hyperbolic.

There is a stronger existing obstruction to a naive embedding strategy:
`hyperbolic-local-embedding-kills-compression-certificates` says that
groups locally embeddable in hyperbolic groups cannot carry the relevant
nontrivial finite compression certificate. Thus the unchanged known
witness cannot be embedded in, or recovered as an appropriate marked
limit of subgroups of, hyperbolic groups. This is an established barrier
in the repository, not a new consequence of Liu's internality.

A different route remains the recorded specialization of
[Dogon--Vigdorovich, Theorem 1.3](https://arxiv.org/html/2506.20843v2):
suitable flexible HS stability for a Kazhdan hyperbolic
group with positive second Betti number yields a nonhyperlinear finite
central extension, still hyperbolic. The new route links this existing
conditional theorem to the new root. No stability hypothesis is proved
here. For the GHB7 candidate the positive second Betti number belongs
to its torsion-free congruence kernel; GHB7 itself has b_2=0. Broad
class-wide stability is not interchangeable with this candidate-specific
target, and known Kazhdan property alone is insufficient.

## 4. One relator: a genuinely different obstruction is needed

The new root `nonhyperlinear-one-relator-group` is also open. Known
torsion one-relator groups are residually finite, whereas torsion-free
one-relator groups are locally indicable and have no nontrivial finitely
generated Kazhdan subgroup. The existing source-backed nodes record
these two separate facts. Neither gives hyperlinearity of every
torsion-free one-relator group.

A short multi-relator presentation is not a one-relator presentation.
Neither the small Leavitt presentation nor its marked central HNN
extension supplies this target. The positive compiler ropes are locally
indicable, but their presentation is not one-relator either. The useful
new task is compatibility of unitary approximations through actual
Magnus/HNN decompositions, or an obstruction not requiring the known
Kazhdan compression configuration. The source scope of current positive
one-relator approximation results must be retained; see for example
Berlai's [2025 preprint](https://arxiv.org/abs/2502.05064), rather than
assuming general soficity or hyperlinearity.

## 5. What is actually wired

- A stronger exact relative-coset target and route to the existing
  positive compiler branch; that branch and finite-presentation exact
  recognition classification remain open.
- Separate nonhyperlinear hyperbolic and one-relator roots, each with
  a route to its weaker existing nonsofic root. No geometric existence
  theorem has been asserted.
- A proved obstruction to the natural finite-vector permutation lift
  in the rank target's Attempts section.
- The hyperlinear-but-nonsofic target remains open; Liu's negative
  examples eliminate candidates for it rather than solve it.

The parallel integration artifacts record the completed MF separation,
linear-constraint-game existence and concrete central seed, all-field
stable finiteness, and intermediate-wreath obstruction. Those deductions
retain Liu, Thom and all additional literature inputs explicitly.

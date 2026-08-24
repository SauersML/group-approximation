# New LLP and compiler-fence sources: primary-source audit (2026-08-23)

This audit checks six August-2026-frontier inputs against the current Cairn.
It records only exact theorem scopes; none of the papers supplies an
unconditional explicit non-hyperlinear group.

## Primary files

The PDFs were downloaded directly from arXiv on 2026-08-23.

| arXiv | title | SHA-256 |
|---|---|---|
| `2606.18369v1` | Paulsen--Rahaman--Samei, *Amenable traces and the joint numerical radius* | `e2ffcc5932bfd40c68097b5c19010fd28a470a7f56c6df5545a4c5bb7a6d7ac7` |
| `2607.11001v1` | Harris, *Ubiquity of Counterexamples to the Smith-Ward problem* | `c2c7b73b4fa2c37d362bc32edb3beaebba69431431a9c6fc8afa958df4cbd81f` |
| `2607.04274v1` | Scherer, *A Three-Dimensional Operator System without the Smith--Ward Property* | `058642ae8c146d30a9759beae162eb94bc64db9377980ffed9bd8594d22d03a7` |
| `2608.05378v1` | Lalonde, *Maximally entangled states are not complete for pseudo-telepathy* | `94bd810647c4c0331da9aefdd74cb23aeaddb67d344bb020cb858a57b12e06da` |
| `2608.11139v1` | Tang--Zhu--Bai--Wang--Chen, *A Sharp Local-Question Threshold for GHZ-Equatorial Completeness in Four-Player XOR Games* | `f9f955ead9b5ea032b6bff39b599b19c5ee5cec4ee98acb9d3b9d28797640156` |
| `2608.15409v1` | MacMahon, *1-Bounded Entropy for C-star Algebras* | `15696fe1d545b706383b9d346fbe54dbb8816c5b4b6234c440b3f60c05860332` |

Primary links:

- <https://arxiv.org/abs/2606.18369>
- <https://arxiv.org/abs/2607.11001>
- <https://arxiv.org/abs/2607.04274>
- <https://arxiv.org/abs/2608.05378>
- <https://arxiv.org/abs/2608.11139>
- <https://arxiv.org/abs/2608.15409>

## 1. The genuinely new closing criterion

Paulsen--Rahaman--Samei Theorem 4.6 says exactly:

```text
G hyperlinear + pi nonamenable + lambda_G prec pi
  => C^*_pi(G) does not have LLP.                      (A1)
```

Thus LLP of an intermediate representation completion can close the group
goal without property (T), non-residual-finiteness, or LLP of `C^*(G)`.
This is integrated as
`llp-regular-dominating-completion-forces-nonhyperlinear`.

Theorem 4.9 specializes `(A1)` to a Brown--Guentner ideal completion: `G`
must be nonamenable, `D` must be an algebraic ideal of `ell^infinity(G)`
containing `c_00(G)`, and `C^*(G) != C^*_D(G)` canonically.  Under those
hypotheses `C^*_D(G)` has no amenable trace, and hyperlinearity of `G`
forces failure of LLP.  The theorem does not require `C^*_D(G)` to differ
from the reduced completion.  Accordingly the Cairn target says "proper
D-completion," not the stronger and potentially ambiguous "strict exotic
completion."

The resulting new root route is
`nonhyperlinear-from-proper-d-completion-llp`.  It has one honest open
dependency: `explicit-proper-d-completion-with-llp-exists`.

## 2. Harris is a negative normal form, not an LLP algorithm

Harris Theorem 2.4 constructs, from `n` unitary generators of a unital
C-star algebra `A`, a structured three-dimensional hyperrigid operator
system `span{I,D,G}` in `M_(n+2)(A)` which generates that matrix algebra.
Corollary 3.5 proves that if `A` fails LLP, this system fails LP.

This compresses every negative certificate to dimension three.  There is
also a stronger positive composition: Proposition 3.4(2) says LP of this
particular hyperrigid system implies LLP of the ambient matrix algebra.
Consequently PRS + Harris give the exact derived criterion

```text
lambda_G prec pi + pi nonamenable + LP(S_pi)
  => LLP(C^*_pi(G))
  => G non-hyperlinear.                                (A2)
```

**CORRECTED 2026-08-23.**  This section originally continued: "Conversely,
LLP of the ambient algebra passes to the matrix amplification and restricts
to LP on this finite-dimensional subsystem.  Therefore the Harris system
gives the exact equivalence `LP(S_A) <=> LLP(A)`  (A3)."  That converse is
**withdrawn**.  LLP of `A` is a statement about ucp maps defined on `A` (or
on `M_k(A)`); LP of `S_A` quantifies over every ucp map out of `S_A` into a
quotient, and such a map need not extend to the ambient algebra.
Hyperrigidity supplies uniqueness of extensions of representations, not
existence of an extension of an arbitrary ucp map into a prescribed
quotient.  Only

```text
LP(S_A) => LLP(A)                                      (A3')
```

is available, which is Proposition 3.4(2) plus matrix/corner permanence, and
is the same implication as Corollary 3.5 read contrapositively.  For a
finitely generated nonamenable group, taking `pi=lambda_G` makes `LP(S_G)`
*sufficient* for `LLP(C^*_r(G))`, and its positive side already forces
non-hyperlinearity by Paulsen--Rahaman--Samei.  This does not make LP/LLP
decidable and does not output a generic finite SDP dual.  The correction and
its (nil) cascade effect are recorded in
`harris-lp-to-llp-implication-is-one-directional`; the negative normal form
is recorded in `llp-failure-has-three-dimensional-hyperrigid-witness`, whose
own equivalence paragraph is corrected to match.  Note this section's own
"Net cascade change" paragraph below already said "a sufficient target, not
an equivalence with ambient LLP" -- the two halves of this audit disagreed,
and the sufficient reading is the correct one.

Scherer's `span{1,D,K} subset M_4(C^*_r(F_2))` is the explicit precursor.
The Scherer and Harris introductions give incompatible descriptions of the
model system's exactness.  No exactness claim from that comparison is used
in Cairn; the common hyperrigidity/nonlifting statement is enough.

## 3. Lalonde is a state-conversion fence

Lalonde Theorem 1.1 gives a `4 x 3` input, `6 x 6` output game with a
perfect local-dimension-six strategy and no perfect maximally entangled
strategy.  Section 4.2 gives the exact algebraic interface: a maximally
entangled strategy would induce a trace on the square-root effect algebra
annihilating every losing product.  A strengthened level-4 tracial-NPA
relaxation has a 5.6 MB rational infeasibility certificate; the theorem is
also formalized in Lean.

The correct conclusion is not that every notion of "tracial strategy" is
impossible in every presentation.  It is that this explicit commuting-
effect algebra has no trace on its perfect losing face, even though a
perfect finite vector-state strategy exists.  This directly fences silent
replacement of nontracial Gram data by the normalized-HS vector.

There is also a sharply conditional positive use.  The rational finite-
level certificate, or equivalently an ultraproduct compactness argument
from its exact infeasibility conclusion, gives a positive dimension-free
loss gap for finite-matrix tracial tuples satisfying the game-algebra
relations.  This is integrated as
`lalonde-certificate-gives-dimension-free-tracial-gap`.  If a finite marked
group compiler could preserve Lalonde's nontracial perfect strategy for
nontriviality while decoding canonical group microstates to that forbidden
tracial face on one common carrier, the gap would prove the group
non-hyperlinear.  The route
`nonhyperlinear-from-lalonde-certificate-group-compiler` records exactly
that implication and leaves the vector-state/common-carrier compiler open.

## 4. Tang et al. separate abelian phase and ordered group words

Tang et al. Theorem 1.1 proves the exact four-player threshold.  At most
three active questions per player, commuting value one is equivalent to a
perfect MERP strategy.  At four, the Klein game has commuting value one and
no MERP strategy.  Proposition 2.2 identifies the mechanisms: a PREF is an
integer incidence/phase obstruction, whereas a true refutation is an
ordered product whose words freely reduce.  At three every PREF lifts; at
four one need not.

The four-question example is not known to separate finite-dimensional and
commuting values.  It is integrated only as a phase-to-word compiler fence.

## 5. MacMahon supplies a bridge and a trace-blindness warning

MacMahon proves `h^top(A) <= h(A)` (Theorem 8.1) and the variational
principle `h(A)=sup_tau h(M_tau)` (Theorem 6.1 in the introductory
specialization).  The latter makes the C-star invariant blind to which
trace is canonical.  It therefore cannot promote an arbitrary non-CE trace
on a group C-star algebra to the canonical group trace.

Theorems 9.1 and 9.2 compute the operator-system versions from a spanning
set, so Harris's three-dimensional witnesses fall within the new invariant
formalism.  Neither source proves that the entropy detects LP or LLP.  No
route edge is added for that speculative connection.

## Net cascade change

The new route family to the root is conditional on a strictly different
LLP target:

```text
explicit proper D-completion with LLP
  -> Paulsen--Rahaman--Samei obstruction
  -> explicit non-hyperlinear group.
```

The sharper positive interface is `(A2)`: one may replace ambient LLP by
LP of the explicit three-dimensional Harris generator system.  This is a
sufficient target, not an equivalence with ambient LLP.

Harris narrows how that target can fail.  Lalonde and Tang rule out two
unsound compiler shortcuts.  MacMahon unifies norm and trace microstate
invariants but, because of its supremum over traces, does not solve
canonical trace promotion.

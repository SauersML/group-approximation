# A second-level Rice theorem for approximation properties of groups

Assembled 2026-08-26.  Every statement below is proved in the named Cairn
nodes; this note only puts them in one place and fixes notation.

## Setting

`P_fp`: finite presentation codes whose group has `P`.  `P_rec2`:
two-generator recursive presentations (indices of enumerators of relators)
whose group has `P`.  `P_V`: pairs of words in Higman's universal finitely
presented group `V` generating a subgroup with `P`.  `INF`, `FIN`: indices
of programs with infinite, finite domain; `Pi^0_2`- and
`Sigma^0_2`-complete respectively.

A **local approximation property** `P_M` is defined by a model predicate on
finite multiplication tables: `G` has `P_M` iff every finite table of `G`
has models of every accuracy.  Sofic, hyperlinear, operator-MF, LEF, weakly
sofic and linear sofic are of this form.

## Theorem 1 (marked-group closedness; `local-approximation-properties-are-marked-closed`)

For every model predicate `M`, `P_M` is hereditary and local, closed in
the space of marked groups, and every finitely generated group failing
`P_M` has a finitely presented cover (finitely many of its relators)
failing `P_M`.  For soficity this is `Covers/TableCover` in Lean.

## Theorem 2 (second-level Rice; `second-level-rice-theorem-for-local-approximation-properties`)

If residually finite groups have `P_M` and some finitely generated group
does not, then: `P_fp` is `Sigma^0_1`-hard and `NON-P_fp` is `Pi^0_1`-hard
(so neither is r.e./co-r.e. respectively, and neither is decidable);
`P_rec2` and `P_V` are `Pi^0_2`-hard and their complements
`Sigma^0_2`-hard; and when `P_rec` is `Pi^0_2` these are
`Pi^0_2`-complete, with `P_fp in Pi^0_2 \ Pi^0_1` and
`NON-P_fp in Sigma^0_2 \ Sigma^0_1`.

Proof shape: Theorem 1 turns the counterexample into a finitely presented
seed; the parametric FIN/INF switch (`ParametricFinInfSwitch`, route
`arbitrary-forbidden-seed-hereditary-property-switch-proof`) with that seed
has values `1` on `INF` and the seed on `FIN`; the two-generator
bidirectional bridge `B2(-)` has residually finite value on `1` and
contains the seed otherwise; Mikaelian's explicit Higman embedding of the
free product of the family puts everything inside `V`; Adian--Rabin
(`AdianRabinGeneral`) handles finite presentations.

## Theorem 3 (soficity; `sofic-recognition-has-a-pi2-upper-bound`, `sofic-recognition-two-generator-recursive-is-pi2-complete`, `sofic-recognition-finite-presentations-arithmetical-position`)

Unconditionally: `SOFIC_rec2` and `SOFIC_V` are `Pi^0_2`-complete;
`SOFIC_fp in Pi^0_2 \ Pi^0_1` and `NONSOFIC_fp in Sigma^0_2 \ Sigma^0_1`.
The certificate is a permutation tuple with small Hamming relator defects
and large Hamming displacement on listed words; the checker is primitive
recursive.  The only input from the nonsofic-groups program is one finitely
presented nonsofic group (`Endpoint/MainResults`).

## Theorem 4 (dichotomy; `approximation-property-recognition-dichotomy`)

Either every group is hyperlinear and the recognition problems are trivial,
or `HYP_rec2` and `HYP_V` are `Pi^0_2`-complete and `HYP_fp` is undecidable
with non-r.e. complement.  Equivalently: a non-hyperlinear group exists iff
a finitely presented one exists iff `HYP_fp` is undecidable iff `HYP_rec2`
is `Pi^0_2`-complete.  Same for weakly sofic and linear sofic
(`Pi^0_2`-hard).

## Theorem 5 (residual finiteness; `residual-finiteness-of-enumerated-presentations-is-pi3-complete`)

On countably generated recursively enumerated presentations residual
finiteness is `Pi^0_3`-complete, while LEF is `Pi^0_2`-complete on the same
syntax; the two coincide on finite presentations.  Mechanism: for
`a_j = b^j a b^-j` the central HNN extension
`H_c = <a, b, s | [s, a_j] = 1, j < |W_c|>` is residually finite iff `W_c`
is finite (a finitely generated subgroup of a free group is profinitely
closed; the subgroup on all nonnegative conjugates has `b^-1 a b` in its
closure, so `[s, b^-1 a b]` dies in every finite quotient), and countable
free products encode the outer universal quantifier.  Upper bound by
compactness of `Q^N`.  Open: the two-generator version (needs an effective
Wilson envelope) and `Pi^0_2`-completeness of `RF_fp` (residually finite
Higman).

## What remains open

* `SOFIC_fp` `Pi^0_2`-complete: needs `sofic-safe-finite-presentation-compiler`.
* `hyperlinear-recognition-undecidable`: equivalent to the program goal; a
  MIP*=RE-style reduction with exact relations on the positive side would
  prove it without exhibiting a group.

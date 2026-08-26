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

## Theorem 6 (amenability; `amenability-two-generator-recursive-is-pi2-complete`)

Amenability is `Pi^0_2`-complete on two-generator recursive presentations,
metabelian is `Pi^0_2`-complete, and containing `F_2` is
`Sigma^0_2`-complete.  Upper bound: Kesten's criterion (return
probabilities of the simple random walk, certified by derivation counts).
Hardness: `G_J = <a, t | [a, t^j a t^-j], j in J>` is `A(Gamma_J) x| Z`
with `Gamma_J` the shift graph of `J`, amenable iff `J = Z_{>0}`; reduce
from `TOT`.  Amenability is not a local approximation property, so this is
outside the Rice theorem, yet lands at the same level.

Sharpening of Theorem 5: residual finiteness is `Pi^0_3`-complete already at
two generators (`residual-finiteness-two-generator-recursive-is-pi3-complete`,
via `G_J = <a,t | [a, t^j a t^-j], j in J>` residually finite iff `J u -J u {0}`
is profinitely closed, `shift-raag-family-is-rf-iff-symmetrized-index-set-closed`,
with rows `2^x(4j+1)`), and at three generators (`residual-finiteness-three-generator-recursive-is-pi3-complete`),
via `H_J` residually finite iff `J` profinitely closed in `Z`
(`centralizing-hnn-over-conjugate-basis-is-rf-iff-index-set-closed`) and the
dyadic index sets (`index-set-profinitely-closed-is-pi3-complete`); the same
`H_J` are LEF and sofic for every `J`.

## Theorem 7 (property (T); `kazhdan-property-t-of-finite-presentations-is-sigma1-complete`)

Kazhdan's property (T) is `Sigma^0_1`-complete on finite presentations
and on two-generator recursive presentations: semidecidable (Ozawa's
sum-of-squares criterion, rationalized by Netzer--Thom), and
`Sigma^0_1`-hard because the Rabin group `K(w)` is trivial when `w = 1` and
a nontrivial amalgam over `F_2` otherwise, which fails Serre's FA and
hence (T).  Not a Markov-property argument: (T) is not hereditary; the
negative branch is a *splitting*.

## Further rows

* Amenability on finite presentations: `Pi^0_2 \ Pi^0_1`
  (`amenability-of-finite-presentations-arithmetical-position`);
  completeness open (`amenability-of-finite-presentations-is-pi2-complete`,
  root) because Higman-type compilers introduce free subgroups.
* Residually `p`: `Pi^0_3`-complete on two-generator recursive
  presentations for every prime `p`
  (`residually-p-two-generator-recursive-is-pi3-complete`).
* Weak soficity and linear soficity: `Pi^0_2` on recursive presentations
  (`weak-soficity-recognition-has-a-pi2-upper-bound` via Glebsky's
  product-quotient characterization; `linear-soficity-recognition-has-a-pi2-upper-bound`
  via the rank metric), hence trivial-or-`Pi^0_2`-complete dichotomies.
* Finite presentability: `Sigma^0_2`-hard, `Sigma^0_3`, on two-generator
  recursive presentations (`finite-presentability-two-generator-recursive-is-sigma2-hard`).
* Fixed ambient: inside Higman's universal group, two-generated subgroups
  realize levels three (residual finiteness), two (amenability) and one
  (property (T)) (`fixed-ambient-subgroup-levels-rf-amenable-t`).
* Ledger of all cells: `arithmetical-complexity-table-of-group-properties`.
* Conditional: `hyperlinear-fp-recognition-complete-iff-nonhyperlinear-group`
  needs only `mf-compiler-positive-branch-is-hyperlinear` (quasidiagonality
  of the regular trace of the MF compiler's positive branch).

## Lean status (2026-08-26, 03:45)

Kernel-checked on main: `Computability/HereditaryPropertySwitchCompleteness`
(`enumeratedCodeProperty_pi02Hard` for every hereditary property with a
finitely presented forbidden seed); `Computability/SoficRecognitionSecondLevel`
(`soficCode_pi02Hard`, `nonsoficCode_sigma02Hard`);
`Computability/SoficMicrostateNormalForm` and `SoficRecognitionPi02`
(`pi02_isSofic`, `sofic_fp_strict_position` on finite codes);
`Computability/SoficEnumeratedPi02` (`sofic_enum_pi02Complete`,
`nonsofic_enum_sigma02Complete` on enumerated codes: the first
machine-checked exact arithmetical classification of a group approximation
property); `Computability/HyperlinearUndecidabilityRoute`
(`not_computablePred_iff_exists_nonhyperlinear_code`, alongside a peer
session's `exists_not_isHyperlinear_iff_codeProperty_not_computable`);
`Covers/HyperlinearTableCover` (peer session).  `Computability/ProfinitelyClosedIndexSet` (`pi03Complete_closedIndex`, the
computability core of the `Pi^0_3` residual-finiteness theorems);
`Computability/LEFEnumeratedPi02` (`lef_enum_pi02Complete`, the second exact
classification).

## What remains open

* `SOFIC_fp` `Pi^0_2`-complete: needs `sofic-safe-finite-presentation-compiler`.
* `hyperlinear-recognition-undecidable`: equivalent to the program goal; a
  MIP*=RE-style reduction with exact relations on the positive side would
  prove it without exhibiting a group.

# Atlas typed hard/interior/comb row-census acquisition audit

Date: 2026-08-23

## Outcome

The repository contains enough literal data to replay the finite Atlas words,
but not enough typed data to form the coefficient matrix `[C D]` required by
`atlas-authenticated-s3-extension-minor-decodes-pairings`.  In particular, a
rank calculation from the currently stored JSON files would have to invent
either channel equations or identifications of external multiplicity
reservoirs.  No such surrogate calculation is admissible.

The boundary is finite and explicit.  A complete census becomes mechanical
once the acquisition record in Section 3 is supplied.

## 1. Literal data which are present

| datum | source | exact content |
|---|---|---|
| six quotient relators | `experiments/atlas-six-relator-relative-pieces.json` | the complete free-product syllable words for `s_0`, `s_11`, `s_30`, `s_44`, `s_55`, and `c_19243`; lengths `6,8,8,8,8,16` |
| two hard boundary representatives | `experiments/atlas-boundary-11-30.json` | the class-11 and class-30 words and their two factor projections |
| collision word | `experiments/atlas-word-19243.json` | the collision-tree word and its factor projections |
| full first boundary | `experiments/atlas_self_similarity_global_audit.py` | an exact reconstruction algorithm for all 234 first-boundary words |
| A4 authentication packet | `experiments/atlas_a4_packet_generation.py` and `experiments/atlas_a4_packet_component_audit.py` | an exact reconstruction of 30 shortest A4 contexts and the 12 distinct pair constraints, including chart labels and tree indices |
| raw and comb operator names | `experiments/atlas-raw-compressor-source-words.json` | free-product words of lengths 25 and 175 whose exact Leavitt values are the scalarized raw swap and comb compressor |
| shallow raw/comb kernel search | `experiments/atlas_raw_comb_mixed_relations.py` | an exact enumeration algorithm for radius-three collisions between the raw closure and its comb conjugate |

The last two rows require care.  A source word is an operator name, not an
equation in a microstate.  Also,
`experiments/atlas-raw-comb-mixed-relations.json` stores only the collision
counts (167 buckets, 18 shortest buckets), not the collision normal forms
held in the script's local `records` variable.  Even regenerating those
normal forms would not select a packet consequence or give its bounded
normal-closure provenance.

## 2. Data absent from the typed decoder

The desired entries

```text
R0^* W L0-W,   R1^* W L1-W,   R0^* W L1
```

are currently semantic objects of the robust radical-quotient/Fourier gate,
not named Wedderburn blocks of the literal word files.  This is explicit in
`notes/ATLAS_RELATIVE_PERFECTNESS_AND_COEFFICIENT_ENDPOINT.md` at `(RPC128)`
and in `notes/TRUE_DIAGONAL_PAIRING_DEFECT_SUPPLIES_SPECTRAL_INVARIANCE.md`:
the common-coordinate extraction of `W,R0,R1,L0,L1` is still the live
theorem.  `notes/FALSE_TWO_RAW_COMPRESSORS_DO_NOT_IDENTIFY_FIBERS.md` proves
why the two printed compressor words do not supply the missing
identification: they leave arbitrary centralizer-valued fiber holonomy.

Consequently the following literal fields do not yet exist:

1. word-visible finite-carrier projectors together with a finite-matrix-only
   positive-mass selection rule defining one common corner `L2(P M Q)` for
   every selected term;
2. explicit compressed-word definitions of `W,R0,R1,L0,L1` on that selected
   corner;
3. a selected list of hard/interior/comb **equations** constraining those
   blocks (as opposed to the raw and comb operator names);
4. for every selected normal-closure consequence, a fixed bounded filling in
   the six relators;
5. a parenthesization/recoupling path for every projected product, including
   every intermediate S3/S4 type and Clebsch--Gordan channel;
6. a complete list of all other path products in the same rows.  These are
   the nuisance columns `D` and may not be discarded.

The six relator words themselves are not missing.  What is missing is the
typed projection which connects their block paths to the radical-quotient
arrows.  Conversely, the raw/comb words are present, but no committed row
says which equality involving them is to be projected.  Group-word
associativity does not repair the missing recoupling record: different
Clebsch--Gordan bracketings are related by nontrivial Racah transforms, so a
coefficient census must declare one and transport every term consistently.

## 3. Bounded acquisition schema

A complete conservative census must contain one record per projected scalar
row with all of these fields:

```text
row_id
relation_id
relation_left_word
relation_right_word
normal_closure_filling              # if not a defining relator
product_parenthesization
source_projector_word
target_projector_word
common_source_corner_id
common_target_corner_id
finite_matrix_selection_rule
selection_hypotheses
selection_mass_lower_bound
selection_HS_loss_bound
intermediate_type_path              # S3/S4 labels at every multiplication
clebsch_gordan_channel_path
exact_coefficient_Q_sqrt2
reduced_multiplicity_monomial
column_class                        # X00, X11, X01, or nuisance:<stable id>
```

Acceptance requires:

* every relation word is one of the six literal relators or comes with a
  fixed bounded normal-closure filling in them;
* every operator term has the same declared source and target corner before
  scalar row operations are performed;
* the common multiplicity cut is produced by a genuinely finite-matrix-only
  rule (for example a spectral/Gram selection on regular microstates), with
  a dimension-independent HS loss and a fixed positive normalized-trace
  lower bound;
* the three desired column tags are justified by the explicit compressed
  definitions of `W,R0,R1,L0,L1`;
* every untagged reduced path monomial is retained as a distinct nuisance
  column unless an exact packet law identifies it;
* replaying the declared recouplings reproduces every coefficient in
  `Q(sqrt(2))` exactly.

The finite-matrix-only qualifier is load-bearing.  A purely algebraic
word-visible cut would hold in the exact Leavitt tracial countermodel as
well.  Combined with quotient-rank three and the spectral Leavitt endpoint,
it would manufacture a contradiction inside that exact model.  Equivalently,
`universal-atlas-ideal-cannot-force-hall-deficit` already rules out the
analogous universal forbidden-block extraction.  The authentication must
therefore use finite multiplicity/regular-microstate information that is not
a universal star-ideal consequence.  Literal finite-carrier projectors are
allowed; universally identifying their external multiplicity reservoirs is
not.

There is now a sharper selector fence.  By
`separate-packet-calculi-have-no-common-matching`, two separately
authenticated regular finite-packet reservoirs have independent full
multiplicity-unitary gauges.  Every unitary-natural spectral, within-block
Gram, PI, central-polynomial, tensor, or exterior-power construction leaves
those gauges intact.  Its only multiplicity cuts are zero or full, and it
cannot return any nonzero matching between the two reservoirs.  In the
approximate form, a matching of normalized mass `mu` has Haar-averaged
gauge-covariance residual exactly `2mu` while the separate packet defects
remain zero.  Consequently the acquisition record must identify a literal
mixed cross-reservoir operator before invoking a polar or spectral common-cut
step; separate block invariants cannot fill that field.

Only after this artifact exists is it meaningful to compute

```text
rank [C D] - rank D.
```

If the result is three, the established nuisance-quotient theorem supplies
the dimension-free decoder.  If it is below three, the literal channel-minor
route is refuted.  Before acquisition, either numerical result would be a
statement about an invented model rather than the Atlas packet.

## 4. Why no census script was run

The existing programs can safely regenerate word lists and finite quotient
images.  They cannot infer the absent finite-matrix selection/common-corner
map or decide which radical-quotient arrow a path monomial represents.
Encoding either choice inside a script would silently assume
`atlas-hard-packet-authenticates-s4-extension-triple`, the principal open
theorem upstream of the rank calculation.  The conservative outcome of this
audit is therefore the acquisition schema above, not a surrogate matrix.

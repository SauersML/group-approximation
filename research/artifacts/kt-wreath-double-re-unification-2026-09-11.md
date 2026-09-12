# Kun--Thom wreath, double, and relative embeddability: one problem over a (T) base

Date: 2026-09-11. Author lane: `q34-wreath`. This is an assessment and
integration note, not a new proof. Every mathematical input it uses is an
already-established node; the contribution is to record their consequence for
the Kun--Thom pair as graph structure and to state, in one place, what the
whole cluster reduces to.

## The reduction

`binary-free-and-ordinary-coset-wreaths-share-hyperlinearity` is proved for
**every** countable inclusion `C <= A` (route
`tensor-gaussian-binary-wreath-equivalence-proof`). Instantiating at
`(A,C) = (G,Gamma)` for the Kun--Thom Theorem E pair
`Gamma = EL_r(F_q[x_1,...,x_d]) < G = EL_r(F_q[x_1^(±1),...,x_d^(±1)]) rtimes SL_d(Z)`
gives, with no new work:

    W = (+_(G/Gamma) Z/2) rtimes G   hyperlinear
      <=> D = G *_Gamma G            hyperlinear
      <=> L(Gamma) <= L(G)           RE/C
      <=> G *_Gamma (Gamma x Z)      hyperlinear   (centralizer HNN)
      <=> L^oo(R^(G/Gamma),g) rtimes G   Connes embeddable   (Gaussian).

The double-to-`RE/C` half is `kt-q2-double-hyperlinear-iff-relative-embeddable`
for this exact pair. The equivalence is now the node
`kt-wreath-hyperlinear-iff-double-hyperlinear`.

## Why this matters for the program

`W` is the group Kun--Thom prove **nonsofic** (`kun-thom-nonsofic-wreath`,
Theorem A; `kt-pair-group-double-is-nonsofic` for `D`). So `W`/`D` is a fork
machine (`kun-thom-nonsofic-wreath`, downstream note):

- hyperlinear  =>  hyperlinear nonsofic group  =>  Pestov Q3.4 separation
  (`hyperlinear-nonsofic-group`);
- non-hyperlinear  =>  first non-hyperlinear group (`non-hyperlinear-group`).

Both branches are open, and the equivalence shows the wreath lane
(`hyperlinear-wreath-model`, `kt-wreath-relative-canonical-actor-exactification`,
`kt-two-positive-compressors-generate-full-obstruction`) and the double lane
(`hyperlinear-nonsofic-from-kt-reduced-cstar-mf`, `kt-double-reduced-cstar-is-mf`,
`kt-q2-double-reduced-cstar-has-unique-trace`) are attacking one object.

## What the one object is, and why it is hard

`RE/C` of `L(Gamma) <= L(G)` where both groups are **Kazhdan**. This is an
instance of the Gao--Junge open problem: given `M`, `N` Connes embeddable, is
`M *_N M` embeddable? Known when the amalgam base is **hyperfinite**
(Brown--Dykema--Jung, Cor. 4.5); open in general, and here the base `L(Gamma)`
is a property-(T) factor, about as far from hyperfinite as possible. Every
wreath-permanence theorem in the literature -- Hayes--Sale, Gao--Kunnawalkam
Elayavalli--Patchell, Holt--Rees, Alekseev--Bradford -- needs a sofic/permutation
coset action, refuted here by `coordinate-action-not-sofic`; amenable-stabilizer
results fail because the stabilizers are conjugates of the Kazhdan `Gamma`. So
no import resolves it, matching the structural finding of
`notes/HYPERLINEAR_NONSOFIC_ATTEMPT_2026-08-26.md` Section 1: the first
hyperlinear nonsofic group cannot come from a permanence theorem.

## The missing lemma the arithmetic lane already exploits

For the **arithmetic** wreath `W_3 = (+_{Gamma/Lambda} Z/2) rtimes SL_3(Z[1/3])`
the lane runs a second, unconditional constraint:
`coset-wreath-hyperlinearity-forces-strong-one-boundedness`. Its engine is
essential freeness of the coset Bernoulli action
(`coset-bernoulli-action-is-essentially-free`, proved via the Bruhat--Tits
building of `SL_3(Q_3)`), which makes the lamp algebra a Cartan
(`coset-wreath-algebra-has-a-lamp-cartan`) and activates the Jung--Hayes
strong-1-boundedness ceiling: a hyperlinear `W_3` must have a **rigid** matrix
model, no `c d^2` family of non-conjugate microstates.

That discipline does **not** yet apply to the Kun--Thom wreath, because the
essential-freeness input is arithmetic-pair-specific: the building argument has
no home for `EL_r(F_q[x^(±1)]) rtimes SL_d(Z)`. The precise open lemma is now
posed as `kt-coset-bernoulli-essentially-free`. If established, the same
entropy ceiling would bind every hyperlinear model of the Kun--Thom wreath,
turning the moduli of the compression-defect constructions into a second
refutation instrument (a `c d^2` non-conjugate family would prove `W`
non-hyperlinear). The elementary directions look reachable; the `SL_d(Z)`
factor and mixed elements are the open core.

## Bottom line (this lane's view)

The Kun--Thom wreath hyperlinearity question is not a distinct problem from the
double or the HNN group: all four are `RE/C` over a (T) base, a named open
amalgamation problem. The two live routes to a decision are (i) a genuinely new
`RE/C` construction native to the reduced norm, escaping the two-compressor
cocycle of `kt-two-positive-compressors-generate-full-obstruction`, or (ii)
the entropy-ceiling refutation, which first needs
`kt-coset-bernoulli-essentially-free`. No shortcut through existing permanence
theory exists.

# Quantum PCP proof development: integration and analytic-input ledger

Date: 2026-09-20. This is an integrated edition of the user's supplied
“Quantum PCP from Cairn: proof development, strengthened amplification,
and the remaining locality problem.” The new full finite-dimensional proofs
are in [the amplification artifact](qpcp-strengthened-amplification-2026-09-20.md).
Previously established syndrome results are reused through their canonical
proofs below; their stronger hypotheses and counterexamples remain explicit.

**This integration does not establish quantum PCP.** It establishes the
conditional loss threshold `L<(t+1)/2` and an obstruction forcing
`L>=(t+1)/2` for a specified universal private-proof class. The missing
construction is a polynomial-time, normalized, constant-locality reduction
preserving exponentially small YES energy, all-state NO soundness, and
linear per-round description growth. A restricted-domain construction
would also suffice with a QMA-hard seed and proved closure invariant.

## 1. Provenance and trust boundaries

The supplied document reports an audit of `group-approximation-main (1)(1).zip`
with 75,611 entries, 519,310,776 uncompressed bytes and SHA-256
`ea0fa7cbdcdf97212971b1f3c547e304e4eb147d1ccf532fd6528cd077192b40`.
It reports 34,115 parsed graph nodes and a 71-node incoming closure of the
QPCP root under its traversal, supplemented by reverse invalidations,
Library notes, and later artifacts. Those are **provenance claims of the
supplied audit**, not measurements of this live checkout or a claim that
this integration independently read every archive entry.

The supplied Library items are the August 25 syndrome note and Liu's
September 20 manuscript, `nonhyperlinear-groups-exist-2026-09-20.pdf`.
The supplied audit reports reading manuscript pages 1–7, 29–31 and 36–38
and Cairn's analytic reconstruction, not independently reproving the entire
analytic theorem. No unavailable Library file is given an invented local
path. The current integration reads the live canonical nodes and their
written artifacts; archive filenames need not describe the current state.

An `ESTABLISHED` Cairn status means closure of its recorded proof graph,
not human refereeing or Lean verification. In particular, the accepted
September 20 internality chain supersedes stale “under review” headings,
while the stronger one-model normalization remains separate and open.
The new walk and parity proofs do not depend on Liu's theorem at all.
No argument here uses the separate non-MF mechanism arXiv:2608.28772.

## 2. Canonical wiring and proof ledger

| Supplied material | Canonical Cairn integration | Status and boundary |
|---|---|---|
| §§2, 6: normalized walk construction, positive sandwiches, arbitrary entanglement | [Global amplification](../global-walk-linearly-amplifies-hamiltonian-energy.md), [proof route](../global-walk-hamiltonian-amplification-proof.md) | Strengthened in place; all integer `t>=2`, negative transition eigenvalues allowed |
| §7: reciprocal iteration, completeness and linear bit growth | [Conditional root route](../qpcp-from-global-walk-reduction.md), [reducer interface](../global-walk-reducer-has-net-energy-gain.md) | Route proved; reducer OPEN with `L<(t+1)/2` |
| §8: graph parity at every arity and matching private obstruction | [Regular parity family](../regular-graph-parity-has-uniform-single-defects.md), [FCC theorem](../factorwise-complete-composition-returns-the-input-energy.md), [FCC route](../factorwise-complete-composition-returns-the-input-energy-proof.md) | Written proofs; FCC route requires the new parity claim and the stronger amplifier |
| §2.3: rational weights | [Amplification artifact §1](qpcp-strengthened-amplification-2026-09-20.md#1-target-normalization-and-precision), [weighted iteration route](../qpcp-by-dinur-iteration.md) | Final constant-gap rounding replaces unjustified exact denominator clearing; the layered reducer also gains explicit linear bit growth and nondecreasing site count |
| §4: nonhyperlinear consequences | [Liu integration](liu-cairn-integration-2026-09-20.md), §3 below | Analytic and structural group imports stay named |
| §5: trace, state and tensor geometry | [Trace/local-witness claim](../tracial-internality-does-not-supply-local-witness-control.md), [proof](../tracial-local-witness-control-counterexamples.md) | Elementary counterexamples; no blanket impossibility of group methods |
| §9: rounder optimum, positive shift and joint support | [Rounder identity](../combinatorial-gap-and-rounder-give-energy-gap.md), [positive-shift audit](qpcp-positive-shift-audit-2026-09-11.md), [joint-support proof](qpcp-joint-syndrome-support-2026-09-07.md) | Existing proved results, restated in §5 below |
| §10: constant floor does not supply syndrome effects | [Separation claim](../gap-and-floor-do-not-force-compatible-syndrome-effects.md), [proof route](../gap-and-floor-compatible-syndrome-separation-proof.md) | Existing written proof includes graph existence; no efficient graph generator asserted |
| §11: local code tests and auxiliary proofs | [Logical blindness](../correctable-data-tests-are-logically-blind.md), §6 below | Exact fixed-code-space statement, not a general quantum-code no-go |
| §12 and Appendix A: finite checks | [Runnable regression](check-qpcp-strengthened-amplification-2026-09-20.py), [exact replay](qpcp-strengthened-amplification-replay-2026-09-20.json) | Finite regression, separate from universal proofs |
| §13: unfinished compiler | [QPCP root](../quantum-pcp-constant-gap-local-hamiltonian.md) | OPEN; no construction or formal proof of QPCP asserted |

## 3. What nonhyperlinearity adds, with premises retained

Let `M=product_(j->omega)(M_(d_j)(C),tr_(d_j))`, with normalized trace
`tr_d=Tr/d` and the original dimensions fixed. Liu's Theorem 1.2/6.7 says
that for **every** homomorphism `pi:Gamma->U(M)` from a finitely generated
property-(T) group, the entire relative commutant is `[A_j]_omega` for
unital finite-dimensional coordinate subalgebras `A_j`. Chosen lifts need
not be exact representations. Full multiplicity algebras, unequal block
ranks, retained corners, and uniformity over coordinate contractions are
part of the analytic reconstruction, not dispensable technicalities.

The downstream **analytic premise N** is: if `Gamma<=G` are finitely
generated property-(T) groups, `G=<Gamma,u_1,...,u_s>`, and
`u_i Gamma u_i^(-1)<=Gamma`, then every `pi:G->U(M)` has `pi(G)`
normalizing `pi(Gamma)' intersect M`. The accepted route uses **universal
internality for subgroup and ambient representations plus Thom's conditional
normalization theorem**, credited to Andreas Thom by Liu. It does not
assume the stronger one-model statement from just one internal commutant.
See [acceptance and bypass](liu-section-six-acceptance-and-thom-bypass-2026-09-20.md).
Model-dependent expectation averaging, including uniform infinity-to-2 norm
control, does not specify a tensor-site-local implementation or a polynomial
schedule for verifier families.

### The conditional wreath deduction

Let `R_+=F_2[x_1,x_2,x_3]`, let `R` be its Laurent extension, and put
`Gamma=EL_3(R_+)`, `G=EL_3(R) semidirect SL_3(Z)`, with exponent columns
transformed by the integer matrix action. The nonnormal infranormal
Kazhdan-pair property and finite compressor generation are **Kun–Thom
structural inputs**. Set `X=G/Gamma` and `W=(direct_sum_X C_2) semidirect G`.
For `t=(I,I+E_12)` and `gamma_0=(I+x_2 E_12,I)`, the coefficient in
`t^(-1)gamma_0 t` is `x_1^(-1)x_2`, not polynomial. Thus `tGamma` and
`gamma_0 tGamma` are distinct left cosets, and
`b=a_(gamma_0 tGamma) a_(tGamma)` is a specified nonidentity lamp product.

For any `pi:W->U(M)`, let `D=pi(Gamma)' intersect M`. The root lamp has
image in `D`. Premise N on the restriction to `G` puts
`pi(a_(tGamma))=pi(t)pi(a_Gamma)pi(t)^(-1)` in `D` too. It commutes with
`pi(gamma_0)`, whose conjugation moves the lamp to `a_(gamma_0 tGamma)`.
The two lamp images are equal involutions, hence `pi(b)=I`. No injective
tracial ultraproduct representation exists.

Compactness gives a finite-window obstruction uniform over matrix dimension:
otherwise increasingly accurate models on an exhaustion, keeping `b`
separated from identity, would form an ultraproduct homomorphism not killing
`b`. This provides neither an input-dependent QMA encoding nor an effective
polynomial bound for finding such a witness. The [exact radical audit](kun-thom-exact-hyperlinear-radical-2026-09-20.md)
retains one lamp per normal-closure fibre; it does not claim every lamp dies.

### The elementary Leavitt deduction

Let the nonzero binary Leavitt ring over `F_2` have generators `s,a,t,b`
with `ts=ba=1`, `ta=bs=0`, `st+ab=1`. Put `e=1-st=ab`, so
`e^2=e`, `es=te=0`, `ea=a`, `be=b`. Work in
`G_4=EL_4(R)`, `Gamma_3=diag(EL_3(R),1)`.
Their property (T) is imported from the elementary-group theorem for these
finitely generated rings, not an assertion about arbitrary rank-two groups.

With `x_ij(r)=I+rE_ij`, define

```text
u = [ s 0 0 e    ]       u^(-1) = [ t  0   0   0  ]
    [ 0 s 0 et   ]                [ 0  t   0   0  ]
    [ 0 0 s et^2 ]                [ 0  0   t   0  ]
    [ 0 0 0 t^3  ]                [ e  se  s^2e s^3].
```

The inverse identities use `ts=1` and
`e+set+s^2et^2+s^3t^3=1`. For `i=1,2,3`,

```text
u_i=x_(4i)(t-1)x_(i4)(1)x_(4i)(s-1)x_(i4)(-t)
```

has `(i,4)` block `[s,e;0,t]`, and `u=u_3 u_2 u_1`.
This proves elementary membership, not just invertibility.
Conjugation gives `u x_ij(r)u^(-1)=x_ij(srt)` for distinct `i,j<=3`.
Also

```text
k_+=diag(I_3,1+at^3)=[x_41(a),x_14(t^3)],
k_-=diag(I_3,1+s^3b)=[x_41(s^3),x_14(b)].
```

The reversed coefficient products vanish; both elements centralize
`Gamma_3`. Direct multiplication gives
`u k_+ u^(-1)=x_14(a)`, `u k_- u^(-1)=x_41(b)`.
These and `Gamma_3` generate `G_4`, since

```text
[x_21(rb),x_14(a)]=x_24(r),
[x_41(b),x_12(ar)]=x_42(r),
```

and commutation with roots in the first three coordinates gives every
remaining root involving coordinate four. Thus N applies with three
compressors `u,k_+,k_-`.

For any `pi:G_4->U(M)`, normalization of `D=pi(Gamma_3)' intersect M`
puts `pi(x_14(a))` in `D`. Hence
`pi(x_24(a))=pi([x_21(1),x_14(a)])=I`, though `a!=0` since `ba=1`.
This proves nonhyperlinearity. In fact the normal kernel contains
`[x_12(b),x_24(a)]=x_14(1)`; elementary signed permutations give all
coefficient-one roots, and
`[x_(i l)(r),x_(l j)(1)]=x_ij(r)` gives every elementary generator.
Thus **every such homomorphism of G_4 is trivial**.

The four length-two creation words `p_i` in `s,a`, with reversed deletion
words `q_i` in `t,b`, satisfy `q_i p_j=delta_ij` and `sum_i p_i q_i=1`.
The inverse ring maps

```text
(r_ij) -> sum_ij p_i r_ij q_j,     r -> (q_i r p_j)_ij
```

identify `M_4(R)` with `R`, so `G_4` embeds in `R^x`. Hyperlinearity
passes to subgroups, proving the unit group nonhyperlinear. Triviality of
**every** tracial image of the whole unit group additionally needs the
repository's `GL_4(R)=EL_4(R)` identification. It is unnecessary for this
nonhyperlinearity conclusion. See the [direct normalization audit](leavitt-direct-normalization-obstruction-2026-09-20.md)
and the [every-field variant](leavitt-all-fields-normalization-obstruction-2026-09-20.md).

Other integrated consequences retain their additional premises:

| Consequence | Additional input and exact scope |
|---|---|
| [Full-defect rings](full-defect-ring-hyperlinear-radical-audit-2026-09-20.md) | Universal two-copy Cohn algebra, fullness, normal generation and rank descent; tracial collapse in every elementary rank `n>=2`, without property (T) of arbitrary rank-two targets |
| [Binary wreath radical](kun-thom-exact-hyperlinear-radical-2026-09-20.md) | Normal closure and residually finite quotient; fibre-parity kernel, not all lamps |
| [Finitely presented surjunctive double](fp-surjunctive-nonhyperlinear-double-audit-2026-09-20.md) | Rank-six finite presentation and permanence inputs for the same specified double |
| [Torsion-free double](torsion-free-nonhyperlinear-rips-double-2026-09-20.md) | Ollivier–Wise cover, lifted Kazhdan pair, finite presentation and asphericity/dimension inputs; dimension **at most three**, not equality |

These are recorded group consequences, not independently reproved analytic
leaves or ingredients in the walk-amplification proof.

## 4. Why a tracial obstruction does not yet verify a local witness

The elementary [counterexample route](../tracial-local-witness-control-counterexamples.md)
proves the following distinctions in full.

- A rank-one `P_D` has `tr_D(P_D)=1/D`, but a state in its range has
  energy one. Its complement has trace `1-1/D` and ground energy zero.
  On `n` qubits, a negligible tracial corner can contain the whole witness.
- All-state domination `Tr(A rho)<=C Tr(B rho)` is exactly operator order
  `A<=CB`, by testing pure states. Normalized trace control alone is weaker.
- `||X||_(2,rho)^2<=D||rho|| ||X||_(2,D)^2`, because
  `rho<=||rho||I`. For a pure state and its rank-one projection, the
  coefficient `D` is attained. Changing inner products alone does not
  remove this loss.
- CNOT fanout maps `X_1` to `X_1...X_n`. Norms, spectra, traces and
  abstract commutants survive arbitrary unitary conjugation; specified
  tensor support does not.

A fixed nonhyperlinear obstruction also does not encode each verifier.
A reduction must retain a nontriviality/separation mark: relators alone
admit the all-identity representation. It must encode arbitrary QMA
instances efficiently and prove YES completeness and NO soundness for all
states with constant support. Model-dependent expectation schedules and
retained-trace tolerance do not supply those quantitative/geometric data.
These observations identify missing transfer theorems, not an impossibility
of any future group-to-Hamiltonian construction.

## 5. Syndrome exactification and the constant-floor separation

For `H=(1/m)sum_a h_a`, let `K_S=intersection_(a notin S) ker h_a`.
Call `S` feasible if `K_S` is nonzero, let `s_*` be the least feasible
cardinality, and put `beta=s_*/m`. The empty intersection is the whole
nonzero ambient space. A bare `C`-rounder outputs an exact-outside-`S`
state with `E|S|<=C sum_a Tr(h_a rho)` for every input state; no efficiency,
locality or witness-preservation is assumed.

Every occurring label is feasible, so `beta m<=E|S|` gives
`e(H)>=beta/C` for `C>0`. Conversely the exact optimum is zero if
`e(H)=0`, and `C_min=s_*/(m e(H))` otherwise. A ground-state input proves
the lower bound; discarding every input and preparing a fixed vector in a
minimum feasible retained kernel proves equality. Positivity gives a
common zero vector in the zero-energy case. Thus on constant-`beta`
families, a constant-cost unrestricted rounder is equivalent to a constant
NO floor, not to the full QMA promise gap. This is the canonical
[rounder identity](../combinatorial-gap-and-rounder-give-energy-gap.md).

For fixed `nu in (0,1)`, replace `h_a` by `(1-nu)h_a+nu I`. Every term
is invertible with the same support. Only `S=[m]` is feasible; declaring
all terms faulty gives gap one and rounder cost at most `1/nu`. Flags
permanently set to one even give pulled-back effects `I<=h'_a/nu`.
But `e(H')=nu+(1-nu)e(H)` and the promise separation is multiplied by
`1-nu`. This [positive-shift audit](qpcp-positive-shift-audit-2026-09-11.md)
supersedes the August 25 suggestion that bare syndrome rounding is the
sole missing ingredient: a separate YES margin is indispensable.

At positive satisfaction tolerance `eta`, robust combinatorial soundness
already contains energy information. If having term energy at most `eta`
outside `S` forces `|S|>=beta m`, take the terms of energy greater than
`eta` as `S` to get `e(H)>=eta beta`. Conversely, a floor `b>eta`
forces `|S|/m>=(b-eta)/(1-eta)` by summing term energies, bounded above
by one on `S` and by `eta` outside. This is not a free replacement for
ordinary soundness.

Two rank-one qubit projections `P=|0><0|` and
`Q=|v_theta><v_theta|`, `v_theta=(cos(theta),sin(theta))`,
`0<theta<pi/2`, have zero common kernel and exact gap `1/2`.
The eigenvalues of `P+Q` are `1±cos(theta)`, so
`e((P+Q)/2)=(1-cos(theta))/2` and `C_min=1/(1-cos(theta))`.
Tensoring independent pairs preserves the normalized parameters. This
[paired-projector obstruction](qpcp-paired-projector-obstruction-2026-09-07.md)
separates exact combinatorial gap from energy.

A joint POVM `{E_S}` admits an unrestricted outcome-conditioned exactifier
**iff** `E_S=0` for every infeasible `S`. Necessity follows by finding an
input producing any nonzero effect; sufficiency follows by the CP maps
`rho -> Tr(E_S rho) sigma_S`, with a fixed state `sigma_S` in each
feasible kernel. Their sum is trace preserving. Marginals
`F_a=sum_(S containing a) E_S` must satisfy local energy domination
for this **same joint measurement**. On the two-projector example, the
equiprobable labels `{1},{2}` and the equiprobable labels `empty,{1,2}`
have identical `F_1=F_2=I/2`, but only the former is exactifiable.

Every finite joint POVM has a commuting one-bit flag dilation
`W psi=sum_S |S> tensor sqrt(E_S) psi`, with `W*B_aW=F_a`.
This says nothing about locality or efficiency of preparing `W`, which
may involve exponentially many full-space effects. The canonical
[joint-support audit](qpcp-joint-syndrome-support-2026-09-07.md)
keeps the compatibility and implementation obligations separate.

### A constant ordinary floor still does not produce compatible local ports

Suppose joint feasibility holds and
`F_a<=C_0 sum_(b in N(a)) h_b`, with each term in at most `R`
neighborhoods. Every feasible `S` meets a frustrated set `T`, so

```text
I <= sum_(a in T) F_a
  <= C_0 min{|T|,R} sum_(b in union_(a in T)N(a)) h_b.          (LF)
```

The [September 16 proof](gap-floor-syndrome-separation-2026-09-16.md)
constructs, for each `g>=3`, a finite graph of maximum degree 512,
girth above `g`, and at least a tenth of its edges monochromatic under
every two-coloring. Its included probabilistic proof samples
`G(n,64/n)` for `n>=max(100,400*64^(g-1))`. The four failure bounds
are: at most `exp(4)(2/exp(2))^n` for a coloring with at most `8(n-2)`
monochromatic edges; at most `2/(64n)` for at least `64n` edges;
at most `1/4` for at least `4*64^g` short cycles; and at most
`(800/7)(e/8)^512` for high-degree mass at least `0.64n`.
Their sum is below one. Deleting one edge per short cycle and all edges
incident to original degree above 512 removes fewer than `1.28n` edges.
The surviving monochromatic fraction is at least
`(6.72n-16)/(64n)=0.105-0.25/n>1/10`. This is an existence proof,
not a claimed efficient graph generator.

Put equality-bit projectors on its `M` edges. Add `M` disjoint qubits,
each with two terms `P=|1><1|`, `Q_q=ww*`, where
`w=(2q,q^2-1)/(q^2+1)`, `q>=2`, `d_q=q^2+1`.
Their common kernel is zero, their sum has least eigenvalue `2/d_q`,
and `(q,-1)/sqrt(d_q)` has energy `1/d_q` in each term. If `tau>=M/10`
is the minimum monochromatic count, disjoint factors give

```text
s_*=tau+M,  e(H)=(tau+2M/d_q)/(3M),
beta>=11/30,  e(H)>=1/30,  C_min<=11.
```

For each frustrated pair `j`, (LF) gives
`I<=2C_0 sum_(a in U_j)h_a` for its neighborhood union `U_j`.
If `U_j` has at most `g` graph edges, they form a forest. Satisfy these
edges and put every pair in its low-energy vector: (LF) forces
`|U_j|>=d_q/(2C_0)`. Otherwise it has at least `g+1` edges.
Summing over the disjoint pair labels and bounding total neighborhood
incidence by `3MR` gives

```text
min{g+1,d_q/(2C_0)} <= 3R.
```

Choosing integer `g>=max(3,3R)` and `d_q>6C_0R` contradicts this;
`C_0=0` is already impossible. Therefore constant locality, degree,
combinatorial gap, ordinary floor, and bare rounder cost do not force
uniform compatible local effects, even with unrestricted measurement and
dilation. The claimed local amplifier may have extra structure excluding
this family; this does not invalidate its family-specific construction
problem. Fixed finite term-matrix variants remain distinct questions.

## 6. Attempts to complete the missing construction

**Private decoder clocks.** Local propagation constraints can evaluate a
fixed-arity clause, but all clock terms and strengths count in normalized
energy. If independent-block encoding, private proofs, and factorwise
completeness hold, the FCC theorem supplies an actual cheating trial
state and excludes the new threshold. Optimizing weights inside that
class cannot overcome the obstruction. Shared computations need a new
all-state proof.

**Identical witnesses.** Swap invariance implies symmetry, not a tensor
power: `( |00>+|11> )/sqrt(2)` is a symmetric entangled example.
An isometry cloning all pure states would turn an overlap `c` into `c^2`,
contradicting inner-product preservation for distinct nonorthogonal states.
But no-cloning does not obstruct existential tensor-power completeness:
a prover can supply that state. Soundness against arbitrary states is the
issue.

**Good codes and small tests.** If the exact encoding `E` corrects erasure
of every data region read by a test, the Knill–Laflamme condition gives
`E*O E=c_O I` for all operators supported on such a region. Expanding a
test on data plus arbitrary auxiliary register as `g=sum_j O_j tensor B_j`
yields

```text
(E* tensor I) g (E tensor I) = I tensor sum_j c_(O_j) B_j.
```

Thus on that fixed exact code space the test cannot read the logical
witness or its correlations beyond the auxiliary marginal. The
[logical-blindness claim](../correctable-data-tests-are-logically-blind.md)
records this precise restriction. It does not exclude decoding, changing
encodings during a computation, or another interface with proved soundness.

**Checkpoints.** From nonnegative `b_j<=L(e_j+b_(j+1))`, `L>=1`, and a
checkpoint `c` at distance at most `r` with `b_c<=A e_c`, expanding the
recurrence gives
`b_j<=L^r(sum_(s=j)^(c-1) e_s+A e_c)`. This removes a depth-dependent
loss only after a bounded-horizon checkpoint inequality is proved, with
compatible global outcomes. An abstract recovery isometry does not prove
that inequality or its locality. In a space-time Hamiltonian with `D`
comparable layers, one entirely corrupted layer is only a `1/D` fraction
of the constraints. Local repair and amplification of this fraction are
separate requirements.

**Internality checkpoints.** The analytic theorem works in normalized
trace, with model-dependent schedules and gaps depending on retained-trace
tolerance. A checkpoint needs finite, tensor-local implementation and
operator inequalities for every witness state. Section 4 proves why this
requires an additional quantitative transfer theorem.

**Restricted domains.** A QMA-hard seed family closed under the two maps
can avoid the parity inputs used by the universal obstruction. Its invariant,
closure, arbitrary-state energy comparisons and resource bounds must be
proved. No such family/reducer is constructed in the supplied development.

## 7. Integration validation

The [graph validation record](qpcp-integration-validation-2026-09-20.json)
compiles a pinned main snapshot plus these integration nodes with Cairn's
own parser, linter, duplicate detector and status compiler. It explicitly
checks that the root and both reducer claims stay OPEN, the strengthened
walk and FCC statements are ESTABLISHED, and each iteration route retains
exactly its corresponding reducer as its missing prerequisite. Historical
source nodes are read in memory, without restoring or editing files through
Git. Unrelated uncommitted graph edits are outside that pinned validation.
The baseline revision and affected node IDs are recorded for reproducibility.
The exact numerical replay is separate from this graph consistency check.

## 8. Source manifest

The supplied audit's C01–C21 labels map to the following existing sources.
This manifest preserves its source identities and distinguishes Library
provenance from live repository paths.

| Label | Source | Role |
|---|---|---|
| C01 | [QPCP root](../quantum-pcp-constant-gap-local-hamiltonian.md) | Open target |
| C02 | [September 11 walk artifact](qpcp-global-walk-amplification-2026-09-11.md) | Historical weaker estimate and replay; superseded quantitatively |
| C03 | [Net-gain reducer](../global-walk-reducer-has-net-energy-gain.md) | Current strengthened open interface |
| C04 | [FCC claim](../factorwise-complete-composition-returns-the-input-energy.md) | Private composition |
| C05 | [FCC proof](../factorwise-complete-composition-returns-the-input-energy-proof.md) | Fake-data trial state |
| C06 | [Rounder identity](../combinatorial-gap-and-rounder-give-energy-gap.md) | Exact optimum |
| C07 | [Positive shift](qpcp-positive-shift-audit-2026-09-11.md) | Independent YES margin |
| C08 | [Floor/syndrome separation](gap-floor-syndrome-separation-2026-09-16.md) | Local frustration and graph lemma |
| C09 | Library `QPCP_cairn_syndrome_rounding_2026-08-25.md` | Supplied audit's earlier source, corrected by C07; no local-path assertion |
| C10 | [Joint syndrome support](qpcp-joint-syndrome-support-2026-09-07.md) | Feasibility versus marginals |
| C11 | [Fixed-term chain](qpcp-fixed-term-chain-2026-09-07.md) | Different obstruction regime |
| C12 | [Dinur architecture](qpcp-dinur-iteration-architecture-2026-09-11.md) | Layered route; precision correction integrated |
| C13 | [Liu integration](liu-cairn-integration-2026-09-20.md) | Analytic trust ledger |
| C14 | [Acceptance and Thom bypass](liu-section-six-acceptance-and-thom-bypass-2026-09-20.md) | Universal versus one-model normalization |
| C15 | [Leavitt direct normalization](leavitt-direct-normalization-obstruction-2026-09-20.md) | Elementary compression |
| C16 | [Exact wreath radical](kun-thom-exact-hyperlinear-radical-2026-09-20.md) | Fibre parity |
| C17 | [Full-defect audit](full-defect-ring-hyperlinear-radical-audit-2026-09-20.md) | All-rank extension |
| C18 | [Surjunctive double](fp-surjunctive-nonhyperlinear-double-audit-2026-09-20.md) | Same specified example |
| C19 | [Torsion-free double](torsion-free-nonhyperlinear-rips-double-2026-09-20.md) | Extra cover and dimension inputs |
| C20 | [Landscape sources](qpcp-landscape-sources-2026-09-12.md) | Prior source navigation |
| C21 | [Paired projectors](qpcp-paired-projector-obstruction-2026-09-07.md) | Rational near-parallel examples |

Primary references are retained below. The integration re-opened P01, P04,
P05 and P08 and checked P01's Claim 8.1/Lemma 2.9 and P08's Theorem 3.6.
Other source-reading assertions belong to the supplied audit and the linked
Cairn reconstructions; no new complete literature or analytic review is
claimed. These bounded checks cannot certify absence of every announcement.

| Label | Primary source | Boundary relevant here |
|---|---|---|
| P01 | Bergamaschi–Metger–Vidick–Zhang, [Derandomised tensor product gap amplification for quantum Hamiltonians](https://arxiv.org/html/2510.01333v1), 2025-10-01 | Layered derandomized amplification grows locality; also supplies expander and seed inputs |
| P02 | Anshu–Breuckmann–Nguyen, [Circuit-to-Hamiltonian from tensor networks and fault tolerance](https://arxiv.org/abs/2309.16475v2), revision 2024-08-07 | Arbitrary-state adversarial semantics needs energy exponentially small in depth; polynomial-depth combinatorial regime is restricted |
| P03 | Breuckmann–Golowich–Vazirani, [Fault-Tolerant Quantum Computation with Adversarial Errors](https://arxiv.org/abs/2608.16857), 2026-08-17 | Near-linear per-step corruption tolerance is not constant-density soundness for a full static space-time Hamiltonian |
| P04 | Sun–Vidick, [Probabilistically Checking Quantum Proofs, with Interaction](https://arxiv.org/abs/2606.09588), 2026-06-08 | Interactive QMA oracle proofs with polylogarithmic queries, not a static constant-locality reduction |
| P05 | Bafna–Vyas, [Private PCPs from Product Expansion](https://eccc.weizmann.ac.il/report/2026/150/), ECCC TR26-150, 2026-08-19 | Classical NP private PCPs; the unconditional square-root-query construction does not resolve quantum PCP |
| P06 | Anshu–Breuckmann–Nirkhe, [NLTS Hamiltonians from good quantum codes](https://arxiv.org/abs/2206.13228v4), revision 2024-12-05 | Low-energy preparation complexity is not a QMA-hardness reduction |
| P07 | Natarajan–Nirkhe, [The status of the quantum PCP conjecture (games version)](https://arxiv.org/abs/2403.13084), 2024-03-19 | Games/witness distinction and correction of earlier amplification claims |
| P08 | Jeronimo–Mittal–Roy–Wigderson, [Almost Ramanujan Expanders from Arbitrary Expanders via Operator Amplification](https://arxiv.org/html/2209.07024v2), revision 2024-10-22 | Operator-valued walk amplification is prior art |
| P09 | Jihao Liu, [Nonhyperlinear groups exist](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf), supplied Library manuscript dated 2026-09-20 | Universal internality imported analytically; supplied audit could not retrieve this public address and asserts no refereeing or independent public-release verification |
| P10 | Knill–Laflamme, [A Theory of Quantum Error-Correcting Codes](https://arxiv.org/abs/quant-ph/9604034), 1996-04-26 | Exact error-correction condition used for logical blindness |

The final proof state is amplification and obstruction proved, group
consequences conditional on their named analytic/structural imports, and
the constant-locality QMA-hardness reduction **not established**.

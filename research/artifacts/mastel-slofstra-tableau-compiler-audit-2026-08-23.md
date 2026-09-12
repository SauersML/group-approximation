# Mastel--Slofstra tableau compiler audit (2026-08-23)

Source: Kieran Mastel and William Slofstra, *Two Prover Perfect Zero
Knowledge for MIP\**,* STOC 2024, DOI `10.1145/3618260.3649702`, especially
Definitions 8.2--8.3 and Propositions 8.4--8.6 (printed pages 999--1001).

This note audits the `Obl` plus randomizing-tableau construction as a
possible group/monomial compiler.  The distinction between the **one
simulated perfect correlation** and the **full universal BCS algebra** is
load-bearing throughout.

## 1. Exact variable-incidence normal form

For the degree-five obliviation, every Boolean source variable `x` is
replaced by five Boolean shares

```text
x(1),...,x(5),                 product_j x(j)=x.
```

The four fresh masks make any at most four of these shares jointly uniform.
If a source variable occurs in several input contexts, the same five named
shares occur in all of them.

For every input context `i`, the tableau then adds

```text
T_i(p,q) in S5,   p in [4], q in [d_i],
r_i(j,k) in S5,   j in [3], k in [d_i-1].
```

The index `i` is part of every new name.  Hence tableau elements and
randomizers are shared by the subdivided clauses belonging to context `i`,
but never by two different input contexts.  The only cross-input-context
variables are the obliviated Boolean shares (including shares of any
Cook--Levin auxiliary Boolean which was already shared before the tableau
step).  Thus all `S5` gauge data are context-private; the original overlap
problem survives solely as literal equality of shared Boolean shares.

## 2. Clause menu and reversibility

The nontrivial clauses are exactly

```text
(1) T_i(1,q) = pi^(iq)_(x_q),
(2) T_i(p+1,q) = r_i(p,q-1)^(-1) T_i(p,q) r_i(p,q),
(3) product_q T_i(4,q) = sigma_i,
```

plus the trivial pair clauses (4) used to make the final system a genuine
subdivision.

Clauses (2) and (3) are finite `S5` word equations and are Latin/reversible:
after fixing every other group-valued coordinate, any one remaining
coordinate is uniquely determined.  Clause (1) is different.  It is a
two-branch lookup from a Boolean bit to two fixed permutations.  The paper's
definition does not require the two branch permutations to be distinct, and
an arbitrary pair of branch permutations is not a homomorphic encoding of a
Boolean group letter.  Therefore it is not justified to describe the whole
tableau as reversible `S5` word syntax.  The seven-bit encoding of an
`S5`-valued variable also retains the finite local domain restriction to 120
valid codewords.

## 3. What is exactly balanced in the simulated correlation

Proposition 8.6 defines one correlation `p_tab` by a finite sampler.  In the
perfect tracial/commuting realization matching that sampler:

* every exposed obliviated Boolean share is fair, and every set of at most
  four distinct shares is jointly fair;
* the `r_i(j,k)` are independent Haar-uniform elements of `S5`;
* `T_i(1,q)` is equally likely to be the two branch values
  `pi^(iq)_1,pi^(iq)_(-1)` (with coincident values allowed);
* each individual tableau entry in rows 2, 3, and 4 is Haar-uniform on `S5`;
* a type-(3) answer is sampled uniformly on the product fiber by choosing
  `d_i-1` entries freely and solving for the last.

This does **not** say that every local clause-answer PVM is flat on its full
allowed answer set.  For example, a type-(2) clause with `p=1`, viewed by
itself, allows its row-one entry to be any element of `S5`.  In `p_tab` that
entry is supported on only the two program instructions.  Trivial pair
clauses involving row-one entries have the same issue, and repeated reads of
one oblivious bit can be correlated.  Thus the precise conclusion is a
finite, rational, explicitly samplable trace profile, not uniform rank for
all answer projections.

More importantly, even the listed balance properties hold only in the
chosen trace/correlation.  They are not defining relations of the universal
weighted BCS algebra.  Another perfect trace can assign different weights,
and zero-probability allowed answers remain projections in the universal
algebra.

## 4. A fixed rational `C_qc \ C_qa` correlation

Apply the effective transformation

```text
B |-> Tab_sub(Obl(B^3SAT))
```

to the fixed Lin loop BCS `B_loop`.  Proposition 8.4 transports its perfect
commuting strategy.  The same finite classical masks and randomizers used in
the proof of Proposition 8.6 work in a tracial commuting representation, so
the resulting commuting correlation is exactly the simulator table
`p_tab`.  Every entry of that table is rational: it is a finite count divided
by products of `2` and `|S5|=120`.

Proposition 8.5 pulls an `epsilon`-perfect synchronous finite-dimensional
strategy for the tableau game back to a
`poly(K_0,N) epsilon`-perfect strategy for `B_loop`.  Since this is one fixed
finite system, Lin's positive source gap remains a positive output gap.  If
`p_tab` were in `C_qa`, its exact synchrony would give a perfect
Connes-embeddable trace (equivalently, synchronous quantum strategies with
defect tending to zero), contradicting that pulled-back gap.  Consequently

```text
p_tab is rational and synchronous,
p_tab in C_qc,                 p_tab notin C_qa.
```

This is an effective finite table obtained from a syntactically known
infinite-loop program; no undecidable search for an instance is involved.

There is also a harmless **answer-splitting refinement** with exactly uniform
local laws.  Let `L` be a common denominator of all rational marginals and
replace an answer `a` to question `x` by

```text
(a,t),       1 <= t <= L p_tab(a|x),
```

discarding zero-marginal answers.  Each question then has exactly `L`
refined answers.  Tensor the commuting realization with independent finite
classical partitions and split the projection for `a` into
`L p_tab(a|x)` equal-trace pieces.  The refined correlation is rational,
perfect, and has marginal `1/L` on every answer.  Forgetting `t` maps every
strategy back to the tableau game, so membership in `C_qa` would imply
`p_tab in C_qa`.  The refined correlation is therefore still in
`C_qc \ C_qa`.

This refinement is an additional finite construction, not a claim that the
unmodified Proposition 8.6 correlation has flat local answer laws.

## 5. Compiler consequences and remaining walls

The tableau is a genuinely narrower source than a generic BCS:

* all non-Boolean gauge variables are private;
* almost every nontrivial local relation is a reversible finite-group word;
* the cross-context diagram is carried only by shared fair Boolean shares;
* one separated trace has an explicit rational profile, and answer splitting
  can make all its row traces equal.

It nevertheless closes none of the current groupification gates.

1. **Monomial matrix pair.** Equal trace of row projections does not give
   operator column partitions of a square quantum-reflection matrix.  The
   type-(1) lookup and the shared-bit consistency diagram must still be
   packaged into one matrix pair, and every auxiliary block must be proved a
   full corner preserving the entire tracial and `R^omega` representation
   spaces.  Extending only `p_tab` is insufficient.
2. **Projective-kernel phase.** The private `S5` equations have exact
   finite-dimensional permutation models and supply no distinguished
   negative central phase.  They do not couple a marked phase to the source
   violation projections, so they do not prove the decoder required by
   `bcs-projective-kernel-phase-compilation`.
3. **Canonical-profile groupifier.** Rational pair moments give an explicit
   target trace profile and remove a rank-denominator nuisance.  They do not
   manufacture algebraic projections in a group ring, a surviving rational
   mark, or a decoder on arbitrary canonical group microstates.  In
   particular, the shared-bit incidence-cycle holonomy is still an operator
   placement problem, not a probability-balancing problem.

The honest conclusion is therefore a useful structured source and a new
narrow full-corner compiler target, not a completed group compiler.

# Joint syndrome support, exact recovery, and the locality boundary

This continues the quantum PCP audit of 2026-09-07. The results below are
finite-dimensional mathematical proofs. They do not construct a QMA-hard
constant-gap Hamiltonian family. No claim of new dilation theory is made;
the dilation used here is the explicit construction in
[Watrous, The Theory of Quantum Information, Theorem 2.42](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf).

## 1. Exact recovery is a condition on the whole outcome

Fix positive terms `h_1,...,h_m` on a nonzero finite-dimensional space `H`.
A fault set `S` is feasible precisely when

```text
K_S = intersection_(a not in S) ker(h_a) != {0}.
```

The empty intersection, for `S = [m]`, is `H`. Let `F` be the family of
feasible sets. This is an upward-closed family of subsets, not a family of
probabilities or approximate states.

**Theorem 1 (fixed-measurement criterion).** Fix a quantum measurement
instrument with classical outcome `S subset [m]` and input effects `E_S`.
An unrestricted outcome-conditioned CPTP recovery can return a normalized
state on `H` satisfying every term outside `S`, for every input and every
positive-probability outcome, if and only if

```text
E_S = 0       for every S not in F.                         (Support)
```

No efficiency or preservation of input information is asserted.

**Proof.** If `E_S` is a nonzero positive matrix, some unit vector `v` has
`<v,E_S v> > 0`. On input `|v><v|` the outcome has positive probability.
A recovered normalized state exact outside `S` has support in `K_S`:
for positive `h_a,sigma`, zero `Tr(h_a sigma)` implies
`h_a^(1/2) sigma^(1/2) = 0`. Thus `K_S` cannot be zero. This proves
necessity of (Support).

Conversely, for each feasible `S` choose a unit vector `u_S in K_S` and
let `sigma_S = |u_S><u_S|`. After observing `S`, discard the remaining
registers and prepare `sigma_S`. This is a CPTP conditional channel. For
an infeasible label choose any CPTP channel, since that label never occurs.
Every occurring output is exact on the original space `H`, proving
sufficiency. Equivalently the resulting input-to-output instrument has
maps `rho -> Tr(E_S rho) sigma_S`, which are completely positive and whose
traces sum to `Tr(rho)`.

For a proposed syndrome isometry `W` and commuting projections `B_a`, define

```text
Pi_S = product_(a in S) B_a product_(a not in S) (I-B_a),
E_S = W^* Pi_S W.
```

The theorem applies to this **same** `W,B` as the energy estimate. Proving
an estimate for one family and a recovery statement for a different family
does not establish a compatible instrument.

## 2. Commuting one-bit flags can represent any joint POVM

Given any POVM `{E_S}`, put

```text
W v = sum_S |S> tensor sqrt(E_S) v,
B_a = |1><1| on syndrome bit a, tensor identity elsewhere.
```

Orthogonality of the bit strings gives `W^*W = sum_S E_S = I`. The `B_a`
commute and are individually one-qubit observables, and

```text
W^* Pi_S W = E_S,
W^* B_a W = sum_(S containing a) E_S =: F_a.
```

If (Support) holds, Theorem 1 supplies a recovery. Consequently commuting
one-bit flag observables on an unrestricted dilation do not restrict the
possible input POVMs. The physical geometry, circuit resources, preservation
of a specified logical algebra, and energy neighborhoods of `W` must be
controlled separately. No bounded-depth implementation follows from the
square-root formula; it can involve exponentially many full-space effects.

Also, `B_a = 0` and `W v = |0...0> tensor v` satisfy all the individual
domination inequalities at cost zero. On a frustrated Hamiltonian their
only outcome is infeasible, so (Support) fails. Domination alone is not the
syndrome construction needed by the attack.

## 3. Identical marginal costs, opposite recovery verdicts

Take the one-qubit pair `P,Q_N` from the previous paired-projector proof,
with `N > 1`, `d=N^2+1`, and `K=P+Q_N`. It has zero common kernel and
least eigenvalue `2/d`. Thus the feasible labels are
`{P}`, `{Q}`, and `{P,Q}`, while the empty label is infeasible.

Use two syndrome qubits, the same bit-test projectors `B_P,B_Q`, and two
different isometries that leave the data untouched:

```text
W_good v = (|10>+|01>)/sqrt(2) tensor v,
W_bad  v = (|00>+|11>)/sqrt(2) tensor v.
```

Both are implementable by preparing a fixed two-qubit state independently
of the data. Their flag marginals agree exactly:

```text
W_good^* B_P W_good = W_bad^* B_P W_bad = I/2,
W_good^* B_Q W_good = W_bad^* B_Q W_bad = I/2.
```

Their joint input effects differ:

| Fault label | Good effects | Bad effects |
| --- | --- | --- |
| empty | 0 | I/2 |
| {P} | I/2 | 0 |
| {Q} | I/2 | 0 |
| {P,Q} | 0 | I/2 |

The good construction is exactifiable: for label `{P}` prepare `I-Q_N`,
and for label `{Q}` prepare `I-P`. These are normalized one-qubit states
and satisfy the retained term exactly. The bad construction cannot be
exactified, because it outputs the infeasible empty label with probability
`1/2` on every input. This follows directly from Theorem 1.

Nevertheless, both satisfy the same local neighborhood inequalities

```text
F_P <= (d/4) K,        F_Q <= (d/4) K,
E|S| = 1.
```

Indeed `K >= (2/d) I`. Taking both neighborhoods to contain both terms
gives occurrence two and global cost bound `C=d/2`. For the good
construction this is the sharp unrestricted rounder cost. It is not
uniform as `N` grows. The bad construction has exactly the same cost
statistics and even the same marginal covering equality `F_P+F_Q=I`, but
fails exactness.

**Consequence.** Marginal energy estimates, bounded-size syndrome tests,
and non-disturbance of data before recovery cannot certify exactness of
the conditional output. This example does not contradict a theorem that
explicitly assumes (EX); it shows why (EX) must be proved for the entire
joint construction. Even the marginal covering inequalities of the earlier
audit are necessary rather than sufficient.

## 4. Verification and remaining obligation

`python3 scripts/check_qpcp_syndrome_support.py` verifies the two ancilla
states, their bit and joint distributions, the full-space kernel test, the
good recovery states, and the neighborhood domination inequalities using
exact rational arithmetic. The all-input recovery criterion and arbitrary
POVM dilation are proved above, not inferred from finitely many examples.
The saved replay is
`research/artifacts/qpcp-syndrome-support-replay-2026-09-07.json`.

The substantive open construction must provide **one** family of joint
effects with (Support), uniform local energy bounds, and the required
physical realization. Neither the generic dilation nor the two-qubit
example provides that family for an amplified QMA verifier. Quantum PCP
therefore remains open in Cairn.

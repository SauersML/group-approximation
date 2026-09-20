# Quantum PCP: full-target continuation and integrated proof record

Date: 2026-09-20. Integrated from the user's supplied
`QUANTUM_PCP_FULL_TARGET_ATTEMPT.md` text. **No full proof or disproof of
Quantum PCP is obtained.** No locality reducer is constructed, and the
conditional iteration theorem is not promoted to an unconditional theorem.

This artifact contains the continuation's complete mathematical arguments.
Part B of the supplied record is already integrated in the
[strengthened amplification proof](qpcp-strengthened-amplification-2026-09-20.md)
and [proof and analytic-input ledger](qpcp-integration-ledger-2026-09-20.md).
Those maintained proofs, their source manifest, and exact replay are reused
rather than introducing competing theorem nodes. Section 8 maps the
entire supplied record to its canonical locations.

## 1. Target and unresolved construction

For input length \(N\), a classical polynomial-time reduction must output
polynomially many fixed-dimensional qudits and polynomially many terms
with polynomial-bit descriptions:
\[
 H=\frac1m\sum_a h_a,\quad 0\le h_a\le I,\quad
 |\operatorname{supp}(h_a)|\le k.
\]
YES instances require \(e(H)\le a_0\), NO instances \(e(H)\ge b_0\), with
fixed \(k\), local dimension, and thresholds \(b_0-a_0>0\).
The NO bound must hold for **every** state of data and auxiliary registers,
including arbitrary entanglement. YES and NO label input cases; no witness
property can be assumed in a NO-case soundness proof.

The established global tensor walk with \(t\) vertices and nontrivial
transition norm at most \(\lambda\) satisfies
\[
 e(\mathcal G_t(H))\ge
 1-(1-e(H))(1-(1-\lambda)e(H))^{t-1}.
\]
Its terms can touch \(tk\) sites. At \(\lambda\le1/2\), a reducer with
loss \(L<(t+1)/2\), completeness preservation, closure under iteration,
and linear per-round description growth would suffice. See
[the precise open interface](../global-walk-reducer-has-net-energy-gain.md)
and [conditional iteration](../qpcp-from-global-walk-reduction.md).
None of Sections 2–5 constructs it. A different reduction could prove QPCP
without satisfying this universal interface; it is a deficiency of this
strategy, not a characterization of all possible proofs.

## 2. Shared classical records and quantum escape

Let \(X,Z\) be data-qubit Paulis and let \(Q_X,Q_Z\) be Hermitian involutions
on an arbitrary finite-dimensional record. Set
\[
 A=Z\otimes Q_Z,\quad B=X\otimes Q_X,\quad K=I/2-(A+B)/4.
\]
Both \((I-A)/2\) and \((I-B)/2\) are projections; \(K\) is their normalized
average. If the record observables commute, then \(AB=-BA\) and
\((A+B)^2=2I\). Therefore
\[
 e(K)\ge(2-\sqrt2)/4.
\]
This is an operator bound, allowing arbitrary data-record entanglement.
It is sharp: both records can predict the positive outcome, with data a
top eigenvector of \(X+Z\). More generally simultaneous diagonalization of
commuting records gives blocks \(\pm Z\pm X\), each attaining the bound.
A shared classical table of both complementary-basis answers thus has a
fixed disagreement floor and cannot preserve arbitrarily small honest
energy for these checks.

Quantum records escape: on a record qubit choose \(Q_Z=Z,Q_X=X\).
The Bell state \((|00\rangle+|11\rangle)/\sqrt2\) has both correlations
equal to one and zero energy. Record observables anticommute while the
correlation tests commute. This is not a no-go theorem for shared quantum
proofs.

Without commutation, put \(c=\|[Q_Z,Q_X]\|\le2\). Multiplication gives
\[
 (A+B)^2=2I+ZX\otimes[Q_Z,Q_X],\qquad
 e(K)\ge\frac12-\frac14\sqrt{2+c}.
\]
The bound follows by the triangle inequality and self-adjointness of
\(A+B\). If a state has energy at most \(\eta\), \(0\le\eta\le1/2\), then
\(\sqrt{2+c}\ge2-4\eta\ge0\); squaring yields
\[
 c\ge\max\{0,\,2-16\eta+16\eta^2\}.
\]
Accurate coherent records of complementary information must retain
substantial noncommutativity. This tests a proposed static replacement
for two-basis interactive checks, not the interactive theorem itself.
Canonical claim:
[shared-record uncertainty](../shared-records-obey-complementary-check-uncertainty.md).

## 3. Coherent records and local phase checks

### 3.1 Information versus unchanged data-only interference

For normalized auxiliary vectors \(u,v\), define the isometry
\(|0\rangle\mapsto|0\rangle|u\rangle\),
\(|1\rangle\mapsto|1\rangle|v\rangle\).
On encoded \(|+\rangle\), the unchanged data-only check \(K_X=(I-X)/2\)
has energy
\[
 \langle K_X\rangle=(1-\operatorname{Re}\langle u,v\rangle)/2. \tag{C1}
\]
Indeed the two off-diagonal entries of the reduced data state are the
overlap and its conjugate divided by two. Orthogonal records cost \(1/2\)
although the original state had zero energy.

Let \(s\) be half the trace norm of the difference of the pure record
states. Their difference has trace zero and nonzero eigenvalues
\(\pm\sqrt{1-|\langle u,v\rangle|^2}\), by diagonalizing on their span.
Thus
\[
 s=\sqrt{1-|\langle u,v\rangle|^2},\qquad
 \langle K_X\rangle\ge(1-\sqrt{1-s^2})/2.                  \tag{C2}
\]
Energy at most \(\eta\le1/2\) implies \(s\le2\sqrt{\eta(1-\eta)}\).
The bound is sharp for real nonnegative overlap. It concerns a
data-preserving basis record and the **unchanged** data-only phase check;
it does not prohibit an encoded replacement observable.

### 3.2 Exact hypercube identity

For normalized auxiliary vectors \(\phi_x\), \(x\in\{0,1\}^n\), \(n\ge1\),
put
\[
 |\Psi\rangle=2^{-n/2}\sum_x|x\rangle|\phi_x\rangle,\qquad
 H_X=\frac1n\sum_i\frac{I-X_i}{2}.
\]
Then
\[
 \langle\Psi|H_X\otimes I|\Psi\rangle
 =\frac1{4n2^n}\sum_{x,i}\|\phi_x-\phi_{x\oplus e_i}\|^2.  \tag{C3}
\]
**Proof.** The expectation of \(X_i\) is \(2^{-n}\) times the sum of
\(\langle\phi_x,\phi_{x\oplus e_i}\rangle\). Each oriented edge has its
reverse, so the sum is real. Substitute
\(\|\phi_x-\phi_y\|^2=2-2\operatorname{Re}\langle\phi_x,\phi_y\rangle\)
in the energy expression. ∎

For \(\phi_x=|f(x)\rangle\), this is half the fraction of oriented edges
on which the entire proof string changes. Parity has energy \(1/2\);
AND has \(2^{-n}\), since just \(2n\) oriented edges meet the all-ones
string; a constant record has zero. Nonconstant records need not incur
a constant average penalty. The exact identity is the conclusion.
Canonical claim:
[coherent-record phase energy](../coherent-records-have-exact-phase-energy.md).

### 3.3 Restoring phase checks exposes encoded-data locality

Let \(C:\{0,1\}^n\to\{0,1\}^M\) be injective with minimum Hamming distance
\(D\), and encode \(E|x\rangle=|C(x)\rangle\).
Additional auxiliary registers may have arbitrary size and remain fully
quantum. If an operator \(g\) touches at most \(k<D\) encoded-data bits,
even acting on the entire auxiliary register, then for distinct labels
\[
 (\langle C(x)|\otimes I)g(|C(y)\rangle\otimes I)=0.       \tag{C4}
\]
**Proof.** At least one of their more than \(k\) differing positions lies
outside the data support. Its matrix element contributes an orthogonal
one-bit inner product. Linearity proves the same for a sum with different
supports. ∎

Let \(P\) project onto the encoded-data span, tensored with auxiliary
identity. Every such Hamiltonian satisfies
\[
 PKP=\sum_x |C(x)\rangle\langle C(x)|\otimes K_x.          \tag{C5}
\]
Dephasing the logical classical label preserves code-supported energy.
The auxiliary optimization need not be classical. This differs from
[erasure-correctable quantum codes](../correctable-data-tests-are-logically-blind.md):
here diagonal blocks can depend on the label; there the entire compressed
data operator is scalar.

For repetition encoding \(|0\rangle\mapsto|000\rangle\),
\(|1\rangle\mapsto|111\rangle\), no sum of terms touching at most two
data bits distinguishes positive and negative GHZ states. A compressed
operator has zero off-diagonal entry, so its operator-norm error in
approximating logical \((I-X)/2\) is at least \(1/2\): the norm bounds
every matrix element of the difference. \(I/2\) attains that error.
With auxiliary identity in the desired target, the same block argument
gives the same bound.

This is a faithful simulation restriction for this encoding. QPCP asks
for ground-energy hardness, so the result does not disprove general
encodings or ground-energy reductions. Canonical claim:
[distance-code compression](../distance-code-local-tests-are-label-diagonal.md).

### 3.4 Approximate membership

Suppose \(0\le K\le I\) and (C5) holds. If
\(\operatorname{Tr}(P\rho)\ge1-\delta\), \(0\le\delta<1\), there is a
code-supported state \(\sigma\), dephased in the logical label, such that
\[
 |\operatorname{Tr}(K\rho)-\operatorname{Tr}(K\sigma)|
 \le\sqrt\delta.                                         \tag{C6}
\]
**Proof.** Normalize the projection:
\(\rho_P=P\rho P/\operatorname{Tr}(P\rho)\).
Purify \(\rho\) and project its purification. The overlap of original and
normalized projected vectors is \(\sqrt{\operatorname{Tr}(P\rho)}\);
the pure-state projector difference has trace distance
\(\sqrt{1-\operatorname{Tr}(P\rho)}\le\sqrt\delta\).
Partial trace contracts this distance, giving the same bound for
\(\rho,\rho_P\). A trace-zero Hermitian difference has positive and
negative parts with equal trace; testing against an effect \(0\le K\le I\)
changes expectation by at most that trace distance.
Finally dephase \(\rho_P\) to obtain \(\sigma\); (C5) preserves energy. ∎

Small leakage supplies only this controlled error for the tested
classical-code proposal, not a large restored phase signal.
Canonical claim:
[leakage bound](../distance-code-leakage-bounds-phase-energy.md).

## 4. Virtual transitions with a diagonal penalty

Keep the computational-basis code and \(Q=I-P\). Let \(H_{\rm pen}\) be
Hermitian, diagonal in the encoded-data computational label (blocks may
act on auxiliary registers), zero on \(P\), and at least \(\Delta Q\)
on \(Q\), with \(\Delta>0\). Let \(V\) be a sum of Hermitian terms each
changing at most \(k\ge1\) data bits. Set \(v=\|V\|\), the norm of the
**whole** perturbation. For real \(z\) put \(a=\Delta-|z|\) and assume
\(a>v>0\).

Solving the complementary eigenvalue-equation block gives the exact
energy-dependent effective operator
\[
 F(z)=PVP-PVQ[Q(H_{\rm pen}+V-zI)Q]^{-1}QVP.              \tag{V1}
\]
For two codewords at Hamming distance \(d\), let \(r=\lceil d/k\rceil\ge2\).
Their off-diagonal block in \(F(z)\) has norm at most
\[
 \frac{v(v/a)^{r-1}}{1-v/a}.                              \tag{V2}
\]
Every expansion term with fewer than \(r\) perturbation factors is zero
in that block.

**Proof.** The unperturbed complementary resolvent
\(R_0=[Q(H_{\rm pen}-zI)Q]^{-1}\) has norm at most \(1/a\) and preserves
the computational label. Since \(v/a<1\), the inverse in (V1) is the
norm-convergent Neumann series
\[
 \sum_{j\ge0}(-R_0QVQ)^jR_0.
\]
A contribution with \(s\) factors of \(V\) changes at most \(sk\) bits.
Intermediate projections and resolvents preserve the label. Thus it
cannot connect the codewords if \(s<r\), including first-order \(PVP\).
For \(s\ge r\) its norm is at most \(v^s/a^{s-1}\). Summing this
geometric tail proves (V2). ∎

A bound on individual perturbation terms does not replace
\(\Delta-|z|>\|V\|\). Penalties mixing labels and constructions outside
the convergent regime are not excluded and need separate analysis.
This bound alone is not a universal gadget-loss theorem.

### Exact repetition example and coefficient convention

For \(n\) bits use constant-string codewords, unit penalties for adjacent
disagreements, and formal perturbation \(g\sum_i X_i\), evaluating the
unperturbed resolvent at zero. A connecting path must flip all \(n\) bits,
so its first possible order is \(n\). The exact positive path sums for
\(n=2,\ldots,8\) at that order are \(2,4,8,16,32,64,128\).

These are the **unsigned path sums** reported by the supplied code.
For \(V=+g\sum_iX_i\), the coefficient in (V1) includes the sign
\((-1)^{n-1}\) and factor \(g^n\). A common penalty scale \(\Delta\)
also contributes \(\Delta^{-(n-1)}\). This makes explicit the distinction
between positive path sums and signed effective-Hamiltonian coefficients.
Unit perturbation is not asserted to satisfy convergence.
The replay checks lower orders vanish, the displayed sums, and signs;
the general support and norm statements use the proof above.

This tested diagonal-penalty construction supplies no reducer meeting the
required normalized loss. Canonical claim:
[virtual transition bound](../diagonal-penalty-transitions-have-distance-order.md).

## 5. One-copy static channel witnesses

For input and output dimension \(D\ge2\), a unitary \(U\) has normalized
Choi vector \(|J_U\rangle=D^{-1/2}\sum_j|j\rangle\otimes U|j\rangle\).
Every trace-preserving channel's normalized Choi state has input marginal
\(I/D\). Replacing an interactive strategy by an arbitrary state must
enforce this causal normalization, not merely invoke the correspondence.

**Proposition.** For any Hermitian \(K\) on one Choi register, if
\(\langle J_U|K|J_U\rangle\le\eta\) for every unitary \(U\), some
computational-basis product state has energy at most \(\eta\).
Its input marginal is trace distance \(1-1/D\) from \(I/D\).

**Proof.** The \(D^2\) generalized shift-and-phase unitaries have Choi
vectors forming an orthonormal basis, since their inner products are
\(\operatorname{Tr}(U^*V)/D=\delta_{U,V}\). Their projectors average to
\(I/D^2\), so \(\operatorname{Tr}(K)/D^2\le\eta\).
Computational-basis product states average to the same density matrix.
At least one has energy at most that average. Its input marginal is
rank one, whose difference from \(I/D\) has eigenvalues \(1-1/D\) once
and \(-1/D\) with multiplicity \(D-1\); half the trace norm is \(1-1/D\). ∎

If \(K\ge0,\eta=0\), positivity and the complete Choi basis force
\(\operatorname{Tr}(K)=0\), hence \(K=0\).
No locality assumption was made. A fixed auxiliary state independent of
the channel changes nothing: apply the argument to the induced Hermitian
operator on the Choi register.

This excludes a uniform one-copy legality test accepting every unitary.
It does not cover channel-dependent auxiliary proofs, independently
promised copies, or a restricted problem-specific accepted family.
It does not refute the interactive theorem. An arbitrary static state
does not automatically obey an interactive strategy's causal constraints.
Computational cryptographic soundness also does not imply a Hamiltonian
bound against all states: ground states have no computational-time bound.
Canonical claim:
[one-copy legality obstruction](../one-copy-choi-tests-cannot-enforce-channel-legality.md).

## 6. Nonhyperlinear inputs remain separate

Grant the nonhyperlinear consequences and accepted written internality
chain in [the September 20 ledger](liu-cairn-integration-2026-09-20.md),
including its distinction between universal internality plus Thom's
normalization and the stronger per-model statement still under review.
This does not discharge the state-local reduction. For rank-one \(P_D\),
\[
 \operatorname{Tr}(P_D)/D=1/D,\qquad\lambda_{\min}(I-P_D)=0.
\]
A trace-negligible subspace can carry the entire ground-state witness.
Testing every pure state also proves that
\(\operatorname{Tr}(A\rho)\le C\operatorname{Tr}(B\rho)\) for every state
is equivalent to \(A\le CB\).
A local syndrome conversion needs operator order or an appropriate
state-dependent estimate, not trace control alone. The existing
[tracial/witness distinction](../tracial-internality-does-not-supply-local-witness-control.md)
records these proofs, the sharp dimension factor in norm conversion,
and the failure of unitary-invariant data to specify tensor support.
No duplicate nonhyperlinearity theorem or new analytic import is added.

An encoding might bridge this distinction. Sections 2–5 limit tested
constructions, not all constructions. A fixed nonhyperlinear seed is not
an input-dependent polynomial reduction from arbitrary QMA instances.

## 7. Provenance, replay, and source boundaries

The source is the user-supplied conversation text. The sandbox download
link is not a local file imported or hashed in this checkout.
The supplied continuation reports 75,611 archive entries, 455 selected
by filename for access, and roughly 17,500 words in its consolidated file.
It explicitly does not claim all selected entries were read.
Its reported hashes are preserved as provenance, **not recomputed here**:

- Archive, `group-approximation-main (1)(1).zip`:
  `ea0fa7cbdcdf97212971b1f3c547e304e4eb147d1ccf532fd6528cd077192b40`.
- Earlier note, `QUANTUM_PCP_CAIRN_PROOF_DEVELOPMENT.md`:
  `da481e23ffe4aa809f2f5eb5e54e22b5ef2c7324d21baffec219146af072588b`.

Its revisited paths are the QPCP root, Dinur architecture, kernel
resolution, adversarial fault-tolerance source, Pauli-frustration
rounding, and Liu integration artifacts, linked from the existing ledger.
Historical reading claims remain attributed to the supplied record;
this integration does not claim an independent audit of its archive or
Liu's full analytic proof.

Run with Python 3.10+, standard library only:
`python3 research/artifacts/check-qpcp-full-target-continuation-2026-09-20.py`.

The maintained integration check executes all three exact suites (the
September 11 walk replay, the strengthened amplification replay, and this
continuation), compares their JSON receipts, checks links and duplicates,
and verifies the live QPCP proof boundary:
`python3 research/artifacts/check-qpcp-full-target-integration-2026-09-20.py`.
It runs in [the QPCP CI workflow](../../.github/workflows/qpcp-research.yml).
The check reports unrelated full-graph errors separately; its success
certifies the stated QPCP scope, not unrelated research lanes.

The supplied suite checks three shared-record operator cases,
18 coherent-phase cases, 132 encoded-support cases, 40 effects tested
against the respective 4 and 16 unitary Choi states in dimensions 2 and 4,
and seven perturbative-order examples. The integrated suite additionally
checks nonorthogonal and negative-overlap coherent records, the sharp GHZ
compression example, a rational leakage example, and a signed Schur
coefficient in a convergent two-bit example. Arithmetic is exact integers
and fractions. These finite cases are regression evidence; the universal
statements use the written proofs. No code constructs a locality reducer.
See [replay](qpcp-full-target-continuation-replay-2026-09-20.json) and
[graph validation](qpcp-full-target-validation-2026-09-20.json).

Primary pages re-opened on 2026-09-20 for this integration:

| Key | Primary source | Bounded check |
|---|---|---|
| R1 | Bergamaschi–Metger–Vidick–Zhang, [Derandomised tensor product gap amplification for quantum Hamiltonians](https://arxiv.org/html/2510.01333v1), 2025-10-01 | Introduction's locality/gap tradeoff separates amplification from constant-locality composition |
| R2 | Sun–Vidick, [Probabilistically Checking Quantum Proofs, with Interaction](https://arxiv.org/html/2606.09588v1), 2026-06-08 | Theorem 1.1 and Sections 1.2/1.4: interactive QMA protocol, polynomial communication, polylogarithmic queries/rounds, exponentially good completeness, constant soundness; removing interaction requires additional work |
| R3 | Breuckmann–Golowich–Vazirani, [Fault-Tolerant Quantum Computation with Adversarial Errors](https://arxiv.org/abs/2608.16857), 2026-08-17 | Abstract's almost-linear per-step corruption tolerance is not a completed static constant-gap reduction |
| R4 | Bafna–Vyas, [Private PCPs from Product Expansion](https://eccc.weizmann.ac.il/report/2026/150/), 2026-08-19 | Report page concerns classical private proofs, not a coherent quantum reducer |
| R5 | Gharibian–Hecht, [Hardness of approximation for ground state problems](https://arxiv.org/html/2411.04874v2), revision 2026-08-09 | Introduction distinguishes its approximation results from Hamiltonian QPCP |

These checks are not premises for the elementary proofs or an exhaustive
certification of the literature. No historical novelty, independent
referee certification, or formal verification is asserted.

## 8. Complete integration map and proof ledger

| Supplied material | Maintained proof location / graph state |
|---|---|
| A.1, A.8: target and missing construction | Section 1; QPCP root and both reducer obligations remain OPEN |
| A.2: shared records | Section 2; shared-record uncertainty claim and direct proof |
| A.3: coherent records | Section 3; phase identity, label-diagonal compression, and leakage claims |
| A.4: perturbative attempt | Section 4; distance-order claim and signed/unsigned coefficient distinction |
| A.5: static channel attempt | Section 5; one-copy legality claim |
| A.6: group-input boundary | Section 6; existing tracial/witness counterexamples |
| A.7, A.9, A.10: provenance, sources, code | Section 7 and linked script/replay |
| B.1–3: provenance, target, literature | Existing integration ledger Sections 1–2/8 and amplification artifact Section 1 |
| B.4–5: wreath/Leavitt and tracial boundary | Existing ledger Sections 3–4 and canonical group proofs, analytic imports explicit |
| B.6–8: walk, reciprocal iteration, private-proof obstruction | Amplification artifact Sections 2–4 and existing claim/route nodes |
| B.9–10: rounders, shifts, joint feasibility, floor/syndrome separation | Existing ledger Section 5 and complete canonical artifacts, including the graph-existence proof |
| B.11–13: attempts and unfinished theorem | Existing ledger Section 6, Section 1 above, root and reducer attempt sections |
| B Appendix A | Existing strengthened-amplification script and replay |
| B Appendix B | Existing ledger Section 8: C01–C21/P01–P10 and source-review boundaries |

The six continuation claims are established only in their stated scopes.
The leakage route explicitly depends on label-diagonal compression.
Root and reducer attempt sections link these results; none is made a
sufficient premise for QPCP or used to invalidate a valid conditional
iteration route. The locality/completeness/all-state soundness construction
remains missing. **This work does not solve the full Quantum PCP conjecture.**


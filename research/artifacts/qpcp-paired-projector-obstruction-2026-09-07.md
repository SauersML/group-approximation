# Exact rounder obstructions from a pair of qubit projectors

Checked 2026-09-07. These are elementary mathematical proofs and exact
algebraic certificates, not a proof of quantum PCP or a Lean verification.
The contribution to this repository is a sharper test of its proposed
rounder interface. No claim of research novelty is made: the underlying
two-projection spectral geometry is classical (see, for example, the
[Jordan-plane treatment of sums of projections](https://arxiv.org/abs/1811.10518)).

## 1. Conventions

Let `K = sum_a h_a` and `H = K/m`, with `m >= 1` and `0 <= h_a <= I`
on a nonzero finite-dimensional Hilbert space. An exact rounder is a quantum
instrument whose outcomes are a fault set `S` and a normalized state
`sigma_S` satisfying `Tr(h_a sigma_S) = 0` for every `a not in S`.
Its cost is `E|S| <= C Tr(K rho)` on **every** input state `rho`.
No efficiency, locality, or preservation of the input is imposed here.

Write `s*` for the smallest possible fault-set cardinality. The corrected
identity in `combinatorial-gap-and-rounder-give-energy-gap` is

```text
C_min = 0                         if lambda_min(H) = 0,
C_min = s*/(m lambda_min(H))       otherwise.
```

The first case follows because positivity makes a zero-energy ground state
exact for every term. Preparing it with `S = empty` costs zero. For positive
ground energy, the lower bound follows by applying any rounder to a ground
state, and equality is attained by discarding the input and preparing a
state exact off a minimum fault set. Uniform constant cost is equivalent to
a uniform positive energy floor only for families with `s*/m >= beta > 0`.

## 2. A positive-combinatorial-gap family with vanishing energy

For each integer `N >= 1`, let `d = N^2 + 1` and define two one-qubit terms

```text
P = |1><1|,
w = (2N, N^2 - 1)^T / d,
Q_N = w w^*,
H_N = (1/(2N)) sum_(j=1)^N (P_j + Q_(N,j)).
```

Here the subscript `j` means that the matrix acts on qubit `j` and as the
identity on the other qubits. There are `2N` terms, each is 1-local, each
has norm one, and each qubit occurs in exactly two terms. The matrices have
rational entries with `O(log N)` bits; the explicit instance has polynomial
description size. In particular, the example does not obtain its small
energy by multiplying the terms by small scalars.

**Theorem 1.** For this family,

```text
s*(H_N) = N,
combinatorial gap = 1/2,
lambda_min(H_N) = 1/(N^2 + 1),
C_min(H_N) = (N^2 + 1)/2.
```

**Proof of the spectrum.** The identity
`4N^2 + (N^2 - 1)^2 = (N^2 + 1)^2` shows that `w` is a unit vector, so
`Q_N` is an orthogonal rank-one projector. The orthonormal vectors

```text
g = (N, -1)^T / sqrt(d),       f = (1, N)^T / sqrt(d)
```

diagonalize `P + Q_N` with eigenvalues `2/d` and `2N^2/d`, respectively.
For `N >= 1` the first is the smaller one. The `N` site sums commute, and
their joint eigenbasis consists of tensor products of `g` and `f`.
The smallest eigenvalue of their sum is therefore `2N/d`, achieved by
`g` tensor-powered `N` times. Dividing by `2N` gives `1/d`.
This uses a full eigenbasis, so entangled inputs cannot have lower energy.

**Proof of the combinatorial defect.** The two one-qubit kernels have
trivial intersection: `ker P` is spanned by `(1,0)^T`, whose overlap with
`w` is `2N/d != 0`. If a normalized global state exactly satisfied both
terms at some site, its one-qubit reduced density matrix would be supported
in this zero intersection, which is impossible. Here positivity justifies
the support assertion: `Tr(A rho) = 0` for positive `A,rho` implies
`A^(1/2) rho^(1/2) = 0`. Thus every feasible fault set removes at least one
term at each site, even when the output is entangled or mixed, giving
`|S| >= N`. Removing all the `Q` terms and preparing `|0>` on every qubit
achieves equality. Hence `s* = N`.

**Proof of the sharp cost.** Every nonzero-probability output of a rounder
has at least `N` faults. On the ground state its input total energy is
`2N/d`, hence `N <= C (2N/d)` and `C >= d/2`. Conversely, the constant
instrument just described always costs `N`; on any input
`Tr(K rho) >= 2N/d`, so `C = d/2` suffices. This proves all four formulas.

**Scope.** Positive constant combinatorial gap, constant qudit dimension,
bounded occurrence, and projector terms are insufficient to imply a
constant-cost rounder. No endpoint-faithfulness assumption is needed.
This is not a counterexample to QPCP: the displayed family is easy to solve,
and QPCP asks for a hard family produced by an appropriate reduction. The
matrices `Q_N` vary with `N`; this example does not rule out a construction
using a fixed finite collection of suitably conditioned gadgets.

## 3. Exactification imposes covering inequalities on flag effects

For an arbitrary instrument, let `E_S` be its input POVM effect for the
classical label `S`, and put `F_a = sum_(S containing a) E_S`.
Then `0 <= F_a <= I`; `F_a` gives the probability of flagging term `a`.

**Lemma.** If a set `T` of terms has no common zero-energy state, then any
exactifier satisfies

```text
sum_(a in T) F_a >= I.                                      (Cover)
```

**Proof.** An outcome with `S` disjoint from `T` would have to prepare a
normalized state satisfying every term in `T`, which is impossible. It
therefore has probability zero on every input, and its positive effect
`E_S` is zero. All remaining labels have `|S intersection T| >= 1`, so

```text
sum_(a in T) F_a
  = sum_S |S intersection T| E_S
  >= sum_S E_S = I.
```

The conclusion holds independently of how the instrument measures, and
includes coherent ancillas, joint commuting flags, and arbitrary recovery.
For each incompatible pair in Theorem 1 it gives `F_(j,P) + F_(j,Q) >= I`.

## 4. Charging each flag only to its own term is impossible

**Theorem 2.** Take `N > 1` and the single-qubit pair `P,Q_N`. There is no
exactifier whose marginal effects obey

```text
F_P <= c_P P,       F_Q <= c_Q Q_N
```

for finite nonnegative constants `c_P,c_Q`. This remains impossible on any
finite-dimensional spectator extension, with `P,Q_N` tensored by identity.

**Proof.** If `0 <= F <= I` and `F <= c P` for an orthogonal projection
`P`, every vector in `ker P` has zero `F`-quadratic form. Positivity gives
`ker P subset ker F`, whence `F = P F P <= P`. The two proposed
inequalities therefore force

```text
F_P + F_Q <= P + Q_N.
```

But exactification and the zero common kernel give `F_P + F_Q >= I` by
(Cover). Combining them would give `I <= P + Q_N`, contradicted by its
ground eigenvalue `2/(N^2 + 1) < 1`. Tensoring a ground vector with any
spectator vector proves the same contradiction on an extension. This proof
does not assume the effects themselves commute.

For Cairn's isometry and commuting syndrome projectors, the marginal effects
are exactly `F_a = W^* B_a W`, and they are positive contractions. Thus
using `N(a) = {a}` in local syndrome domination cannot work even on this
two-term instance. This does **not** invalidate domination by a larger
neighborhood, which is what the actual open port claim allows. Mixing both
terms removes the kernel obstruction; it still pays the small spectral
scale in Theorem 1.

## 5. Reproducible verification boundary

Run `python3 scripts/check_qpcp_rounding.py` from the repository root.
The dependency-free checker expands the cleared-denominator identities as
integer polynomials. Equality of their coefficient lists verifies identities
for every parameter, not just selected values. The mathematical arguments
above supply the domain `N >= 1`, eigenvalue ordering, tensorization,
instrument positivity, and the all-size combinatorial proof.

As a separate finite regression, the checker uses rational row reduction
on the full tensor-product matrices and exhausts **all** fault sets for
`N = 1,2,3`. It also checks several exact ground energies and the zero-energy
rounder case. The finite enumeration is not claimed to exhaust larger
instances or to certify QMA-hardness. The saved JSON gives its exact scope.

`scripts/check_qpcp_rounding.wl` supplies the corresponding Wolfram Language
identities. Both Wolfram plugin calls attempted in this session failed with
HTTP 404 at the service endpoint, and no local Wolfram executable was
available. The Wolfram file is consequently **unexecuted**, not independent
Wolfram verification. No Lean toolchain was available and no Lean proof is
claimed. Cairn checks the graph's structure and dependencies; its derived
`ESTABLISHED` status is not a proof-assistant judgment.

## 6. Consequences for the QPCP attack

The graph continues to leave these substantive obligations open:

| Obligation | Why these results do not supply it |
| --- | --- |
| Polynomial-time hardness reduction with constant combinatorial gap, locality, and local dimension | The example is an easily diagonalized family, not a reduction. |
| YES energy below the NO floor | No completeness-preserving amplifier is constructed. |
| Uniform local syndrome domination | Single-term neighborhoods are obstructed; larger neighborhoods still need an actual construction and uniform bounds. |
| Syndrome-conditioned exactification for that construction | The abstract covering condition is necessary, not a recovery construction. |

The 2026-09-07 source check found the open status stated in
[Bafna--Vyas, ECCC TR26-150](https://eccc.weizmann.ac.il/report/2026/150/).
The [FOCS 2026 list](https://focs.computer.org/2026/accepted-papers/) confirms
the Bafna--Nguyen--Zhang authorship of the combinatorial amplification work;
its full iterated parameters were not obtained in this session. The
[2025 derandomized tensor-product amplification paper](https://arxiv.org/abs/2510.01333)
explicitly retains a locality increase. None of these sources, and none of
the calculations here, resolves constant-locality quantum PCP.

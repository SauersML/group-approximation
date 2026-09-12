# Normalization and backward supports bound faithful tensor-OR reduction

Date: 2026-09-12. Status: elementary proof, not Lean-verified. No claim
to priority is made. This is a constraint on a specified simulation
architecture, not a disproof of quantum PCP or its general reducer.

## 1. The bound with ancillas and encoding

Write `Omega=|0^t>` and `e_j=X_j Omega` for the `t` orthonormal
one-excitation vectors. A fixed ancilla vector `a` may be arbitrarily
entangled among its own qubits. It is independent of the data input.
Let `V psi=U(psi tensor a)`, where `U` has depth `D` and each layer
consists of disjoint gates of arity at most `b`. Gates can act anywhere.

Let `K=sum_i p_i k_i` be a convex combination of positive contractions
supported on at most `k` physical qubits each. Conjugating `k_i` backward
through one circuit layer multiplies its support bound by at most `b`.
Thus `B_i=U* k_i U` has support on at most `k b^D` input qubits, of which
at most `q=min{t,k b^D}` belong to the data. Call that data subset `S_i`.
This support statement concerns operators; it does not assume that the
ancilla state is a product.

Put `a_i=<Omega tensor a,B_i(Omega tensor a)>`. Then `0<=a_i<=1`,
and `eta=sum_i p_i a_i` is the encoded vacuum energy. For `j` outside
`S_i`, `B_i` commutes with `X_j`, so

```text
<e_j tensor a,B_i(e_j tensor a)>=a_i.
```

For `j` in `S_i` that expectation is at most one. Therefore

```text
(1/t) sum_j <V e_j,k_i V e_j>
 <= (1-|S_i|/t)a_i+|S_i|/t
 <= a_i+q/t.
```

Multiply by `p_i` and sum. The weights sum to one, giving

```text
(1/t) sum_j <V e_j,K V e_j> <= eta+q/t.                 (1)
```

If `V*KV >= P_t/L-delta I`, where `P_t=I-|Omega><Omega|`, every
summand on the left of (1) is at least `1/L-delta`. Consequently

```text
1/L <= eta+delta+min{1,k b^D/t}.                        (2)
```

This uses only diagonal matrix elements of the operator inequality;
off-diagonal simulator terms and noncommuting interactions cannot avoid it.
Adding arbitrarily many ancillas cannot change the support count.

For fixed `k,b,D` and `eta+delta=o(1/t)`, multiplying (2) by `t`
gives `t/L<=k b^D+o(1)`, so `L` cannot be `o(t)`. In the exact case,
when `k b^D<t`, `L>=t/(k b^D)`. More generally (2) implies the
depth restriction `b^D >= (t/k)(1/L-eta-delta)` whenever its right
side is positive and greater than one.

## 2. Sharpness without encoding

For `1<=k<=t`, define

```text
K_(t,k) = (1/binomial(t,k)) sum_(S subset [t], |S|=k)
            (I_S-|0^S><0^S|) tensor I_(S complement).
```

Every summand is a `k`-local projection. A computational basis string
of weight `r` is accepted (zero penalty) by precisely those subsets
avoiding its `r` nonzero coordinates, so its eigenvalue is

```text
lambda_r = 1-binomial(t-r,k)/binomial(t,k).
```

Use zero for the numerator if `t-r<k`. The eigenvalue is zero at
`r=0`; for `r>=1` it is increasing in `r` and its minimum is
`lambda_1=k/t`. Thus

```text
(k/t)P_t <= K_(t,k) <= P_t.
```

The loss `L=t/k` is attained, exactly matching (2) with `D=0` and
`eta=delta=0`. At fixed `k` the list of all subsets has polynomial
size, so sharpness is also an explicit finite construction.

## 3. Consequence and limitation for the active reducer

A tensor-walk amplified clause has the form `I-tensor_j(I-h_j)`.
Taking every factor `h_j=|1><1|` gives precisely `P_t`. Any uniform
clausewise implementation that promises statewise domination on its
encoded data sector and preserves the encoded vacuum must pass (2).
This includes fixed ancillas, shallow local encodings, arbitrary bounded
local terms, and arbitrary normalized nonnegative weights. In this
architecture, fixed locality and fixed encoding depth require linear
loss in `t`; they cannot supply the family `L_t=o(t)` discussed in
`global-walk-reducer-has-net-energy-gain`.

That claim, however, asks for ground-energy inequalities on complete
instances. It does not promise a statewise simulation, a fixed encoding,
or an independent transformation for each clause. On the one-clause
frustration-free example both required ground energies can be zero, so
the general reducer has no obligation to preserve excitation energies.
The theorem therefore does not refute the claim. A collective reduction,
a sufficiently delocalized encoding, or a reduction controlling only
the minimum energy remains outside this argument.

The weight normalization is essential. With unnormalized sums one can
multiply all terms by an arbitrary factor; (1) would then contain their
total weight. Reporting that rescaling as normalized gap gain would be
incorrect.

## 4. External check and provenance

Primary sources checked on 2026-09-12:

- [Bergamaschi--Metger--Vidick--Zhang, arXiv:2510.01333](https://arxiv.org/abs/2510.01333)
  places tensor-product amplification in the quantum-PCP program. Its
  amplification statement does not itself provide the needed locality
  reduction.
- [Aharonov--Zhou, Hamiltonian Sparsification and Gap-Simulation, ITCS 2019](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITCS.2019.2)
  studies obstructions to degree reduction and dilution under simulation
  requirements. It is relevant prior art for distinguishing simulation
  from an unrestricted complexity reduction; (1)--(2) above are proved
  directly and do not invoke its no-go theorems.
- [Nguyen, Simons workshop abstract, 2026-07-23](https://simons.berkeley.edu/talks/quynh-t-nguyen-harvard-university-2026-07-23)
  describes the still-open locality-preserving quantum gap-amplification
  program and a combinatorial-soundness template. This result is only
  an obstruction for the narrower statewise architecture defined here.

Repository searches for tensor OR, single-excitation, local simulation,
and backward support did not find this exact bound already encoded.
The literature search was bounded and is not an originality certificate.
No computational search is used as proof of the universal theorem.

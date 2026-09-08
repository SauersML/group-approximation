# A fixed-term chain obstruction to bounded-neighborhood exactification

This note tests the proposed kernel-resolution construction. It proves an
explicit obstruction even for a fixed finite collection of qubit projectors,
and gives a direct dual certificate. It does not prove or disprove quantum
PCP: the chain below has combinatorial gap `1/(n+1)`, which tends to zero,
and no QMA-hardness reduction is provided.

The ferromagnetic spin-chain setting and its gapless behavior are classical;
see [Koma and Nachtergaele, *The spectral gap of the ferromagnetic XXZ
chain*](https://arxiv.org/abs/cond-mat/9512120). Their boundary conventions
are not imported here. All bounds for the particular endpoint penalties
below are proved directly. No novelty claim is made for the spin model,
the permutation argument, or the standard variational method.

## 1. A direct range-cover certificate

Let positive terms `h_a` on a nonzero `D`-dimensional space have no common
kernel. Fix energy neighborhoods, let `A_a` be their sums, and let `P_a`
project onto `ran A_a`. Suppose a density matrix `rho` obeys

```text
eta = 1 - sum_a Tr(P_a rho) > 0.                              (Cover)
```

**Lemma 1.** No exactifying instrument can have marginal effects
`F_a <= C_0 A_a` for any finite `C_0`.

**First proof.** Finite domination implies `ran F_a subset ran A_a`.
Since a marginal effect is a positive contraction, `F_a<=P_a`. Exact
recovery cannot output the empty fault set on this frustrated instance.
Consequently `sum_a F_a >= I`, since every occurring label has cardinality
at least one. Evaluating in `rho` contradicts (Cover).

Here is also a full explicit certificate in the earlier SDP's dual format:

```text
Y_0 = rho - sum_a P_a rho P_a,
epsilon = eta/(2D),
Y = Y_0 - epsilon I,
t = 2 + 8D/eta,
X_a = t(I-P_a).                                               (Certificate)
```

Then `X_a>=0`, `Tr(Y)=eta/2>0`, and `Tr(X_a A_a)=0`.
For every `a`, compression of `Y_0` to `ran P_a` is nonpositive: the
summand `P_a rho P_a` cancels the compression of `rho`, leaving negative
compressions of the other positive summands. Thus that compression of
`Y` is at most `-epsilon I`.

Also `-sum_a P_a rho P_a <= Y_0 <= rho`. The positive matrix in the left
bound has trace `1-eta<1`, and `rho` has norm at most one. Hence
`||Y_0||<=1` and `||Y||<=1+epsilon<=2`. For `u in ran P_a` and
`v in ker P_a`,

```text
<u+v,(X_a-Y)(u+v)>
 >= epsilon ||u||^2 - 4||u||||v|| + (t-2)||v||^2
 >= (t-2-4/epsilon)||v||^2 = 0.
```

So `X_a>=Y` for every `a`. Every feasible fault label is nonempty;
choosing any one of its indices and adding the remaining positive `X_a`
gives `sum_(a in S) X_a>=Y`. This is a zero-denominator dual certificate,
with no optimizer or separation oracle required.

## 2. One fixed collection of local matrices

For `n>=2`, on a path of `n` qubits, put

```text
K_n = |1><1|_1 + sum_(i=1)^(n-1) e_i + |0><0|_n,
e_i = |singlet><singlet|_(i,i+1) = (I-SWAP_(i,i+1))/2,
|singlet> = (|01>-|10>)/sqrt(2).
```

There are `m=n+1` norm-one projector terms, locality at most two, and at
most two terms incident to each qubit. Their local matrices have entries
in `{0,1,-1/2,1/2}` and are drawn from a fixed finite collection.

**Frustration and exact fault sets.** The common kernel of all the `e_i`
is the fully symmetric subspace, since adjacent swaps generate every
permutation. The left penalty restricts such a vector to `|0...0>`:
permutation symmetry transports the zero `|1><1|_1` expectation to every
site. The right penalty excludes that vector. Thus `ker K_n={0}`.

Removing either endpoint penalty gives the all-zero or all-one state.
Removing edge `i` gives the product state with sites `1,...,i` zero and
sites `i+1,...,n` one. Thus every nonempty fault set is feasible, and the
minimum fault cardinality is exactly one. The normalized Hamiltonian
`H_n=K_n/(n+1)` has combinatorial gap exactly `1/(n+1)`.

**An exact product-state variational bound.** Set `T=n-1` and for
`j=0,...,T` define

```text
b_j=(T-j,j)^T,       d_j=(T-j)^2+j^2,
rho_j=b_j b_j^*/d_j,       rho= tensor_(j=0)^T rho_j.
```

These are rational pure-state density matrices. Both endpoint penalties
have zero expectation. The determinant of `b_j,b_(j+1)` is `T`, so

```text
Tr(e_(j+1) rho) = T^2/(2 d_j d_(j+1)) <= 2/T^2,
Tr(K_n rho) <= 2/(n-1),                                      (Energy)
```

where `d_j>=T^2/2` follows from `2d_j-T^2=(T-2j)^2>=0`.

## 3. Every bounded term subset has an explicit positive spectral bound

Fix an integer `L>=1` and assume `n+1>L`. For *any* subset of at most `L`
terms, let `A` be its sum and `P` its range projection. We claim

```text
A >= delta_L P,           delta_L=1/[8(L+1)^4].               (Local)
```

The subset may be spatially disconnected. Its selected edges decompose
into path components, each with `r<=L+1` sites. No component contains both
endpoint penalties: that would require selecting all `n+1` terms. It
therefore suffices to treat an unpinned component and a component with one
endpoint penalty. Different components act on different tensor factors.

**Unpinned component.** For `r>=2`, write `E=sum_i <v,e_i v>` and let
`Q_sym` be the symmetric-subspace projection. Every permutation is a word
of length at most `ell=r(r-1)/2` in adjacent swaps. Telescoping the word
and applying Cauchy--Schwarz gives

```text
||(I-U_pi)v||^2 <= ell^2 sum_i ||(I-SWAP_i)v||^2
                = 4 ell^2 E.
```

The repeated occurrence of an edge in a word is included in this bound.
Averaging all permutations yields

```text
||(I-Q_sym)v||^2 = (1/2) average_pi ||(I-U_pi)v||^2
                 <= 2 ell^2 E.
```

Thus the positive spectrum is at least `1/(2 ell^2)`, which is larger than
`1/(8r^4)`. For `r=1` the unpinned operator and its range projection are
both zero, so the asserted inequality is vacuous.

**One pinned endpoint.** Let the field penalize `|1>` at the first site;
the other cases follow by reflection or flipping all bits. Write `B` for
the field expectation and `E` for the edge energy. Transporting that field
to site `j` uses `j-1` adjacent swaps, each at most once. Telescoping gives

```text
||(|1><1|_j)v|| <= sqrt(B)+2 sqrt((j-1)E).
```

The projections onto the individual bad bits satisfy
`I-|0...0><0...0| <= sum_j |1><1|_j`. Squaring the displayed norm bound
and summing therefore gives

```text
||(I-|0...0><0...0|)v||^2 <= 2r B+8r(r-1)E
                         <= 8r^2(B+E).
```

This proves a positive spectral bound `1/(8r^2)`. The common kernel is
exactly `span{|0...0>}`, by the same permutation argument as above.

**Combine components.** Each component operator is positive. The spectrum
of their tensor sum consists of sums of component eigenvalues; the least
nonzero sum is at least the least component bound. Spectator identities
do not change this. Since every component has `r<=L+1`, (Local) follows,
including the empty subset, where `A=P=0`.

## 4. A universal bounded-neighborhood obstruction

**Theorem 2.** Fix integers `L,R>=1`. If

```text
n > 1+16R(L+1)^4,                                             (Threshold)
```

then **no** choice of one energy neighborhood per term, each containing
at most `L` terms and with each term occurring in at most `R` neighborhoods,
admits an exactifying instrument satisfying `F_a<=C_0 A_a` for any finite
`C_0`. The neighborhoods may be nongeometric, and the measurement and
recovery may be arbitrary global channels.

**Proof.** For the rational product state above, (Local), occurrence, and
(Energy) give

```text
sum_a Tr(P_a rho)
 <= delta_L^(-1) sum_a Tr(A_a rho)
 <= (R/delta_L) Tr(K_n rho)
 <= 16R(L+1)^4/(n-1) < 1.
```

The instance is frustrated, so Lemma 1 applies. Its displayed formulas
give an explicit dual certificate for each neighborhood choice. The range
projectors themselves are exact: the kernel projection of a subset is
the tensor product of symmetric-subspace projections on unpinned
components and all-zero/all-one projections on pinned components.

All these projectors are rational. On an unpinned `r`-site component,
the symmetric projection has matrix entry `1/binomial(r,k)` when both
bit strings have weight `k`, and zero otherwise. Thus the certificate can
be specified by exact local matrices and tensor products even when the
global dimension is large. No dense polynomial-size matrix encoding of
the full `2^n`-dimensional certificate is claimed.

## 5. What this resolves and what it leaves open

This proves that a fixed finite term collection, uniform local positive
spectra, and bounded occurrence **do not** supply a kernel resolution.
It closes that generic inference. The conditional theorem requiring a
resolution remains valid, and an amplifier might have additional global
structure that supplies one.

The counterexample has vanishing combinatorial gap. It does not refute a
construction specifically for constant-combinatorial-gap NO outputs, nor
either of the QPCP construction claims. A polynomial-time amplifier with
constant locality and dimension, a constant combinatorial gap, and the
required YES margin is still missing. Quantum PCP remains OPEN in Cairn.

The script `scripts/check_qpcp_chain_obstruction.py` verifies exact local
kernels and spectral inequalities for every tested small subset, direct
dual certificates for small chains, and the rational threshold arithmetic.
The proofs above, rather than extrapolation of these finite checks, establish
the all-size statements. Wolfram returned a service `404` during this audit;
no Wolfram or Lean verification is claimed.

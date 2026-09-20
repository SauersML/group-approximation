# Quantum PCP from Cairn: strengthened amplification and the remaining locality problem

Date: 2026-09-20. Integrated from the user's supplied proof-development and
source audit of this date. Ordinary mathematical proofs and exact finite
regressions; no Lean, external-refereeing, or historical-priority claim.

**Quantum PCP remains open in this development.** The new completed results
are a sharper global tensor-walk estimate, a conditional iteration theorem
with reducer loss `L<(t+1)/2`, and a private-composition obstruction reaching
that threshold at every fixed locality. No locality reducer is constructed.
The accompanying [integration ledger](qpcp-integration-ledger-2026-09-20.md)
connects the supplied document's other arguments to their canonical Cairn
claims, analytic imports, literature, and unresolved interfaces.

The subsequent [full-target continuation](qpcp-full-target-continuation-2026-09-20.md)
tests shared records, coherent encodings, virtual transitions and static
channel proofs. It preserves this theorem and its conditional status;
none of those attempts constructs the reducer.

## 1. Target, normalization and precision

Write `H=(1/m)sum_a h_a`, `0<=h_a<=I`, and `e(H)=lambda_min(H)`.
The target is a deterministic polynomial-time reduction from each QMA
problem to constant-locality, constant-dimension Hamiltonians, with
polynomially many terms and polynomial-bit descriptions, distinguishing
`e(H)<=a` from `e(H)>=b` for fixed `b-a>0`. A spectral gap of one Hamiltonian,
a tracial conjugation gap, and this promise gap are different quantities.

Equal repetition of every term leaves `H` unchanged. Scaling an unnormalized
sum provides no gain after accounting for local strength and total weight.
For a weighted intermediate `sum_a p_a h_a`, polynomial-bit rational weights
do not ensure a polynomial common denominator. Instead choose an integer
`D`, round down `D p_a`, and distribute the remaining units among the largest
fractional parts. The integers `q_a` sum to `D` and

```text
|p_a-q_a/D| <= 1/D,
||sum_a (p_a-q_a/D)h_a|| <= m/D.
```

At a final constant gap `gamma`, take `D>=8m/gamma`. Each ground-energy
threshold changes by at most `gamma/8`, and repeating term `a` exactly `q_a`
times uses polynomial size. This corrects unrestricted exact-denominator
clearing. The global labelled-walk construction below is already uniform.

The external inputs for the conditional hardness theorem are the standard
exponentially complete 5-local QMA seed, with YES energy at most `2^(-N)`
and NO energy at least `1/q(N)` for a fixed polynomial, and deterministic
fixed-degree two-sided spectral expanders for every sufficiently large term
count. See [BMVZ, Claim 8.1 and Lemma 2.9](https://arxiv.org/html/2510.01333v1).
Normalizing a polynomial term count retains an inverse-polynomial NO bound;
QMA witness amplification supplies the requested exponentially small YES
bound. Fixed powering lowers the expander's nontrivial transition norm to
`1/2`; equal repetition handles finitely many small term counts.

## 2. Global tensor-walk amplification

Let `K` be a nonzero finite-dimensional Hilbert space and `Q_v=I-h_v`.
Let `M` be real symmetric, nonnegative and stochastic, the transition matrix
of a regular undirected multigraph on the `m` term labels. With uniform unit
vector `u`, assume `||M-uu*||<=lambda<1`. A stationary walk contains **t
vertices and t-1 edges**, for any integer `t>=2`. Define

```text
A_t = E_(v_1,...,v_t) Q_(v_1) tensor ... tensor Q_(v_t),
G_t(H) = I-A_t.
```

The factors act on distinct copies. Both `A_t` and `G_t(H)` are positive
contractions. With a `d`-regular walk graph there are `m d^(t-1)` equally
weighted labelled walks, including parallel-edge multiplicities. Locality
is at most `tk`, site count is `tn`, and local dimension is unchanged.
Projective input terms give projective rejection terms.

**Theorem (positive-sandwich bound).** For `epsilon=e(H)`,

```text
1-(1-epsilon)(1-(1-lambda)epsilon)^(t-1)
    <= e(G_t(H)) <= min{1,t epsilon}.                         (PS1)
```

This includes arbitrary entanglement among copies, odd walk lengths, and
transition matrices with negative eigenvalues.

### Transfer identity

On `L=C^m tensor K^(tensor t)`, put

```text
U psi = u tensor psi,  P=UU*,  T=M tensor I,
D_j = sum_v |v><v| tensor Q_v^(j).
```

Expanding label matrix entries gives the exact operator identity

```text
A_t = U*D_1 T D_2 T ... T D_t U.                              (PS2)
```

The coefficient of a path is `M_(v_1,v_2)...M_(v_(t-1),v_t)/m`;
operators on distinct copies multiply to its tensor acceptance term.
No product-state assumption enters this identity.

### Positive sandwiches and endpoints

Write `a=1-epsilon`, `c=lambda+(1-lambda)a`. Positivity gives

```text
0 <= U*D_j U = (I-H)^(j) <= a I,
U*D_j^2 U <= U*D_j U <= a I.
```

Let `V=|T|^(1/2)` and `J=sign(T)`, with sign zero equal to zero. Then
`T=VJV`, `||J||<=1`, and

```text
|T| <= lambda I+(1-lambda)P.                                 (PS3)
```

Indeed the uniform eigenspace has eigenvalue one and all other eigenvalues
have absolute value at most `lambda`. No laziness assumption is used.
For `D=D_j`, the operators `VDV` and `D^(1/2)|T|D^(1/2)` are `XX*` and
`X*X` for `X=VD^(1/2)`. Hence

```text
||VDV|| = ||D^(1/2)|T|D^(1/2)||
        <= lambda ||D||+(1-lambda)||D^(1/2)PD^(1/2)||
        <= lambda+(1-lambda)||U*DU|| <= c.                   (PS4)
```

The endpoints improve as well:

```text
U*D|T|DU <= lambda U*D^2U+(1-lambda)U*DPDU
         = lambda U*D^2U+(1-lambda)(U*DU)^2
         <= [lambda a+(1-lambda)a^2]I = ac I.                (PS5)
```

Thus `||VDU||` and `||U*DV||` are at most `sqrt(ac)`. In (PS2), insert
`T=VJV`: two endpoints contribute `ac`, the `t-2` middle sandwiches
contribute `c^(t-2)`, and all sign factors are contractions. Therefore
`||A_t||<=a c^(t-1)`. Since `A_t>=0`, `e(I-A_t)=1-||A_t||`, proving soundness.
There is no division by `a` or `c`, so endpoint energies zero and one are
included. The matrices `V,J` are proof devices, not required computations.

For completeness take a unit ground vector `psi` of `H` and the trial
state `psi^(tensor t)`. Put `a_v=<psi,h_v psi>`. For each walk,
`1-product_j(1-a_(v_j))<=sum_j a_(v_j)`. Each position is uniform, giving
energy at most `t epsilon`; positivity and normalization give the bound one.
This proves (PS1).

### Rational bound and comparison

For `B_t(lambda)=1+(t-1)(1-lambda)`,

```text
e(G_t(H)) >= B_t(lambda) epsilon/(1+B_t(lambda) epsilon).      (PS6)
```

For `x in [0,1]`, `1-x<=1/(1+x)` and
`(1-y)^s<=1/(1+sy)` for integer `s>=0`, `y in [0,1]`.
The latter follows by differentiating `(1-y)^s(1+sy)`, which is
nonincreasing (the case `s=0` is equality). Multiply with
`y=(1-lambda)x`, and use
`(1+x)(1+(t-1)(1-lambda)x)>=1+B_t(lambda)x`. Taking complements proves (PS6).
For `lambda<=1/2` use `B_t=(t+1)/2`.

The September 11 estimate was
`1-(1-epsilon)(1-(1-lambda^2)epsilon)^((t-2)/2)`.
Set `r^2=1-(1-lambda^2)epsilon`. Then
`r^2-c^2=(1-lambda)^2 epsilon(1-epsilon)>=0`, so
`c^(t-1)<=r^(t-2)`: (PS1) dominates that estimate. For `lambda=0`,
`A_t=(I-H)^(tensor t)`, and (PS1)'s lower bound is exact.

Known operator-valued expander-walk amplification is prior art:
[Jeronimo–Mittal–Roy–Wigderson, Theorem 3.6](https://arxiv.org/html/2209.07024v2).
A cyclic shift of copies converts tensor emissions to their operator
framework, as the September 11 artifact explains. No qualitative novelty
or historical-priority claim is made here.

Repeated amplification without reduction grows locality to `k t^r`.
Writing all walks of one long walk also costs exponentially many terms in
its length. Neither operation alone gives constant-locality quantum PCP.

## 3. Conditional iteration with loss below (t+1)/2

Fix `k_0>=5`, integer `t>=2`, and constants `L,A,S>=1`. Suppose a
deterministic polynomial-time reducer, given `H` and its explicit walk
amplification, returns a normalized at-most-`k_0`-local qubit Hamiltonian
`H'` on **every** at-most-`k_0`-local input, satisfying

```text
e(G_t(H))/L <= e(H') <= A e(G_t(H))+2^(-n),                    (R1)
n <= n' <= Sn,  m' <= Sm,  b' <= S(b+n+m+1).                  (R2)
```

Here `b` is the maximum term-description bit length including supports,
and fixed amplification/duplication factors are absorbed into `S`.
These are separate soundness, completeness, closure, and linear resource
requirements. Merely polynomial output size per invocation is insufficient.

**Theorem.** If `L<B_t=(t+1)/2`, this reducer proves the normalized
constant-locality quantum-PCP target.

For NO energy `epsilon_i>0`, (PS6) and (R1) give

```text
epsilon_(i+1) >= B_t epsilon_i/[L(1+B_t epsilon_i)].           (R3)
```

Set `z_i=1/epsilon_i` and `theta=L/B_t<1`. Then
`z_(i+1)<=theta z_i+L`, and induction yields

```text
epsilon_r >= 1/[theta^r/epsilon_0+L(1-theta^r)/(1-theta)].     (R4)
```

Starting with `epsilon_0>=1/q(N)`, choose `r=O(log N)` with
`theta^r q(N)<=1`. The resulting floor is the positive constant

```text
g=1/[1+L/(1-theta)].                                         (R5)
```

The positive fixed point of (R3)'s comparison map is
`(B_t-L)/(B_t L)`, positive exactly when `L<B_t`.

For YES inputs, let `K=max{1,At}`. Pad with spectator qubits to `n_0>=N`;
(R2) ensures `n_i>=N`. With `a_0<=2^(-N)`,

```text
a_(i+1)<=K a_i+2^(-N),
a_r<=K^r(a_0+r 2^(-N))<=K^r(r+1)2^(-N).                     (R6)
```

Since `r=O(log N)`, this is eventually at most `g/4`. Finitely many smaller
input lengths may be hard-coded. The site, term, and bit-length vector
satisfies a fixed linear growth bound by (R2) and the constant-size tensor
products. After `O(log N)` rounds it is polynomial, as is total time.
Fixed rational bounds above `theta` (below one) and below `g` suffice to
implement the round count and final thresholds; real constants require no
numerical oracle. This proves the conditional theorem.

| Analysis | Sufficient loss at spectral bound 1/2 |
|---|---|
| September 11 nonlinear estimate followed by coarse truncation | `L<(3t+2)/16`, even `t` |
| Same old estimate, reciprocal iteration | `L<(3t+2)/8`, even `t` |
| Positive sandwiches and reciprocal iteration | `L<(t+1)/2`, all integers `t>=2` |

For the middle row, put `s=(t-2)/2` and apply the rational argument to
`(1-x)(1-3x/4)^s`; its slope is `1+3s/4=(3t+2)/8`.
At `t=10`, `B_t=11/2` allows `L=5`. Starting at `1/1024`, 73 comparison
rounds certify the floor `1/56`; the comparison energy is approximately
`0.017882099660054156`. This is an exact recurrence example, not an
instance of a constructed reducer.

## 4. Matching private-proof obstruction at every fixed locality

Use the existing [FCC definition and fake-data lemma](../factorwise-complete-composition-returns-the-input-energy-proof.md).
For clarity the full hypothesis and core proof follow. On diagonal input
predicates, encode each original bit in each copy by its own independent
isometry into a block. Each amplified clause `f` has a private register
`A_f` and a normalized local tester `G_f=sum_i p_(fi) g_(fi)`, with
`0<=g_(fi)<=I`. Each test meets at most `k_0` data blocks and only the
clause's private proof; its support within that proof is unrestricted.
The output is `H'=sum_f mu_f G_f`, with probability weights.

Factorwise completeness requires that **every** classical tuple `y`
satisfying the selected predicate in each copy has a private proof
`pi_f^y` of `G_f`-energy at most `eta`. This is stronger than completeness
only on globally valid histories. Proofs may depend on `y` and have
unbounded size and circuit complexity.

Suppose each predicate has at least `r` distinct variables and flipping
any one of them repairs a violation. If a distribution of input assignments
violates each specified predicate with probability at most `rho`, then

```text
e(H') <= eta+rho k_0/r.                                      (FCC)
```

**Proof.** Sample one assignment `x` and put it in every actual data copy.
For each clause independently, repair each violated selected factor by
flipping a uniformly chosen variable in that factor, obtaining `y^f`.
Repairs within one clause lie in different copies, so every selected
factor is now satisfied. Prepare the private honest proof `pi_f^(y^f)`,
while retaining actual data `x`. All these proofs coexist as a product
conditional on the sampled assignment and repairs. If a test meets no
repaired data block, its reduced state equals its honest reduced state,
by product encoding. Otherwise its energy changes by at most one.
Each queried block is flipped with probability at most `rho/r`; a union
bound gives `rho k_0/r`. Average tests, clauses and random choices to
obtain a valid mixed trial state with (FCC)'s energy. No independence of
queried-block events or separability of an arbitrary output is assumed.

### Regular-graph parity instances

For each fixed `r>=2`, take a connected simple `r`-regular graph with `m`
vertices and a Boolean variable on every edge. Charge vertex zero by one
and every other vertex by zero. Let `h_v` project onto violation of the
incident-edge parity equation at `v`; `H_F=(1/m)sum_v h_v`.

If `A` is the binary incidence matrix, every column has two ones, so
`Ax=e_0` is impossible. Every assignment violates at least one predicate.
For each target `v`, a path from zero to `v` has incidence `e_0+e_v`;
its edge indicator therefore violates **only** `v`. Use the empty path
for `v=0`. Thus `e(H_F)=1/m`; diagonality prevents a quantum state from
lowering the classical minimum. Uniform choice of target gives violation
probability exactly `1/m` at every vertex. Each term has locality `r`
and every variable occurs in two terms.

For all sufficiently large even `m>r`, explicit examples are the circulant
with steps `±1,...,±r/2` for even `r`; for odd `r` use
`±1,...,±(r-1)/2` and the antipodal perfect matching. They are simple and
regular; step-one edges ensure connectedness. This covers odd arity too.

### Threshold theorem

Fix output locality `k_0>=2`, take `r=k_0`, and fix integer `t>=2`.
Suppose a universal FCC reducer has completeness error `eta_m` with
`m eta_m -> 0` on this family and satisfies `e(H')>=e(G_t(H_F))/L`.
By (FCC), `e(H')<=eta_m+1/m`. By (PS1) at spectral bound `1/2`,

```text
F_t(x)=1-(1-x)(1-x/2)^(t-1),
m F_t(1/m)/L <= 1+m eta_m.
```

Since `F_t(0)=0`, `F_t'(0)=(t+1)/2=B_t`, taking `m` to infinity gives

```text
L >= B_t.                                                   (FCC-sharp)
```

More generally `limsup m eta_m<=c` implies `L>=B_t/(1+c)`.
With spectral bound `lambda`, the identical argument gives
`L>=B_t(lambda)`. Encodings of entire copies instead of independent bits
only give `L>=B_t/k_0` from the existing whole-copy lemma; they are not
silently included in the stronger conclusion.

The factor average satisfies
`E_walk (1/t)sum_j h_(v_j)^(j)=(1/t)sum_j H^(j)` by stationarity;
its ground energy is exactly `e(H)`. It attains (FCC) for `eta=0,r=k_0`.
It does not attain a claimed optimal universal reducer loss.

The obstruction excludes universal independent-block, private-proof,
factorwise-complete reducers at the sufficient threshold. It excludes
private clocks, assignment testers and mediator gadgets only when they
meet these hypotheses. It allows shared proof registers, correlated
encodings, genuinely global completeness, and restricted QMA-hard domains.
A restricted route must specify a QMA-hard seed family and a proved invariant
preserved by amplification and reduction; an unnamed class of successful
outputs is circular. No such closed family is constructed here.

## 5. Exact finite regressions

Run with Python 3.10 or later, using only the standard library:

```sh
python3 research/artifacts/check-qpcp-global-walk-2026-09-11.py
python3 research/artifacts/check-qpcp-strengthened-amplification-2026-09-20.py
```

The first script checks the original 128 labelled four-vertex walks,
transfer identity, and full 16-dimensional rational LDL certificate with
lower bound `8/25`. Its acceptance matrix hash is
`ab80b435a5c3f8ade43f223cfc0914a1ac773884e1e900758df5d7492a920dd7`.

The second is the supplied Appendix A regression, adapted only for style
and certificate reporting. Its checked-in JSON records 27 regular graphs,
294 one-defect witnesses, 3,232 old-bound scalar grid cases, 6,464 sharper
scalar grid cases, and nine full-operator inequalities for noncommuting
projectors. The operator cases have 2, 3, or 4 copies and nontrivial
transition eigenvalue `-1/2`, `0`, or `1/2`; the negative cases test the
absence of an implicit laziness requirement. Exact LDL decompositions are
replayed on the full spaces. On the original four-copy acceptance matrix,
the new certified lower bound is `521/1250`. The reciprocal recurrence
and the 73-round example above are checked with exact fractions.

These are finite regression certificates, not formal verification or a
replacement for the universal proofs. No test instantiates the missing
locality reducer. See the [replay](qpcp-strengthened-amplification-replay-2026-09-20.json).

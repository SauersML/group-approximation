# Independent conditional acceptance of Liu's Theorem 5.1 assembly

2026-09-20. Scope: the assembly on printed pages 23–29, independently
cross-checked against `large-scalar-blocks-from-repair-and-resolvents` and
`liu-block-construction-audit-2026-09-20.md`. This is a conditional proof
check, not an independent acceptance of its four analytic input theorems.

## Attribution and verdict

**Conditional PASS.** The route's four stated premises suffice for its
target, with the advertised original dimensions, tolerance-dependent
scalar gaps, unrestricted ranks and numbers of blocks, and doubled
nearby generators. No further hypothesis or unproved assembly step was
found in this cross-review.

The proof being checked is **Jihao Liu**, [*Nonhyperlinear groups
exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf)
(2026-09-20), Theorem 5.1, using Theorems 3.2 and 4.3 and Lemmas
5.2–5.4. This note does not claim Liu's analytic proof for Cairn and
does not establish Theorem 6.7 or any of the input leaves merely by
citing this acceptance.

The four inputs, treated as premises rather than reproved here, are:

- `quotient-gap-gives-uniform-relative-projection-repair`;
- `low-energy-povms-round-equivariantly-in-place`;
- `resolvent-assembly-controls-covariance-and-leakage`;
- `defective-block-expansion-prunes-to-doubled-gaps`.

All traces and norms below use the ambient physical denominator d_n
unless explicitly identified as a normalized retained-block trace.

## 1. Selection and quantitative coverage

Fix t>0 before any ultrafilter limit. Put L=36/a^2, beta=t/(4L),
gamma=sqrt(t), lambda=1/t. The repair premise supplies ONE e_n and
eta_n BEFORE any choice of test projection. Its vanishing bad trace
and eta_n are thus valid for every adaptively selected seed.

For any p, rounding e_n p e_n at 1/2 gives q<=e_n with
`||p-q||_2^2<=2 tr(p(1-e_n))`. Consequently the strict test

```
E_n(p)+3 tr(p(1-e_n)) < beta tr(p)
```

implies a repaired projection f satisfying
`||f-p||_2^2<t tr(p)`, `E_n(f)<=eta_n tr(f)`, and
`(1-t) rank(p)<rank(f)<(1+t) rank(p)`. The constants require only
L>=1 and the displayed t range in Liu's proof.

In the actual window b_i of D_(i-1)=(I+lambda S_(i-1))^-1, select a
minimum positive-rank p_i satisfying this test. A minimum exists over
integer ranks even though the test is strict; compactness of its open
feasible set is not needed. For B_i=D_(i-1)-D_i the inverse identity
gives `tr(B_i)>=k_t tr(p_i)`, with
`k_t=lambda/(1+lambda) (1-2 sqrt(t))^2>0`. This proves termination,
`sum tr(f_i)<=A_*`, and `J_n=sum E_n(f_i)<=eta_n A_* ->_omega 0`.
The final window's failure of the same test forces its trace to zero.
Since it contains ker(S_m), `A_n=sum tr(f_i)>=1-zeta_n` with
zeta_n tending to zero. No positive lower bound on any seed's trace
has been inserted.

The determinant calculation at the second resolvent scale is compatible
with this adaptive selection: p_i lies in the spectral window
`S_(i-1)<=sigma`, where `sigma=gamma/(lambda(1-gamma))`. Thus

```
A_n log(2)-b_t <= tr log(I+S_m) <= log(1+A_n),
tr phi((I+S_m)/2) <= b_t+h_0 zeta_n,
phi(x)=x-1-log(x).
```

These give `A_n<=1+v_t`, `lim tr(D_m)<=s_t`, and full POVM variance
`lim V_n<=2 q_t`, where v_t,s_t,q_t are O(t). The resolvent input
gives summed POVM energy at most `72 lambda J_n`, hence vanishing.
These estimates are about the actual increments, not substitute
orthogonal projections or a merely approximate partition.

## 2. Covariance and leakage really have vanishing sums

The in-place rounding input supplies the PVM Q_i with summed energy
tending to zero and total squared approximation error at most
`5000 V_n+o_omega(1)`. Its energy conclusion is independent of the
fixed nonzero purity error; a rounding input lacking that feature
would NOT suffice here. Fixed accuracy levels 1/r followed by the
explicit diagonal choice in Liu's proof justify these two conclusions
simultaneously with an unbounded number of labels.

For Liu's fixed cutoff g at this fixed t, set
`Y_i=g(D_(i-1)) B_i Q_i`. The terms involving commutators of B_i and
Q_i have vanishing squared sums. The remaining term is localized:

```
||[u,g(D)] B_i||_2 <= sqrt(lambda) ||[u,g(D)] D f_i||_2,
[u,g(D)]D = [u,g(D)D]-g(D)[u,D].
```

Both D and g(D)D are fixed continuous functions of S_(i-1) with
finite limits at infinity. The localized resolvent premise therefore
controls their sums against f_i. In particular it proves
`sum_i E_n(Y_i)->_omega 0`; no factor m_n is introduced.

The common spectral cutoff of G_i=Y_i^*Y_i on [1/3,1/2] is legitimate
for arbitrarily many labels because `sum tr(G_i)<=1`. Its coarea
estimate yields orthogonal initial projections P_i<=Q_i and
`sum E_n(P_i)->0`. The bounded Lipschitz inverse-square-root cutoff
then gives partial isometries V_i with

```
V_i^*V_i=P_i,   Pi_i=V_i V_i^*<=b_i,
sum E_n(V_i)->0,
Pi_i <= 3 g(D_(i-1)) B_i g(D_(i-1)).
```

The last domination is essential: the range projections Pi_i are NOT
asserted orthogonal. The monotone leakage premise, first at each fixed
rho>0 and then with rho decreasing, gives
`sum tr(Pi_i(1-e_n))->0`. More explicitly its bound is
`6 K_(g,rho) tr(1-e_n)+6 rho^2`; first take the ultrafilter limit,
then rho->0. This establishes the needed total range leakage without
assuming any relation between the ranks of e_n and individual blocks.

## 3. Every transported half-rank test is covered

Pinching and polar completion give w_j reducing all P_i, with
`sum_j ||w_j-u_j||_2^2->0`. Define

```
Delta_(j,i)^+ = u_j V_i-V_i w_j,
Delta_(j,i)^- = u_j^* V_i-V_i w_j^*,
Z_i=(4h)^-1 sum_j ((Delta^+)^*Delta^+ +(Delta^-)^*Delta^-),
H_i=V_i^*(1-e_n)V_i.
```

These positive matrices are supported on P_i. The crucial summation
uses only the initial projections:

```
sum_i ||V_i(u_j-w_j)||_2^2
 = tr((u_j-w_j)^* (sum_i P_i) (u_j-w_j))
 <= ||u_j-w_j||_2^2.
```

Together with summed energy of V_i, this proves `sum tr(Z_i)->0`.
The adjoint calculation is valid because
`[u^*,V]=-u^*[u,V]u^*`. Cyclicity and the range leakage prove
`sum tr(H_i)->0` independently.

Now take ANY projection q<=P_i of rank at most rank(P_i)/2. The
transport y=V_i q V_i^* is a projection inside the SAME b_i selected
earlier. Moreover

```
rank(y)=rank(q)<=rank(P_i)/2
 <=rank(f_i)/2<(1+t)rank(p_i)/2<rank(p_i).
```

If q is nonzero, y cannot satisfy the strict selection test, by the
actual minimum-rank rule. For q=0 the resulting inequality is trivial.
Thus every q simultaneously obeys
`beta tr(q)<=E_n(y)+3 tr(q H_i)`.
The exact commutator identity is

```
[u_j,V_i q V_i^*]
 = V_i[w_j,q]V_i^* + Delta_(j,i)^+ q V_i^*
   -V_i q (Delta_(j,i)^-)^*.
```

Because w_j reduces P_i, its first term has the same 2-norm as
`[w_j,q]`. The two error terms have total weighted squared norms
`tr(q Z_i)`. The direct-sum triangle inequality gives
`E_n(y)<=2 E_w(q)+4 tr(q Z_i)`. Hence

```
E_w(q)>=(beta/2) tr(q)-xi_i,
xi_i=2 tr(Z_i)+(3/2) tr(H_i),
xi_n=sum_i xi_i ->_omega 0.
```

The defect is independent of q and its SUM vanishes. There is no
exchange of an ultrafilter limit with a supremum over projections:
the all-test inequality already holds at each coordinate.

## 4. Order of limits and exact output

The pruning premise applies at the fixed positive threshold
theta=beta/2. It loses at most `16 xi_n/beta` trace and perturbs the
doubled unitaries by a total squared amount at most `16 h xi_n/7`
relative to w_j. Both vanish at this fixed t. Every retained block
has scalar gap `beta^2/256` in its own normalized trace.

The earlier coverage bound leaves trace at most
`F(t)=2((5002+4/gamma)q_t+s_t)=O(sqrt(t))`. Given epsilon, choose
ONE fixed t with F(t)<=epsilon, and perform every preceding limit
at that t. No claim of uniform covariance constants as t->0, no
varying-threshold pruning, and no gap independent of epsilon is used.
This proves exactly the canonical target and no stronger fixed-gap
decomposition for the unperturbed generators.

## 5. Separate all-fields comparison

The new `leavitt-all-fields-normalization-obstruction-2026-09-20.md`
matches Section 7 of
`liu-leavitt-direct-internality-and-consequences-2026-09-20.md`.
In particular it includes the finite elementary-factorization
coefficients of u,k_+,k_- in the finitely generated subring S, does
NOT assume GL_4(S)=EL_4(S), proves generation over every r in S,
and uses the killed nonzero mark x_24(a) from k_+. This avoids
requiring a factorization of an additional unit k. Characteristic
two, simplicity, and finite presentation are not needed for that
all-fields nonhyperlinearity deduction. Its analytic normalization
premise remains separate from this Theorem 5.1 cross-review.

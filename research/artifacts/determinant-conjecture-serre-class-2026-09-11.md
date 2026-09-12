# The determinant conjecture as an arithmetic condition on spectral measures

Date: 11 September 2026 (fork `determinant-conjecture`). Written proofs, no
machine verification. Literature statements marked *cited* were not re-read
from source in this session.

## 0. Setting

For a group `G`, `tau` is the canonical trace on `N(G)`, extended to
`M_n(N(G))` as `tr_n (x) tau` normalized so `tau(1)=1`. For a self-adjoint
`A` in `M_n(C[G])`, `mu_A` is its spectral probability measure on `R`. The
Fuglede--Kadison determinant of a self-adjoint `B` is

```text
det(B) = exp( integral_{(0,infinity)} log t  d mu_|B|(t) ),
```

with the kernel excluded. For `f` a real polynomial and `A` self-adjoint,
functional calculus gives

```text
log det f(A) = integral_{ f != 0 } log |f(lambda)|  d mu_A(lambda).      (FC)
```

*Cited:* Lück's determinant conjecture (Lück, *L^2-Invariants*, 2002,
Chapter 13): for every group `G` and every `A in M_{m x n}(Z[G])`,
`det(A) >= 1`. It holds for sofic groups (Elek--Szabó, Math. Ann. 332
(2005)) and for Schick's class `G` (Schick, Trans. AMS 353 (2001)).
`det(A^*A) = det(A)^2` is a standard property of the determinant.

Define the **Serre class** of probability measures on `R`:

```text
S = { mu : integral_{Q != 0} log|Q| d mu >= 0  for every nonzero Q in Z[x] }.
```

## 1. Exact reformulation

**Theorem 1.** A group `G` satisfies the determinant conjecture if and only
if `mu_A` lies in `S` for every `n` and every self-adjoint `A in M_n(Z[G])`.

*Proof.* (<=) Given `B in M_{m x n}(Z[G])`, put `A=B^*B`, self-adjoint in
`M_n(Z[G])`. With `Q=x`, (FC) gives `log det(A) >= 0`, and
`det(B)=det(A)^(1/2) >= 1`.

(=>) For nonzero `Q in Z[x]`, `Q(A)` is a self-adjoint element of
`M_n(Z[G])`, so the conjecture gives `det Q(A) >= 1`, and (FC) is the Serre
inequality for `Q`. QED

So the conjecture concerns only single operators, one variable at a time: it
asks whether integral group-ring spectra obey every Serre inequality.

## 2. Integral spectral limits obey the Serre inequalities

Call a probability measure an **integral spectral measure** if it is the
normalized eigenvalue counting measure of a symmetric integer matrix.

**Theorem 2.** Let `mu_k` be integral spectral measures supported in
`[-C,C]`, converging weakly to `mu`. Then `mu` lies in `S`.

*Proof.* Fix nonzero `Q in Z[x]` and let `Z` be its (finite) zero set in
`[-C,C]`.

1. For a symmetric integer `N x N` matrix `B`, `Q(B)` is a symmetric integer
   matrix whose nonzero eigenvalues are exactly the values `Q(lambda_i) != 0`.
   Their product is, up to sign, the lowest nonzero coefficient of the
   characteristic polynomial of `Q(B)`, a nonzero integer. Hence
   `integral_{Q!=0} log|Q| d mu_B >= 0`.
2. For `0<delta<1`, `f_delta = log max(|Q|,delta)` is continuous and bounded
   on `[-C,C]`, so `integral f_delta d mu = lim_k integral f_delta d mu_k`.
3. `integral f_delta d mu_k >= mu_k(Z) log delta + integral_{Q!=0} log|Q| d mu_k
   >= mu_k(Z) log delta`.
4. By the portmanteau theorem (`Z` is closed), `limsup mu_k(Z) <= mu(Z)`.
   Since `log delta<0`, `integral f_delta d mu >= mu(Z) log delta`. Hence
   `integral_{Q!=0} log max(|Q|,delta) d mu >= 0` for every `delta`.
5. As `delta` decreases to 0 the integrands decrease to `log|Q|` on `{Q!=0}`
   and are bounded above. Monotone convergence gives
   `integral_{Q!=0} log|Q| d mu >= 0`. QED

With Theorem 1: **if every self-adjoint `A in M_n(Z[G])` has `mu_A` equal
to a weak limit of integral spectral measures of bounded support, then `G`
satisfies the determinant conjecture.** Soficity supplies such limits (a
sofic model of `A` is an integer matrix), but the condition is one-variable
and makes no mention of any approximation of `G` itself.

This is one-sided. `fk-transfer-needs-uniform-log-integrability` shows that
moment convergence does not carry log determinants across in general. Only
the inequality survives the limit, and the integrality of every approximant is
what carries it.

## 3. Integer moments are not enough

The moments `tau((A^*A)^j)` of an integral group-ring element are integers.
That alone does not give the conjecture.

**Proposition 3.** Let `phi=(1+sqrt5)/2`, `psi=(1-sqrt5)/2=-1/phi`, and

```text
mu = w_+ delta_(phi^2) + w_- delta_(psi^2),    w_(+/-) = (1 -/+ 1/sqrt5)/2.
```

Then `mu` is a probability measure on `[0,3]`, every moment is an integer,
`m_j = (L_(2j) - F_(2j))/2` (Lucas and Fibonacci numbers), and

```text
integral log lambda d mu = -(2/sqrt5) log phi < 0.
```

*Proof.* Binet: `phi^k=(L_k+F_k sqrt5)/2`, `psi^k=(L_k-F_k sqrt5)/2`. Then
`m_j = (phi^(2j)+psi^(2j))/2 - (phi^(2j)-psi^(2j))/(2 sqrt5)
= L_(2j)/2 - F_(2j)/2`, an integer because `L_k = F_(k-1)+F_(k+1) == F_k
(mod 2)`. The log integral is `w_+ log phi^2 + w_- log psi^2 =
(w_+ - w_-) 2 log phi`. Check: `m_1=1`, `m_2=2`, `m_3=5`. QED

Its failure is Galois-theoretic. The two atoms are conjugate algebraic units,
and the conjecture forces equal mass on conjugates in this purely atomic
situation, since `phi^2 psi^2 = 1`. A spectral measure in `M_n(Z[G])` with
unequal von Neumann multiplicities on a Galois orbit, and no compensating
continuous part, would violate the conjecture. Galois invariance of
`dim_N(G) ker(A-lambda)` is known for sofic groups but is not assumed here.

## 4. What this means for nonsofic groups

A counterexample must be a nonsofic group (Elek--Szabó), and by Theorem 1 it
is witnessed by one self-adjoint `A in M_n(Z[G])` and one nonzero
`Q in Z[x]` with `integral_{Q!=0} log|Q| d mu_A < 0`. The model failure is
Proposition 3: conjugate eigenvalues carrying unequal von Neumann mass.

Test groups: the binary Leavitt unit group (`openai-leavitt-unit-nonsofic`),
the Kun--Thom wreaths `(Z/2) wr_(G/Gamma) G` (`kun-thom-nonsofic-wreath`), and
Fournier-Facio's torsion-free group (`fournier-facio-group-is-nonsofic`).

For a Kun--Thom wreath `W`, the Fourier transform on the base identifies
`L(W)` with the generalized Bernoulli crossed product
`L^infinity({±1}^(G/Gamma)) x| G`, whose action Kun--Thom prove not sofic
(Corollary D). Each finite-index normal `N` in `G` gives a finite quotient
`W -> (Z/2) wr_(G/Gamma N) (G/N)` by summing over fibers. These quotients
cannot separate `W`, because `Gamma` is not profinitely closed. Their integral
spectral measures therefore approximate the spectral measure of the image of
`A` in a proper quotient trace, not `mu_A` itself. Whether `mu_A` is an
integral spectral limit for every `A` is exactly the open case.

## 5. Purely atomic Serre-class measures are Galois-equidistributed

**Theorem 5.** Let `mu` be a probability measure on `R` supported on finitely
many algebraic integers. Then `mu` lies in `S` if and only if:
- every atom is totally real;
- for every Galois orbit, all conjugates in the orbit carry the same mass.

*Proof.* (<=) Let `O` be an orbit of degree `d` with common weight `w`, and
let `Q` be nonzero in `Z[x]`. If `Q` vanishes at one conjugate it vanishes on
all of `O`, and `O` is excluded from the integral. Otherwise the contribution
of `O` is `w log|N_(K/Q)(Q(alpha))|`, which is nonnegative because
`Q(alpha)` is a nonzero algebraic integer.

(=>) Fix an orbit `O` of `alpha`, with `K=Q(alpha)` of signature `(r1,r2)`
and weights `w_i` on the real conjugates. Put
`Q_k = R_k * prod_(O' != O) P_(O')`, where `P_(O')` is the minimal polynomial
of another orbit and `R_k in Z[x]` satisfies `R_k(alpha)=u^k` for a unit `u`
of the order `Z[alpha]`. `Q_k` vanishes on every other orbit, so the Serre
inequality reads `k sum_i w_i log|sigma_i u| + C_O >= 0`, with `C_O`
independent of `k`. Since `k` ranges over `Z` (u^(-1) lies in `Z[alpha]`),
`sum_i w_i log|sigma_i u| = 0` for every unit `u`.

The units of `Z[alpha]` have finite index in `O_K^x`, so by Dirichlet their
logarithmic embedding spans the hyperplane `sum x = 0` in `R^(r1+r2)`, with
coordinates `log|sigma_i u|` at the real places and `2 log|tau_j u|` at the
complex ones. The weight vector `(w_1..w_r1, 0..0)` is orthogonal to that
hyperplane, so it is a multiple of `(1,...,1)`. If `r2 > 0` it is zero, so an
orbit carrying positive mass is totally real, with equal weights. QED

The Fibonacci measure of Section 3 fails exactly this test.

## 6. Where a violation can live

For `A in M_n(Z[G])` let `H` be the subgroup generated by the support of `A`.
The trace of `N(G)` restricts to that of `N(H)`, so `mu_A` and `det(A)` are
the same computed in `H` or in `G`. By Elek--Szabó a violation needs `H`
nonsofic. For the test groups:
- **Kun--Thom wreath `W = B x| G`.** Elements over the locally finite base
  `B`, or over the residually finite group `G`, obey the conjecture. A
  violation must mix lamps and group letters so that they generate a
  nonsofic subgroup.
- **Leavitt unit group.** Elements over locally finite subgroups or free
  subgroups obey the conjecture. The nine-leaf elementary subgroup is a
  finitely generated nonsofic support. Thompson's `V` sits inside, and its
  soficity is open.

## 7. Moment-only approximation schemes cannot work

Gauss quadrature at order `j` of a measure with integer moments has algebraic
nodes and Christoffel weights that need not be Galois-equal. The normalized
eigenvalue counting measure of the Jacobi matrix is uniform on the nodes, with
non-integral entries, and does not converge to `mu` in general. The Fibonacci
measure is its own two-node quadrature and is not in `S`. So no scheme that
sees only the moments of `mu_A` can produce integral approximants. It must use
the group, or Galois equidistribution of spectral mass, which Theorem 5 shows
is forced whenever the spectrum is purely atomic.

The converse to Theorem 2 is a separate question: is every Serre-class measure
on an interval an integral spectral limit? A. Smith, arXiv:2111.12660, gives a
necessary and sufficient condition for a measure on a compact set (under
technical hypotheses) to be a limit of distributions of conjugates of algebraic
integers. Its exact condition was not re-read here, so it is not imported. Two
gaps remain even if it applies:
- equidistributed orbits must be realized by symmetric integer matrices with
  negligible extra spectrum;
- companion matrices are not symmetric, and tree adjacency realizations
  (cited, not re-read: Salez, JCTB 2015) add uncontrolled eigenvalues.

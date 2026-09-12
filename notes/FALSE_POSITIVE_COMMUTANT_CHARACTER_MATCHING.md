# Positive-invisible Fourier walls are an exact character-matching problem

Date: 2026-08-11

## 1. Outcome

The paired-Fourier globalization problem asks for a unitary which is
invisible on a common positive additive subgroup but moves one marked
Laurent class.  On a finite abelian tangent module this local problem has an
exact solution.  It is not a dense unitary optimization.

Let `A` be a finite abelian group, let

`pi:A -> U(V)`                                                `(PCM1)`

be a finite-dimensional unitary representation, let `P<=A`, and let
`m in A`.  Among all unitaries commuting with `pi(P)`, the maximum squared
normalized Hilbert--Schmidt displacement of `pi(m)` is a finite assignment
problem inside the fibers of character restriction

`A^ -> P^.`                                                  `(PCM2)`

For the regular representation the answer depends only on the order `r` of
`m+P` in `A/P`:

`E_reg(P,m)=0`                         if `r=1`,
`E_reg(P,m)=4`                         if `r` is even,
`E_reg(P,m)=2+2 cos(pi/r)`             if `r>1` is odd. `(PCM3)`

In particular, every nonzero marked quotient class has

`E_reg(P,m)>=3.`                                            `(PCM4)`

Thus local positive invisibility and macroscopic marked displacement are
automatic as soon as the marked class survives in `A/P`.  The optimum is
attained by a permutation of Fourier characters, equivalently by an exact
finite Pauli multiplier; numerical unitary search cannot improve it.

This does **not** finish FALSE.  In an honest finite Laurent quotient the
image of the full positive polynomial module can already contain the inverse
marked monomial, making `m in P` and forcing `(PCM3)` to vanish.  In a
growing-window model the remaining problem is to choose these character
permutations coherently over the external principal bundle.  The theorem
reduces that gate to finite character incidences and twisted cocycle
constraints.

## 2. Character-fiber decomposition

Normalize the Hilbert--Schmidt norm by

`||X||_2^2=dim(V)^(-1) Tr(X^*X).`                       `(PCM5)`

Define

`E_pi(P,m)`
` =max_{T in U(V), [T,pi(p)]=0 for all p in P}`
`      ||T pi(m) T^* - pi(m)||_2^2.`                    `(PCM6)`

Since `A` is finite abelian,

`V=directSum_(chi in A^) V_chi,`
`pi(a)|_(V_chi)=chi(a) 1_(V_chi).`                      `(PCM7)`

For `eta in P^`, put

`V_eta=directSum_(chi|_P=eta) V_chi.`                  `(PCM8)`

The spaces `(PCM8)` are exactly the joint eigenspaces of `pi(P)`.  Hence

`pi(P)'=directSum_(eta in P^) End(V_eta).`             `(PCM9)`

For each `eta`, list the eigenvalues of `pi(m)|_(V_eta)`, with
multiplicity, as

`z_(eta,1),...,z_(eta,d_eta) in S^1.`                  `(PCM10)`

## 3. Exact assignment formula

**Theorem 1.**  With the preceding notation and `d=dim(V)`,

`E_pi(P,m)`
` =2-(2/d) sum_eta min_(sigma in Sym(d_eta))`
`                    sum_(i=1)^(d_eta)`
`                    Re(z_(eta,sigma(i)) conjugate(z_(eta,i))).` `(PCM11)`

In particular, an optimizer may always be chosen to permute the character
slots inside each `P`-isotypic block.

### Proof

Put `U=pi(m)`.  Every admissible `T` is block diagonal over `(PCM8)`, and

`||TUT^*-U||_2^2`
` =2-2 Re dim(V)^(-1) Tr(TUT^*U^*).`                  `(PCM12)`

On one block, diagonalize `U=diag(z_1,...,z_s)`.  Direct expansion gives

`Re Tr(TUT^*U^*)`
` =sum_(i,j)|T_(ij)|^2 Re(z_j conjugate(z_i)).`       `(PCM13)`

The matrix `(|T_(ij)|^2)` is doubly stochastic.  The right side of
`(PCM13)` is linear in this matrix, so its minimum over all doubly
stochastic matrices occurs at a permutation matrix by the Birkhoff--von
Neumann theorem.  Every permutation matrix is unitary and is therefore
admissible.  Thus the minimum over unitaries is exactly the assignment
minimum.  Summing the block minima in `(PCM12)` proves `(PCM11)`.  End
proof.

**Corollary 2 (exact zero criterion).**  `E_pi(P,m)=0` if and only if
`chi(m)` is constant among the characters in the spectral support of `pi`
having any fixed restriction to `P`.

Equivalently, `pi(m)` is central in the finite-dimensional algebra
`pi(P)'`.  Positive marked energy occurs exactly when two spectral
characters agree on `P` but disagree on `m`.

### Proof

The displacement in `(PCM6)` vanishes for every admissible `T` exactly when
`pi(m)` commutes with all of `pi(P)'`.  By `(PCM8)--(PCM10)`, this is
equivalent to being scalar on every `V_eta`.  End proof.

## 4. Closed formula for the regular representation

Take `pi=lambda_A`, the left regular representation.  In the Fourier basis
every `chi in A^` occurs once.  The fibers of `(PCM2)` are cosets of

`P^perp={nu in A^:nu|_P=1}~=(A/P)^.`                 `(PCM14)`

Let `r=ord_(A/P)(m+P)`.  Evaluation at `m` maps `P^perp` onto the group of
`r`th roots of unity, with all fibers of equal size.  Inside every
restriction fiber, every entry of the assignment cost is at least

`c_r=min_(z^r=1) Re(z).`                              `(PCM15)`

Choose `nu_0 in P^perp` attaining `(PCM15)` and use the character
permutation

`chi |-> chi nu_0.`                                   `(PCM16)`

Every matched pair in `(PCM16)` has cost `c_r`, so this lower bound is
attained simultaneously on every fiber.  Therefore

`E_reg(P,m)=2-2c_r.`                                  `(PCM17)`

If `r=1`, then `c_r=1`.  If `r` is even, `-1` is an `r`th root and
`c_r=-1`.  If `r>1` is odd, the roots nearest `-1` have real part
`-cos(pi/r)`.  Equations `(PCM3)--(PCM4)` follow.

The optimizer `(PCM16)` has a concrete Pauli form.  In the physical basis
`ell^2(A)`, it is multiplication by the character `nu_0`; hence it commutes
with every positive translation `lambda_A(p)`, `p in P`, while

`T lambda_A(m) T^*=nu_0(m) lambda_A(m).`              `(PCM18)`

Thus the optimal wall is already an exact root-of-unity multiplier.

## 5. Interface with the equivariant fiber problem

Suppose two sectors use the same basepoint representation `pi` and their
relative holonomy at a base label `k` is `t(k)`.  Agreement on a positive
set `P_0` is exactly

`[t(k),pi(alpha_(k^(-1))g)]=0`
`                  for every g in P_0.`               `(PCM19)`

Write

`P_k=<alpha_(k^(-1))P_0> <= A,`
`m_k=alpha_(k^(-1))m.`                                `(PCM20)`

Then the largest pointwise marked energy compatible with exact positive
agreement is `E_pi(P_k,m_k)`.  For a regular tangent block, Theorem 1
reduces it to the order of `m_k+P_k` and the explicit multiplier `(PCM16)`.

The choices `t(k)` cannot in general be made independently on a transitive
base with nontrivial stabilizer.  On the **regular finite-group base** they
can: `FALSE_REGULAR_BUNDLE_FREE_TABLE_AND_KERNEL_GATE.md` proves that every
unitary table is the relative table of two exact external coboundaries.  For
the actual infinite Laurent action, however, a finite quotient has a
nontrivial kernel action on the fiber.  The remaining constraint is the
explicit kernel-carry intertwining defect `(RBF20)` in that note, not a
constraint among the relative Pauli values themselves.  Thus the continuous
wall variables have disappeared.  Restricting to the optimal Pauli
multipliers turns the remaining search into:

1. compute the positive restriction fibers in the dual tangent module;
2. choose one annihilator character on each base incidence;
3. impose the finite kernel-carry intertwining equations; and
4. maximize the density on which the chosen character is nontrivial at the
   marked class.

This is a finite modular CSP/linear-code problem.  A successful sequence
with nonvanishing objective completes the local commutant portion of the
paired-Fourier FALSE endpoint.  A dual inconsistency certificate would give
a no-go theorem for the entire Pauli/regular subclass.

## 6. Robust reduction from approximate to exact commutants

The exact formula also controls a unitary which only approximately commutes
with the positive subgroup.  Let

`epsilon_P(T)^2`
` =(1/|P|) sum_(p in P)||[T,pi(p)]||_2^2.`             `(PCM21)`

**Theorem 3 (dimension-free commutant correction).**  For every unitary
`T in U(V)`, there is a unitary `T_0 in pi(P)'` such that

`||T-T_0||_2<=sqrt(2) epsilon_P(T).`                  `(PCM22)`

Consequently

`||T pi(m)T^*-pi(m)||_2`
` <=sqrt(E_pi(P,m))+2 sqrt(2) epsilon_P(T).`           `(PCM23)`

Equivalently, if the left side of `(PCM23)` is `D`, then

`E_pi(P,m)>=(max(0,D-2 sqrt(2)epsilon_P(T)))^2.`       `(PCM24)`

### Proof

Let

`mathcal E(X)=(1/|P|) sum_(p in P) pi(p)Xpi(p)^*`     `(PCM25)`

be the trace-preserving conditional expectation onto `pi(P)'`, and put
`X=mathcal E(T)`.  Orthogonality of conditional expectation gives

`epsilon_P(T)^2=2||T-X||_2^2`
`                    =2(1-||X||_2^2).`                `(PCM26)`

Since conditional expectation is operator-norm contractive, `||X||<=1`.
Take the polar decomposition of `X` inside the finite-dimensional algebra
`pi(P)'` and extend its polar partial isometry to a unitary `T_0` in that
algebra.  On every singular value `0<=s<=1`,

`(1-s)^2<=1-s^2.`                                     `(PCM27)`

Therefore

`||X-T_0||_2^2<=1-||X||_2^2=||T-X||_2^2.`            `(PCM28)`

The triangle inequality and `(PCM26)--(PCM28)` give `(PCM22)`.  For any
unitary `U`,

`||TUT^*-T_0UT_0^*||_2<=2||T-T_0||_2.`               `(PCM29)`

Apply `(PCM29)` to `U=pi(m)`, use the definition `(PCM6)` for `T_0`, and
then use `(PCM22)`.  This proves `(PCM23)`; rearranging proves `(PCM24)`.
End proof.

The estimate is independent of `|A|`, `|P|`, and `dim(V)`.  In particular,
when the marked phase is constant on every positive restriction fiber,
Corollary 2 and `(PCM23)` give

`||T pi(m)T^*-pi(m)||_2<=2 sqrt(2)epsilon_P(T).`       `(PCM30)`

Thus approximate positive commutation cannot rescue an absorbed marked
class.  Conversely, Theorem 3 replaces every asymptotically
positive-invisible wall by a nearby exact commutant unitary; Theorem 1 then
computes the sharp supremum over that exact commutant by finite character
matching.

## 7. Sharp finite-window correction and the only local escape

The whole-subgroup average in `(PCM21)` is exact but stronger than the
finite generating-window control supplied by an almost representation.
There is also an exact finite-window bound, with one necessary spectral
factor.

Let `S subset P` generate `P`.  Define the spectral character gap on the
support of `pi` by

`eta_pi(S)`
` =min sum_(s in S)|chi(s)-psi(s)|^2,`                 `(PCM31)`

where the minimum is over spectral characters `chi,psi` with
`chi|_P!=psi|_P`.  If no such pair occurs, put `eta_pi(S)=infinity`.

**Theorem 4 (sharp window-to-commutant estimate).**  For every unitary
`T`, there is a unitary `T_0 in pi(P)'` such that

`||T-T_0||_2`
` <=2 eta_pi(S)^(-1/2)`
`      (sum_(s in S)||[T,pi(s)]||_2^2)^(1/2).`        `(PCM32)`

Consequently

`||T pi(m)T^*-pi(m)||_2`
` <=sqrt(E_pi(P,m))`
`   +4 eta_pi(S)^(-1/2)`
`      (sum_(s in S)||[T,pi(s)]||_2^2)^(1/2).`        `(PCM33)`

### Proof

Use the character decomposition `(PCM7)` and let `mathcal E` be the
conditional expectation `(PCM25)`.  In block-matrix notation,
`T-mathcal E(T)` consists exactly of entries `T_(chi,psi)` for which
`chi|_P!=psi|_P`.  On such an entry,

`[T,pi(s)]_(chi,psi)`
` =(psi(s)-chi(s))T_(chi,psi).`                        `(PCM34)`

Therefore

`sum_(s in S)||[T,pi(s)]||_2^2`
` >=eta_pi(S)||T-mathcal E(T)||_2^2.`                 `(PCM35)`

The polar-correction argument `(PCM27)--(PCM28)` gives a unitary `T_0` in
the commutant with

`||T-T_0||_2<=2||T-mathcal E(T)||_2.`                 `(PCM36)`

Equations `(PCM35)--(PCM36)` prove `(PCM32)`.  Combine `(PCM32)` with the
conjugation estimate `(PCM29)` and the exact optimum `(PCM6)` to obtain
`(PCM33)`.  End proof.

For the regular representation, character restriction is surjective and
`(PCM31)` becomes

`eta_reg(S)`
` =min_(1!=nu in P^) sum_(s in S)|nu(s)-1|^2.`        `(PCM37)`

This is twice the smallest nonzero eigenvalue of the unnormalized Cayley
Laplacian associated with `S` (with the displayed one-sided convention).
For a cyclic group of order `M` with one generator,

`eta_reg(S)=4 sin^2(pi/M)~4 pi^2/M^2.`                `(PCM38)`

Thus the exact character matching plus `(PCM33)` identifies the only local
finite-window escape:

`marked quotient survives and the positive dual spectral gap tends to 0.` `(PCM39)`

This is precisely the high-order-clock regime.  If `eta_pi(S)` is bounded
below, approximate commutation on the fixed positive window reduces
dimension-freely to the exact assignment theorem.  If it tends to zero,
the near-colliding character pair selected by `(PCM31)` is the explicit
clock direction which future global cocycle constraints must transport.

## 8. Branch-cut versus soft-clock dichotomy

Theorems 1 and 4 give a precise local dichotomy for every proposed FALSE
wall.  For a sequence `(A_n,pi_n,P_n,m_n,S_n,T_n)`, write

`D_n=||T_n pi_n(m_n)T_n^*-pi_n(m_n)||_2,`
`Delta_n^2=sum_(s in S_n)||[T_n,pi_n(s)]||_2^2,`
`E_n=E_(pi_n)(P_n,m_n),`
`eta_n=eta_(pi_n)(S_n).`                               `(PCM40)`

Then `(PCM33)` is exactly

`D_n<=sqrt(E_n)+4 Delta_n/sqrt(eta_n).`               `(PCM41)`

**Corollary 5 (local escape dichotomy).**  Suppose

`liminf D_n>=c>0`, `Delta_n->0`.                       `(PCM42)`

Then at least one of the following occurs along a subsequence:

1. **branch-cut escape:** `limsup E_n>0`, so two spectral characters agree
   on `P_n` but distinguish `m_n`;
2. **soft-clock escape:** `eta_n->0` fast enough that

   `limsup Delta_n/sqrt(eta_n)>0`.                     `(PCM43)`

More quantitatively, whenever `D_n>sqrt(E_n)`,

`eta_n<=16 Delta_n^2/(D_n-sqrt(E_n))^2.`              `(PCM44)`

In particular, if the marked class is absorbed in the sense `E_n=0` and
`D_n>=c`, then

`eta_n<=16 Delta_n^2/c^2->0.`                         `(PCM45)`

### Proof

The dichotomy and `(PCM44)` are direct rearrangements of `(PCM41)`.
Equation `(PCM45)` is its specialization to `E_n=0`.  End proof.

For regular tangent blocks, Theorem 1 makes the two branches completely
arithmetic:

* branch cut means `m_n notin P_n`, and already gives `E_n>=3`;
* soft clock means `m_n in P_n` but the least nontrivial positive character
  energy `(PCM37)` tends to zero.

This unifies the two live local constructions.  Truncated long
Fourier/Frobenius modules try to keep the inverse marked monomial outside
the growing positive span.  Natural finite Laurent quotients absorb that
monomial and therefore must use a high-order character whose positive
chord is much smaller than its marked evaluation.  The global
stabilizer/relative-cocycle equations decide whether either local escape can
survive the Kazhdan matching barrier.

## 9. Consequences for compute

Do not optimize arbitrary unitaries at this gate.  The exact assignment
formula proves that character permutations are optimal.  A useful MSI job
should instead emit:

* the finite tangent module and positive submodule at every base incidence;
* the order of the marked quotient class;
* the finite-window character gap `(PCM31)` and its minimizing character
  pair;
* which side of the dichotomy `(PCM41)` supplies the marked energy;
* the annihilator-character variables;
* the sparse modular consistency matrix from external edges and
  stabilizers; and
* either a feasible character assignment with its exact marked density or
  a modular dual obstruction.

The formula also diagnoses the natural finite-ring absorption branch.  If
the finite positive image already contains the marked inverse, then `r=1`
and `(PCM3)` proves exact sterility.  If a branch-cut or truncated module
keeps `r>1`, the local marked separation is automatically at least three in
squared normalized Hilbert--Schmidt norm; only global cocycle coherence
remains.

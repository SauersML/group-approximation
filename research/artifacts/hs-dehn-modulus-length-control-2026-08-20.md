# The Hilbert--Schmidt Dehn modulus: length control replaces self-reference

**Date:** 2026-08-20.
**Status:** four elementary theorems proved here (area bound, word-problem
theorem, Gram saturation, central-pinning fence, exact copying lemma), one
new open target, and a reassessment of the "self-aware search then explode"
programme.  No nonhyperlinear group is claimed.

## 0. Summary

The self-referential route recorded in
`kleene-self-destroying-microstate-lemma` asks for a machine-indexed
compiler `M -> (G_M, w_M)` whose halting side is sound in normalized
Hilbert--Schmidt norm with runtime-independent constants.  This artifact
shows that the self-reference is not the content of that route.  The
content is a single quantitative property of one finite presentation,
which we name the **HS-Dehn modulus**: the defect of a *trivial* word in an
approximate representation, measured against the relator defect, as a
function of the word's *length* rather than its *area*.

- For every finite presentation the HS-Dehn modulus is dominated by the
  Dehn function (Section 1).  So it is finite, and computable whenever the
  word problem is solvable.
- If a finitely presented group is hyperlinear and its HS-Dehn modulus is
  computably bounded, its word problem is solvable (Section 2).  Hence a
  finitely presented group with **unsolvable word problem and computably
  bounded HS-Dehn modulus is not hyperlinear**.  No recursion theorem, no
  machine-indexed family, no search over matrices inside the group: the
  undecidability of the word problem of one fixed group does the work the
  Kleene diagonal did.
- For hyperlinear finitely presented groups the two conditions are
  therefore equivalent: computable HS length control `<=>` solvable word
  problem.  The whole programme is the statement that this equivalence
  fails for some group.
- HS-stability with a computable modulus implies computable HS length
  control, so the known theorem "hyperlinear and HS-stable implies
  residually finite" (`hyperlinear-hs-stable-is-residually-finite`) is the
  special case in which length control comes from stability.  Length
  control is weaker than stability: it asks nothing about nontrivial words
  and nothing about proximity to exact representations.

Three further results explain why the ideas "copy the bad region",
"self-similarity", "dimension-overflow detector" cannot be made to work by
approximate trace data alone, and what they can do:

- **Gram saturation** (Section 3).  Approximate orthogonality data at
  precision `epsilon` certifies dimension at most `O(1/epsilon^2)`, however
  many vectors are involved.  Unbounded dimension at fixed precision cannot
  come from traces of words; it needs an exactification step followed by
  integrality.  This is the conceptual reason the Pauli/Clifford bound
  `marked-clifford-table-exponential-dimension` needs an all-pairs
  epsilon-homomorphism and why the relator-to-all-pairs conversion is the
  crux of every compiler.
- **Central pinning forbids nonlinear predicates** (Section 4).  In a
  finite group with a unique irreducible representation on which a central
  involution `J` acts as `-1`, every commuting family of involutions has,
  in that representation, a joint spectrum that is an affine subspace of
  `F_2^k`.  So a CPU sector pinned by a central character can only carry
  linear constraints.  Nonlinear predicates force sector ambiguity.  This
  is the representation-theoretic face of the fact that LCS games, not BCS
  games, are the natural groupifiable class.
- **Exact copying lemma** (Section 5).  If a unitary finite-dimensional
  representation `rho` of a group contains `n` pairwise commuting,
  pairwise conjugate copies of a perfect group, and a fixed element `w` of
  the first copy has mark density `mu = (1 - Re tr rho(w))/2`, then
  `dim rho >= 2^(n mu)`.  Mark density is exactly conjugation-invariant, so
  "copying the bad region" does multiply the dimension demand.  Thompson's
  group `V` contains `2^k` such copies at every depth `k`.  The approximate
  version, however, saturates by Section 3 unless the `n`-fold structure is
  exactified at a cost that grows with `n`; so copying by itself yields
  profile bounds of Slofstra type, not nonhyperlinearity.

## 1. The HS-Dehn modulus

Fix a finite presentation `G = <S | R>`, `S = {s_1, ..., s_m}`.  For a
tuple `U = (U_1, ..., U_m)` of `d x d` unitaries write `||A||_2 =
(tr(A^*A)/d)^(1/2)` for the normalized Hilbert--Schmidt norm and

```text
Def_R(U) = max_(r in R) || r(U) - I ||_2.
```

For a word `w` in `S^(+-1)` write `w(U)` for its evaluation.

**Definition 1.1 (HS-Dehn modulus).**

```text
F_G(l) = sup { ||w(U) - I||_2 / Def_R(U) :
                |w| <= l,  w =_G 1,  d >= 1,  U in U(d)^m,  Def_R(U) > 0 }.
```

Tuples with `Def_R(U) = 0` are exact representations and satisfy
`w(U) = I` for every trivial word, so they need no clause.

**Lemma 1.2 (area bound).** `F_G(l) <= Dehn_G(l)` for every `l`.

*Proof.* For unitaries `A, B` one has `AB - I = A(B - I) + (A - I)`, so
`||AB - I||_2 <= ||A - I||_2 + ||B - I||_2` by unitary invariance, and
`||g r g^(-1) - I||_2 = ||r - I||_2`.  If `w =_G 1` with area `N`, then `w`
is freely equal to a product of `N` conjugates of relators or their
inverses; free reduction does not change `w(U)`; so
`||w(U) - I||_2 <= N Def_R(U)`.  Take the supremum over words of length at
most `l`. ∎

So `F_G` is a finite function `N -> [0, infinity)`, and it is bounded by a
computable function whenever `Dehn_G` is computable, i.e. (for finitely
presented `G`) whenever the word problem is solvable.  Changing the finite
presentation changes `F_G` by a reparametrization controlled by the Tietze
moves, so "computably bounded" is a property of the group.

**Definition 1.3 (computable HS length control).** `G` has computable HS
length control if there is a computable function
`Phi : N x Q_(>0) -> Q_(>=0)`, nondecreasing in its second argument, with
`Phi(l, t) -> 0` as `t -> 0^+` for each `l`, such that

```text
w =_G 1  and  Def_R(U) <= t   imply   ||w(U) - I||_2 <= Phi(|w|, t)
```

for every finite-dimensional unitary tuple `U`.  The linear case is
`Phi(l, t) = f(l) t` with `f` a computable bound for `F_G`.

Two sources of length control:

- **Area.** `Phi(l, t) = Dehn_G(l) t` works, and is computable iff the
  word problem is solvable.
- **Stability.** If `G` is HS-stable with a computable modulus, i.e. a
  computable `delta : Q_(>0) -> Q_(>0)` such that `Def_R(U) < delta(eps)`
  implies the existence of an exact representation `rho` with
  `max_s ||U_s - rho(s)||_2 <= eps`, then for a trivial word
  `||w(U) - I||_2 = ||w(U) - w(rho)||_2 <= |w| eps`.  Hence
  `Phi(l, t) = l inf{eps in Q : delta(eps) > t}` is an upper-semicomputable
  modulus, which is all Section 2 uses.

## 2. The word-problem theorem

**Theorem 2.1.** Let `G` be finitely presented, hyperlinear, with
computable HS length control.  Then the word problem of `G` is solvable.

*Proof.* Given a word `w`, run two semi-procedures in parallel.

(i) Enumerate products of conjugates of relators, freely reduce, and halt
if `w` appears.  This halts iff `w =_G 1`.

(ii) Enumerate `d >= 1`, `m`-tuples of skew-Hermitian matrices `K_i` with
entries in `Q(i)`, and rationals `t > 0`.  Put `U_i = (I - K_i)(I + K_i)^(-1)`;
these are unitary with entries in `Q(i)`, and as `K` ranges over rational
skew-Hermitian matrices the tuples `U` are dense in `U(d)^m` (the Cayley
image of all skew-Hermitian matrices is the open dense set of unitaries
without eigenvalue `-1`, and the Cayley map is continuous).  For such `U`,
`w(U)`, each `r(U)`, and the squared norms `||w(U) - I||_2^2`,
`||r(U) - I||_2^2` are exactly computable rationals.  Halt if

```text
Def_R(U) <= t     and     ||w(U) - I||_2^2 > Phi(|w|, t)^2,
```

a decidable rational inequality.

If `w =_G 1`, (ii) never halts, by the definition of `Phi`.

If `w !=_G 1`, hyperlinearity supplies, for every `eps > 0`, a dimension
`d` and a tuple `U' in U(d)^m` with `Def_R(U') < eps` and
`||w(U') - I||_2 >= c` for a constant `c > 0` depending only on the
hyperlinearity formulation (with the canonical-trace formulation one may
take `c` arbitrarily close to `sqrt 2`; with the separation formulation,
`c` is the separation constant minus `O(eps)`).  Choose rational
`t > eps` with `Phi(|w|, t) < c`, possible since `Phi(|w|, .) -> 0`.  The
set of tuples in `U(d)^m` satisfying the two strict inequalities
`Def_R(U) < t` and `||w(U) - I||_2 > Phi(|w|, t)` is open and contains
`U'`, hence contains a rational Cayley tuple, which (ii) eventually
visits.  So (ii) halts.

Exactly one of the two procedures halts, and which one decides the word
problem. ∎

The argument uses only that, for each nontrivial `w`, *some* positive
lower bound on `||w(U) - I||_2` is available along tuples of defect tending
to zero.  It never needs `sqrt 2`, and it never needs the microstates to be
accurate on more than the one word `w` and the relators.

**Corollary 2.2.** A finitely presented group with unsolvable word problem
and computable HS length control is not hyperlinear.  More precisely, for
such a group there is a nontrivial word `w` such that no sequence of
finite-dimensional tuples has relator defect tending to zero while keeping
`||w(U) - I||_2` bounded below.

**Corollary 2.3 (equivalence for hyperlinear groups).** For finitely
presented hyperlinear `G`: computable HS length control `<=>` solvable word
problem.  (`<=` is Lemma 1.2.)

**Remark 2.4 (relative form).** Let `W` be a recursive set of words such
that `{w in W : w !=_G 1}` is not recursively enumerable, and suppose the
length-control inequality holds for the trivial words of `W` only.  The
same proof shows `G` is not hyperlinear.  With `G` the Boone group of a
universal machine and `W` the family of halting commutators
`[k, t(a, b)]` over all inputs, this is the single-group form of
`hs-pcp-boone-compiler`: uniformity over inputs of one universal machine
replaces the machine-indexed family, and undecidability of the halting set
replaces the recursion theorem.

**Remark 2.5 (what is gained and what is not).** Nothing analytic is
gained: the halting-side estimate `(HPB2)` is exactly a length-control
estimate for one family of bounded-length words whose areas are
unbounded.  What is gained is conceptual hygiene.  (a) The target is a
property of one group, stated without reference to any machine inside it.
(b) The property is a named invariant, `F_G`, with a known upper bound
(area) and a known sufficient condition (stability), so partial progress
can be stated as inequalities `F_G(l) <= ...` on explicit presentations.
(c) The self-referential search is seen to be a proof device for
semi-deciding nontriviality, which the undecidability of the word problem
already supplies.

**Remark 2.6 (relation to the stable route).** HS-stable plus hyperlinear
implies residually finite (`hyperlinear-hs-stable-is-residually-finite`),
hence solvable word problem for finitely presented groups.  Theorem 2.1
weakens the hypothesis from stability to length control.  A finitely
presented HS-stable group with unsolvable word problem would satisfy
Corollary 2.2; no such group is known, and by the residual-finiteness
theorem it would already be nonhyperlinear.

## 3. Gram saturation

**Lemma 3.1.** Let `v_1, ..., v_N` be unit vectors in an inner-product
space with `|<v_i, v_j>| <= epsilon` for `i != j`.  Then

```text
dim span{v_i} >= N / (1 + (N - 1) epsilon^2),
```

and in particular `dim span{v_i} >= min(N, 1/epsilon^2) / 2`.  Conversely,
for every `epsilon > 0` and `N`, there are `N` such vectors in dimension
`O(epsilon^(-2) log N)`.

*Proof.* The Gram matrix `Gamma = (<v_i, v_j>)` is positive semidefinite with
rank equal to the span dimension, `tr Gamma = N`, and
`tr Gamma^2 = sum |Gamma_(ij)|^2 <= N + N(N - 1) epsilon^2`.  By
Cauchy--Schwarz on the nonzero eigenvalues, `rank Gamma >= (tr Gamma)^2 /
tr Gamma^2`.  For the converse take the `+-1` vectors of a binary code of
relative distance `(1 - epsilon)/2`, which exists with `2^(Omega(epsilon^2 n))`
words of length `n` by Gilbert--Varshamov, and normalize. ∎

**Corollary 3.2 (for word data).** In `M_d(C)` with the normalized HS
inner product the ambient dimension is `d^2`.  Any family of `N` group-word
evaluations `w_i(U)` with `|tr(w_i(U)^* w_j(U))| <= epsilon` for `i != j`
certifies only `d >= (min(N, 1/epsilon^2)/2)^(1/2)`.  In particular the
`4^n` Pauli words, whose exact pairwise orthogonality gives `d >= 2^n`,
certify only `d >= min(2^n, 1/epsilon)` at precision `epsilon`.

**Design consequence.** A hyperlinear microstate sequence supplies defect
`-> 0` but no rate against the dimensions in which it occurs
(`dimension-kleene-threshold-needs-amplification-envelope`).  Lemma 3.1
says that trace data at precision `epsilon` can never demand dimension
beyond `O(1/epsilon^2)`.  Hence every argument that reaches *unbounded*
dimension at *fixed* precision must pass through an exact object whose
representation theory has an integrality constraint: an exactified finite
group (Gowers--Hatami) whose relevant irreducible dimension is large, a
rank, a multiplicity.  Exactifying an `n`-fold product structure from
pairwise or relator data costs precision that grows with `n` (Slofstra's
`(n+1)^2` in the Pauli case, recorded in
`self-similar-dimension-pressure-map-2026-08-20.md`).  This is the exact
place where "dimension explosion" routes pay the area, and it is why the
compiler target is a uniform stability statement for an *infinite*
structure, not a better counting argument.

## 4. Central pinning forbids nonlinear predicates

**Lemma 4.1.** Let `H` be a finite group and `J in Z(H)` an involution.
Suppose `pi` is the unique irreducible representation of `H` with
`pi(J) = -I`.  Then `chi_pi(h) = 0` for every `h notin {1, J}`, and
`(dim pi)^2 = |H|/2`.

*Proof.* The central idempotent `(1 - J)/2` cuts `C[H]` into a summand of
dimension `|H|/2` isomorphic to the direct sum of `M_(dim rho)` over the
irreducibles with `rho(J) = -I`; by uniqueness this summand is
`M_(dim pi)`, so `(dim pi)^2 = |H|/2`.  Orthogonality of characters gives
`|H| = sum_h |chi_pi(h)|^2 >= |chi_pi(1)|^2 + |chi_pi(J)|^2 = 2 (dim pi)^2 =
|H|`, forcing `chi_pi = 0` off `{1, J}`. ∎

**Proposition 4.2.** In the situation of Lemma 4.1, let `x_1, ..., x_k in H`
be commuting involutions and `E = <x_1, ..., x_k>`.  Then the joint
spectrum of `(pi(x_1), ..., pi(x_k))` is an affine subspace of `F_2^k`
(identifying `{+1, -1}` with `F_2`): it is the set of all characters of `E`
if `J notin E`, each with multiplicity `dim pi / |E|`, and the set of
characters with `lambda(J) = -1` if `J in E`, each with multiplicity
`2 dim pi / |E|`.  The same holds in every finite-dimensional
representation of any group `Gamma >= H` in which `J` acts as `-I`, since
such a representation restricts to a multiple of `pi`.

*Proof.* The multiplicity of `lambda in E^` in `pi|_E` is
`(1/|E|) sum_(e in E) chi_pi(e) conj(lambda(e))`.  By Lemma 4.1 only `e = 1`
(and `e = J` if `J in E`) contribute, giving `dim pi / |E|` in the first
case and `(dim pi / |E|)(1 - lambda(J))` in the second.  A character of
`E` is an assignment `s in {+1, -1}^k` satisfying the `F_2`-linear
relations among the `x_i`; the condition `lambda(J) = -1` is one further
affine equation. ∎

**Consequence.** A finite "CPU" group whose predicate sector is pinned by
a central character (the design that makes the Pauli and Clifford
compilers robust: any approximate representation with `J` close to `-I`
on positive density is close to a multiple of `pi`) can only enforce
*linear* constraints on commuting involutions.  The sector `pi_S` of
`finite-predicate-signed-permutation-sector` for a nonlinear `S` is
therefore never the unique `J = -1` sector of its group: other irreducibles
with the same central character exist, and nothing algebraic prefers
`pi_S`.  Sector selection for nonlinear predicates must use a
finite-dimension-specific mechanism, and by
`regular-trace-blocks-exact-local-predicate-return` it cannot be an exact
identity.  This is the group-theoretic reason the exact groupification of
a BCS with nonlinear constraints (`bcs-to-lcs-exact-support-gap`) is hard
while LCS solution groups are immediate, and the reason Taller--Vidick's
reduction passes through 3-XOR with a noisy long code.

## 5. The exact copying lemma and Thompson's `V`

**Lemma 5.1.** Let `rho` be a finite-dimensional unitary representation of
a group `Gamma` on `C^d`.  Suppose `A_1, ..., A_n <= Gamma` are pairwise
commuting subgroups with `A_i = g_i A_1 g_i^(-1)`, and `A_1` is perfect.
Let `w in A_1` and `mu = (1 - Re tr rho(w))/2 in [0, 1]` (normalized
trace).  Then

```text
d >= 2^(n mu).
```

*Proof.* The map `A_1 x ... x A_n -> Gamma` is a homomorphism, so `rho`
restricts to a unitary, hence completely reducible, representation of the
product, whose irreducible constituents are tensor products
`rho_1 (x) ... (x) rho_n` of irreducibles of the factors.  Write
`rho|_(A_1 x ... x A_n) = sum_b m_b (rho^b_1 (x) ... (x) rho^b_n)` with
weights `p_b = m_b dim(b)/d`, `sum_b p_b = 1`.  Put `w_i = g_i w g_i^(-1) in
A_i`.  Since the normalized trace is conjugation-invariant and
multiplicative on tensor products, `mu(w_i) = mu(w) = mu` and
`mu(w_i) = sum_b p_b mu_(rho^b_i)(w)`, where `mu_sigma(w) = (1 - Re tr
sigma(w))/2 <= 1` vanishes when `sigma` is trivial.  Summing over `i`,

```text
n mu = sum_b p_b sum_i mu_(rho^b_i)(w) <= sum_b p_b N_b,
```

`N_b` the number of nontrivial factors of `b`.  So some `b` has
`N_b >= n mu`.  A nontrivial irreducible of a perfect group has dimension
at least `2` (a one-dimensional representation is a character, trivial on
`[A_1, A_1] = A_1`), so `d >= dim(b) >= 2^(N_b) >= 2^(n mu)`. ∎

**Example 5.2 (Thompson's `V`).** `V` is perfect, and for every `k` it
contains the `2^k` pairwise commuting subgroups `V_x` (elements supported
in the cylinder `x`, `|x| = k`), each isomorphic to `V` and all conjugate
in `V` (some element of `V` maps any cylinder onto any other).  Lemma 5.1
gives, for any finite-dimensional unitary representation and any `w in
V_x`, `d >= 2^(2^k mu)` for all `k`, so `mu = 0`: a quantitative form of
"V has no nontrivial finite-dimensional unitary representations".  In the
regular representation all copies have `mu = 1/2`; the lemma is not
violated because `d` is infinite.

**What this does and does not do for the programme.** The lemma is the
exact form of "copying the bad region multiplies the cost": mark density
is exactly conjugation-invariant, so deep copies are as bad as the shallow
one, and `n` commuting copies at density `mu` need `2^(n mu)` dimensions.
This is the mechanism the user-level idea points at, and it is correct.
Its approximate version, however, is governed by Section 3: the block
decomposition is an exact object, and recovering it from approximate
commutation and approximate conjugation among `n` copies requires
exactifying the `n`-fold product at a precision that degrades with `n`
(for `V` the relevant relators at depth `k` have area growing with `k`).
Choosing the depth `k` at which the precision `delta` of a microstate still
allows exactification yields a lower bound of the form
`d >= exp(c delta^(-a))` for the hyperlinear profile of `V`, the same shape
as Slofstra's Clifford--HNN profile, and a finite profile is compatible
with hyperlinearity.  A finite-dimensional model can be "regular-like"
(independent copies of density `1/2`) down to depth about `log log d` and
pay only the area-weighted defect of the relations connecting that depth
to the root.  Turning the copying lemma into nonhyperlinearity therefore
requires exactly the missing ingredient of every other route: exactifying
an unboundedly large structure at fixed precision, i.e. uniform stability.

## 6. Where this leaves the programme

1. The self-referential machine is a proof device, and the undecidability
   of a fixed word problem replaces it (Theorem 2.1).  The open target is
   `unsolvable-word-problem-group-with-computable-hs-dehn-modulus`.
2. Every "detector" that is an exact algebraic identity is killed by the
   regular representation; every detector that is approximate trace data
   saturates at `1/epsilon^2`.  What remains is exactification plus
   integrality, i.e. stability of an infinite structure with uniform
   constants.  Length control is the minimal such statement, and the Dehn
   function is the trivial (area-paying) instance of it.
3. A concrete way to make partial progress statable: compute or bound
   `F_G` for explicit presentations with large Dehn functions and solvable
   word problems (`BS(1,2)`, Baumslag--Gersten, iterated HNN towers),
   asking whether `F_G` can be linear while `Dehn_G` is exponential or
   worse.  Stable examples give linear `F_G`.  A machine group whose
   configuration transport is length-controlled would be the compiler.

## 7. Calibration: the HS-Dehn modulus of a centralized cyclic distortion

`Gamma = <a, t, k | t a t^(-1) = a^2, [k, a] = 1>`, `w_n = [k, t^n a t^(-n)]`.
Model in dimension `L+1`: `a = diag(e^(2 pi i 2^(-x)))`, `t` the cyclic
shift, `k` a `pi/4` rotation across `e_0, e_L`.  Then `Def(U_L) =
|1 - e^(2 pi i/2^L)|/sqrt(L+1)` and `||w_n(U_L) - I||_2 / Def(U_L) ->
2^(n-1)`, matching the area `~2^n` up to a factor four, at defect tending to
zero (`experiments/hs_dehn_centralizer_family.py`; `ratio/2^n = 0.500` for
`L = 8..24`, `n <= 12`).  Hence halting-style soundness with thresholds
`(delta, alpha)` fails for `n >= log_2(alpha/delta) + O(1)` in this family:
runtime-dependence of the constants is forced whenever the distortion runs
through an abelian direction.

Two consequences drawn in `centralized-cyclic-distortion-hs-dehn-tracks-area`
and the Attempts of `unsolvable-word-problem-group-with-computable-hs-dehn-
modulus`: a Kazhdan Rips kernel removes the kernel's distortion entirely but
hands the mark to an approximate representation of the quotient on the
multiplicity bundle over `Irr(N)`; and Taller--Vidick soundness is itself
linear length control (`||J(U) - I||_2 <= 17 Def(U)`) for the solution
groups of nonhalting inputs, so the phenomenon "defect beats area" is
realized by PCP-derived presentations, through averaging over an expanding
constraint family rather than along one derivation.

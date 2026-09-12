# Toms--Winter: strict comparison already compares projections in the tracial ultrapower (2026-09-12)

Lane `toms-winter`.  This artifact carries the proof behind
`strict-comparison-compares-ultrapower-projections` and the reduction it feeds.
Nothing here proves or refutes the Toms--Winter conjecture.

## Sources and what was read

All PDFs were fetched and converted to text on MSI
(`/projects/standard/hsiehph/sauer354/lit/toms-winter/`, ghostscript `txtwrite`).

- J. Castillejos, S. Evington, A. Tikuisis, S. White, *Uniform property Gamma*,
  arXiv:1912.04207 (IMRN 2022).  **Read: introduction, pages 3--4, and Section 6
  pages 32--33.**
  - Theorem A: "The Toms--Winter conjecture holds among separable, simple,
    unital, nuclear, non-elementary C*-algebras which have uniform property
    Gamma."  The paper says this is extracted from Theorem 5.6.
  - Question C (refuted since by Toms, below).
  - The Bauer-simplex form of Question C is triviality of the W*-bundle over
    the extreme boundary.  By Ozawa's trivialisation theorem this is equivalent
    to uniform property Gamma.
- J. Carrion, J. Castillejos, S. Evington, J. Gabe, C. Schafhauser, A. Tikuisis,
  S. White, *Tracially complete C*-algebras*, arXiv:2310.20594v6.  **Read:
  Section 1.4 (steps (i)--(iii), Question 1.5 and the paragraph after it) and
  Section 7.1 up to Lemma 7.3.**
  - Step (ii): "For the uniform tracial completion of a nuclear C*-algebra with
    no finite dimensional representations, CPoU is equivalent to property
    Gamma."
  - Question 1.5: "Does every amenable type II_1 factorial tracially complete
    C*-algebra satisfy property Gamma?"
  - After it: "It remains mysterious whether one should expect a positive
    answer in general, or whether strict comparison for a C*-algebra A would
    imply property Gamma for its uniform tracial completion which, if true,
    would establish the Toms--Winter conjecture."
  - Section 7: with CPoU, reduced products have real rank zero (Proposition
    7.2) and comparison of projections with respect to limit traces, and
    Theorem 7.17 compares projections by designated traces.
- A. S. Toms, *Schubert calculus and uniform property Gamma*, arXiv:2606.12188v2.
  **Read: pages 1--4 and Section 6 (Lemma 2, Theorems 2 and 3).**
  - The obstruction to Gamma is a pair of projections `P`, `Q` in a matrix
    amplification of the uniform tracial completion.  They agree on every
    designated trace, and `P` is not Murray--von Neumann subequivalent to `Q`.
  - Theorem 2 proves this by approximating a putative partial isometry at a
    finite stage.  Point-fibre traces extend to the limit (Lemma 2), so the
    approximant is a nowhere-zero bundle map `p_i -> q_i`, which total
    degeneracy forbids.
  - Theorem 3 converts this into failure of uniform Gamma: Gamma gives CPoU
    for the completion, and CPoU compares projections by traces.
- A. Vaccaro, *Stable rank one, tracial local homogeneity and uniform property
  Gamma*, arXiv:2604.24682v2.  **Read: pages 1--3.**
  - Theorem B: stable rank one plus tracially locally finite nuclear dimension
    gives uniform Gamma.
  - The chain behind it:
    1. stable rank one gives tracial approximate oscillation zero, equivalently
       real rank zero of the tracial ultrapower (Fu);
    2. that gives tracial almost divisibility (Vaccaro, Theorem 2.2);
    3. with tracially locally finite nuclear dimension, that gives uniform
       Gamma (Winter, through CETW22 Theorem 5.5).
- K. Mommaerts, arXiv:2606.12134v1: **abstract and pages 1--2 read.**  This is
  the first non-locally-trivial W*-bundle with fixed II_1 factor fibres.  The
  obstruction, failure of uniform spectral gap, concerns non-Gamma fibres.
- I. Farah, A. Vaccaro, arXiv:2501.01272v3: **abstract read.**  It gives
  continuous-valued forms of "subequivalence of projections in II_1 factors is
  determined by traces", via Michael's selection theorem.
- CETWW, *Nuclear dimension of simple C*-algebras*, arXiv:1901.05853.  **Only
  the use of Lemma 4.7 in CETW footnote 28 was read.**  There, strict comparison
  of a relative commutant algebra is obtained from CPoU of a Z-stable nuclear
  algebra.  The theorem below uses no CPoU and no Gamma.

## 0. Conventions

- **The algebra.** `A` is unital, simple, exact and non-elementary, with `T(A)`
  nonempty.  For exact `A`, quasitraces are traces (Haagerup).
- **Strict comparison.** For `a, b in M_infty(A)_+`, if `d_tau(a) < d_tau(b)`
  for every `tau in T(A)`, then `a` is Cuntz subequivalent to `b`.
- **Traces on matrices.** They are unnormalized: `tau` means `tau tensor Tr_k`
  on `M_k(A)`.
- **The uniform tracial ultrapower.** `A^omega` is `l^infty(A)` modulo the
  sequences with `lim_omega sup_{tau in T(A)} ||x_n||_{2,tau} = 0`, and
  `M_k(A^omega) = M_k(A)^omega`.
- **Limit traces.** A limit trace is `sigma((x_n)) = lim_omega tau_n(x_n)` for
  a sequence `tau_n in T(A)`.
- **The completion.** The uniform tracial completion `M` embeds in `A^omega`
  (CCEGSTW), and designated traces of `M` induce limit traces.

## 1. Theorem

**Theorem.** Let `A` be as in Section 0 with strict comparison, `k >= 1`, and
let `p, q in M_k(A^omega)` be projections with `sigma(p) <= sigma(q)` for every
limit trace `sigma`.  Then there is `v in M_k(A^omega)` with

```text
v* v = p,        v v* <= q.
```

In particular this holds for projections `p, q in M_k(M)` with `tau(p) <= tau(q)`
for all `tau in T(A)`.  Equality of traces is allowed.  No CPoU, uniform Gamma,
nuclearity or dimension hypothesis is used.

### Proof

**Step 1: lifts.**
- Represent `p` and `q` by positive contractions `a_n, b_n in M_k(A)`: lift, then
  clip with functional calculus, which commutes with the quotient map.
- Put
  - `eps_n = sup_tau tau(a_n - a_n^2) + sup_tau tau(b_n - b_n^2)`;
  - `eta_n = max(0, sup_tau (tau(a_n) - tau(b_n)))`.
- `lim_omega eps_n = 0`.  For positive `x in M_k(A)`,
  `tau(x) <= k^(1/2) ||x||_{2,tau}`, and `p - p^2 = 0 = q - q^2`.
- `lim_omega eta_n = 0`.  Suppose instead `eta_n > c/2 > 0` on a set in `omega`.
  Choose `tau_n` there with `tau_n(a_n) - tau_n(b_n) > c/2`, and arbitrary
  `tau_n` elsewhere.  The limit trace `sigma = lim_omega tau_n` then has
  `sigma(p) - sigma(q) >= c/2`, a contradiction.

**Step 2: rank estimates.**
- For `0 <= t <= 1`,
  - `1_(1/2,1](t) <= t + 2t(1-t)`;
  - `t <= 1_(1/2,1](t) + 2t(1-t)`;
  - `t <= 1_(delta,1](t) + delta`.
- Integrate against the spectral measure of a positive contraction `x` in the
  GNS von Neumann algebra of `tau`.  For `x in M_j(A)`:

```text
d_tau((x-1/2)_+) <= tau(x) + 2 tau(x-x^2),
d_tau((x-1/2)_+) >= tau(x) - 2 tau(x-x^2),
d_tau((x-delta)_+) >= tau(x) - j delta.
```

**Step 3: small witnesses.**
- A simple non-elementary C*-algebra is not type I.  So by Glimm's lemma, for
  each `l` there is a nonzero *-homomorphism `C_0((0,1]) tensor M_l -> A`
  (standard; not re-read here).
- The image `c_l` of `t tensor e_11` is a positive contraction with `l` pairwise
  orthogonal Cuntz-equivalent copies in `A`, so `d_tau(c_l) <= 1/l` for all
  `tau`.
- Every trace on the simple unital `A` is faithful and `T(A)` is compact, so
  `m_l = inf_tau tau(c_l) > 0`.
- Put `delta_l = m_l/4`.  Step 2 gives `d_tau((c_l - delta_l)_+) >= 3m_l/4`.

**Step 4: strict comparison at one index.**  Fix `l` and `n` with
`eta_n + 4 eps_n < m_l/2`, and put

```text
a' = (a_n - 1/2)_+ (+) 0,      b' = (b_n - 1/2)_+ (+) (c_l - delta_l)_+    in M_(k+1)(A).
```

By Step 2, for every `tau`,

```text
d_tau(a') <= tau(b_n) + eta_n + 2 eps_n  <  tau(b_n) - 2 eps_n + 3 m_l/4  <= d_tau(b').
```

- By strict comparison, `a'` is Cuntz subequivalent to `b'`.
- By Rordam's lemma (if `a` is Cuntz below `b` then `(a-e)_+ = s* b s` for some
  `s`, for each `e > 0`; standard, not re-read here), with `e = 1/4` there is
  `s` with `(a_n - 3/4)_+ (+) 0 = s* b' s`.
- Put `x = b'^(1/2) s`.  Then `x* x = (a_n - 3/4)_+ (+) 0`, `||x|| <= 1/2`, and
  `x x*` lies in `her(b')`.

**Step 5: compress away the witness.**  Let `e = 1_k (+) 0`.
- Since `x = x e`, the element `w = e x e = e x` in `M_k(A)` satisfies
  `w* w = x* x - x*(1-e) x`.
- The positive element `z = (1-e) x x* (1-e)` lies in `her((c_l - delta_l)_+)`
  and has norm at most `1/4`.  So `tau(x*(1-e)x) = tau(z) <= d_tau(c_l)/4 <= 1/(4l)`
  for every `tau`.
- Let `g` be continuous with `g = 0` on `[0,1/4]` and `g = 1` on `[1/2,1]`.  Then
  `g(b_n)(b_n - 1/2)_+^(1/2) = (b_n - 1/2)_+^(1/2)`.  So
  `w w* = e x x* e = g(b_n) w w* g(b_n)`.

**Step 6: diagonal sequence.**
- Let `S_l = {n : eta_n + 4 eps_n < m_l/2}`, which lies in `omega`.  Put
  `T_l = S_1 cap ... cap S_l`, and `l(n) = max{l <= n : n in T_l}` (0 if none).
- Then `l(n) >= L` on `T_L cap [L, infty)`, so `lim_omega l(n) = infty`.
- Define `w_n` by Step 5 with `l = l(n)`, or `w_n = 0` when `l(n) = 0`, and let
  `w = [(w_n)]`.
- The error terms satisfy
  `||x_n*(1-e)x_n||_{2,tau}^2 <= ||x_n*(1-e)x_n|| tau(x_n*(1-e)x_n) <= 1/(16 l(n))`
  uniformly in `tau`.  So in `M_k(A^omega)`:

```text
w* w = (p - 3/4)_+ = p/4,        w w* = g(q) w w* g(q) = q w w* q.
```

So `v = 2w` is a partial isometry with `v*v = p` and `vv* <= q`.  QED

If `sigma(p) = sigma(q)` for all limit traces, then `q - vv*` is a positive
element with every limit trace zero.  By the compactness argument of Step 1,
it is zero in `M_k(A^omega)`, so `p` and `q` are equivalent.

## 2. Consequences

**2.1 Projection-comparison certificates against Gamma cannot coexist with
strict comparison.**
- Toms's certificate for his simple algebra `B` (Theorem 5) and for the
  non-simple limit (Theorem 2) is a pair `P, Q` in a matrix amplification of
  the completion.  The two agree on all traces and are not equivalent.
- Both proofs use only this: a putative partial isometry has finite-stage
  contractions close to it in uniform 2-norm.  A partial isometry in
  `M_k(A^omega)` also provides these, through representing sequences and norm
  density of the stages.
- Point-mass survival (Lemma 2 and Proposition 4(3)) then produces a
  nowhere-zero bundle map, which total degeneracy forbids.
- So `B` is simple, exact and non-elementary, and has no partial isometry
  between `P` and `Q` in `M_k(B^omega)`.  By the Theorem, `B` fails strict
  comparison.  This is a direct argument, independent of Winter's purity
  theorem and CETWW.
- More generally, no Gamma obstruction that works by non-subequivalent
  projections with dominated traces can live in a strict-comparison algebra,
  whatever its building blocks.

**2.2 The residual question.**  With CETW Theorem A, the unital Toms--Winter
conjecture follows from:

```text
(Q_tr)  A unital simple separable nuclear non-elementary, and projections in
        every M_k(A^omega) compared by limit traces  =>  A has uniform Gamma.
```

- The hypothesis of `(Q_tr)` concerns only the tracial ultrapower.
- For a tracially complete algebra with CPoU the hypothesis holds (CCEGSTW
  Theorem 7.17).  So `(Q_tr)` asks whether this consequence of CPoU already
  forces CPoU, for completions of nuclear algebras.

**2.3 The locally finite nuclear dimension locus.**
- Let `A` have locally finite nuclear dimension and strict comparison.  Then
  `A` is Z-stable iff rank density holds, by the established chain
  `rank-density-and-strict-comparison-give-purity` plus Winter's purity
  theorem.
- Rank density is the existence, in `A^omega`, of projections with every
  continuous affine trace profile (`rank-density-is-quadratic-trace-selection`).
- A counterexample on this locus therefore has a tracial ultrapower in which
  projections are compared perfectly by traces, yet some trace profiles have no
  projections at all: comparison without existence.

## 3. Attempts on (Q_tr)

- **Unconditional cells.**  Uniform Gamma holds without the hypothesis in
  these cases:
  - compact finite-dimensional extreme boundary;
  - stable rank one with tracially locally finite nuclear dimension (Vaccaro,
    Theorem B).
- **CPoU gluing.**  CETWW produce CPoU from Gamma by averaging with
  approximately central halving projections.  Comparison gives partial
  isometries between projections that already exist.  It supplies neither the
  projections nor their centrality.
- **Real rank zero.**  On the tracially locally-finite-nuclear-dimension locus,
  real rank zero of `A^omega` gives Gamma (Vaccaro Theorem 2.2 plus Winter).
  So `(Q_tr)` there follows from "comparison forces real rank zero of the
  tracial ultrapower", the converse of CCEGSTW Proposition 7.2.  No argument is
  known.
- **W*-bundles.**  For a Bauer simplex, `(Q_tr)` asks whether a W*-bundle with
  hyperfinite II_1 fibres, arising as a completion and comparing projections in
  its reduced powers, is trivial (Ozawa).  The only known non-local-triviality
  obstruction (Mommaerts) needs non-Gamma fibres.
- **Mechanisms excluded as counterexamples.**
  - Villadsen Euler-class gaps: a small trivial projection not below a larger
    twisted one.
  - Toms's Thom--Porteous degeneracy loci.

  Both produce non-subequivalent projections with dominated traces.  A
  counterexample to `(Q_tr)` among strict-comparison algebras needs an
  obstruction to central halving that no pair of projections detects.

## 4. One cycle on locally finite nuclear dimension: existence versus centrality

Throughout this section `A` is unital, simple, exact, non-elementary, with
strict comparison and locally finite nuclear dimension.

**4.1 Rank density plus comparison gives unital matrix algebras in `A^omega`.**
Suppose rank density holds.
- By the quadratic selection equivalence there is a projection `e` in `A^omega`
  with `sigma(e) = 1/k` for every limit trace.  It is represented by near
  projections `b_n` with `sup_tau |tau(b_n) - 1/k| -> 0` and defect tending to 0.
- By the Theorem, `e <~ 1 - e`.  Iterate: `e_j <= 1 - (e_1 + ... + e_(j-1))`,
  which has trace `(k-j+1)/k >= 1/k`, and equal traces give equivalence.
- After `k` steps `1 - sum e_j` has zero trace, hence vanishes in `A^omega`.
- The partial isometries give matrix units of a unital `M_k` inside `A^omega`.

This copy is not central.  Uniform Gamma needs the central version, and
CETW's uniform McDuff property is the central unital version.

**4.2 What is new, and what is not.**
- On this locus, strict comparison plus rank density already gives purity
  and then Z-stability, by the established chain.  So 4.1 adds nothing to
  Toms--Winter on this locus.
- It locates the two failure modes separately.
  - **Existence failure** (no rank density): the tracial ultrapower has no
    projection of some continuous profile.
  - **Centrality failure** (rank density, no Gamma): matrix algebras exist
    in `A^omega` but none is approximately central.  With strict comparison
    this mode is impossible on the locus.
- So a Toms--Winter counterexample with locally finite nuclear dimension is
  an existence failure.  That is exactly failure of approximate integer
  division of ranks of layer-cake elements (`rank-density-from-approximate-rank-division`).

**4.3 Why comparison does not divide.**  Let `Q` be a projection in `A^omega`
with profile `L tau(a)`, obtained from the layer-cake element `b_L`.
- Division asks for `R <= Q` with `L` orthogonal equivalent copies below `Q`
  and profile `tau(a) - epsilon`.
- At a single extreme trace this is easy: the GNS factor is the hyperfinite
  II_1 factor, and Kaplansky density approximates there.
- Glimm's lemma inside the hereditary subalgebra of a representing near
  projection gives a nonzero divisor, but its profile is uncontrolled.
- Greedy accumulation of such divisors increases the profile by uncontrolled
  amounts at different traces.  Countable saturation of `A^omega` realizes
  countably many conditions only when each finite set of them is approximately
  satisfiable, and "profile at least `tau(a) - epsilon` everywhere" is the
  statement itself.
- The Theorem supplies uniqueness, so any two candidate divisors with ordered
  profiles are nested up to equivalence.  It never supplies a candidate.

So the lfnd crux is unchanged:

```text
(D)  strict comparison  =>  for every b in M_infty(A)_+, L, eta there is y with
     |L d_tau(y) - d_tau(b)| < eta for all tau.
```

The only new constraint is that any obstruction to `(D)` must coexist with
perfect projection comparison in `A^omega`.  A certificate of the form "these
two near projections cannot be compared" is ruled out; the certificate has to
be "no near projection of this profile exists".

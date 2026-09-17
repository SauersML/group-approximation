# A Maharam-type zero-one law for quasitraces (sw-086, 2026-09-17)

Lane: reframer on `stw99-problem-i-quasitraces-are-traces`.

## 0. Summary

Let `M` be a type `II_1` AW*-factor with its normalized quasitrace `tau`
(`tau = D` on projections, `D` the dimension function). Define the **minorant
mass**

```text
S_M(1) = inf { sum_i c_i D(p_i) :  finitely many c_i >= 0, projections p_i,  sum_i c_i p_i >= 1 }.
```

**Theorem A (zero-one law).** `S_M(1)` is `0` or `1`. It is `1` exactly when `M`
is a W*-factor. The following are equivalent:

1. `M` is a W*-algebra;
2. `tau` is linear (a trace);
3. some nonzero positive linear functional `phi` on `M` satisfies `phi(p) <= D(p)`
   for every projection `p`;
4. `S_M(1) > 0`;
5. there is a constant `C` with `tau(a_1+...+a_N) <= C (tau(a_1)+...+tau(a_N))`
   for all `N` and all `a_j in M_+`;
6. there is a constant `C` with `tau_N(G) <= C tau_N(E_N(G))` for all `N` and all
   `G in M_N(M)_+`. Here `tau_N` is the unique quasitrace extension with
   `tau_N(x (x) e_11) = tau(x)`, and `E_N` is the diagonal pinching.

When these fail, the constants in 5 and 6 are unbounded and no nonzero positive
functional lies below `D`.

**Corollary B (Problem I as non-pathology).** The following are equivalent:

- (I) every bounded quasitrace on a unital C*-algebra is a trace;
- (II) every normalized quasitrace `q` on a unital C*-algebra `A` dominates a
  nonzero positive linear functional, i.e. `0 != phi <= q` on `A_+`;
- (III) every such `q` is C-subadditive on finite sums for some constant `C = C(q)`.

**Corollary C (shape of a counterexample).** If `M` is not W*, then for every
`eps > 0` there is a finite weighted projection cover `sum_i c_i p_i >= 1` with
`sum_i c_i D(p_i) < eps`. Any such cover:

- has more than `1/eps` terms;
- cannot be split into `k <= 1/eps` classes of pairwise commuting projections.

**Corollary D (Jensen collapse).** `M` is not W* iff for every `eps > 0` there are
`N` and `G in M_N(M)_+` with `tau_N(E_N G) < eps tau_N(G)`. Moreover, `G` can be
taken to be the Gram matrix of a cover.

This is a noncommutative analogue of the Maharam problem.

- In a counterexample, `D` would be a *pathological* additive measure on the
  projection lattice. It would be completely additive on every Boolean
  subalgebra, yet dominate no nonzero positive functional.
- Talagrand's pathological submeasures (Ann. Math. 2008) are commutative and not
  additive. Commutative additive measures are never pathological.
- Theorem A says the pathology cannot be partial: there is no intermediate mass
  `0 < S_M(1) < 1`.

### 0.1 Why this is not a restatement

These are the nearest graph results.

- **Certificates artifact, Proposition 4.1** (`stw01-certificates-products-universal-tests-2026-09-11.md`).
  It gives trace ⟺ subadditive ⟺ superadditive, all with constant `1`. Its
  complement trick does not survive a constant `C > 1`. Theorem A 5 and 6 allow
  any constant, and 3 and 4 allow an arbitrarily small linear mass.
- **The rr0-witness artifact** (§4.3, Corollary 4.4, and §4 item 1).
  - Its route asks for a *faithful state*, which is conditional on Wright 1975.
  - It dies at "dimension-free constants", with superadditivity iterates carrying
    a factor `N`.
  - Here any constant suffices, the conclusion is unconditional (Gow Cor. 3.10,
    read with proof as in the three-projection artifact (I4)), and the functional
    need not be faithful.
- **`stw01-quasitrace-crux-is-awstar-factor-w-star`.** It reformulates Problem I
  through large W*-corners or faithful CAP states. Here the minorant is found by
  Hahn–Banach from `D` itself, and the zero-one law is new.

### 0.2 Paradigm answers

- **Why this succeeds where the recorded routes died.** Those routes needed an
  exact inequality, or a dimension-free constant in a fixed direction. Here the
  invariant changes from linearity of `tau` to a *convex* quantity, the mass of
  the best linear minorant. Hahn–Banach produces the minorant. Complete
  additivity of `D` makes it CAP. Unitary invariance of `D` spreads any positive
  mass over all projections. No constant is ever needed.
- **First falsifiable step.** Check that the Hahn–Banach minorant is CAP and that
  its unitary conjugates separate projections. Both are done in §2.
- **Calibration.**
  - In `M_n`, and in `II_1` W*-factors, `S = 1`.
  - For commutative algebras, `S = 1`.
  - In exact algebras (Haagerup), `q` is a trace, so `S = 1`.
  - Talagrand's commutative pathological submeasures are not additive, so they
    fall outside the hypotheses. Nothing known-false is "proved".

## 1. Inputs

- **(G1)** Gow, arXiv:2601.04431v2, Thm 4.11 (`stw01-kaplansky-2q-pedersen-retract-equivalence`):
  (I) holds iff every type `II_1` AW*-factor is W*.
- **(G2)** Gow, Cor. 3.10 (after Pedersen Thm 3.9.4), as recorded in
  `research/artifacts/stw01-three-projection-universal-test-2026-09-12.md`, (I4).
  An AW*-algebra with a separating family of states that are completely additive
  on projections (CAP) is W*.
- **(G3)** A `II_1` AW*-factor `M` has a unique normalized quasitrace `tau`. On
  projections it is the dimension function `D`, which is completely additive on
  orthogonal families. Source: Gow §2.3 after Def. 2.23, recorded in the same (I4).
- **(D)** Kaplansky dimension theory for finite AW*-factors of type `II_1`:
  - `D(p) = 0` iff `p = 0`;
  - `D` takes every value in `[0,1]`;
  - `D(e) = D(f)` iff `e ~ f`;
  - `e ~ f` implies `1-e ~ 1-f` (finiteness), hence `e` and `f` are unitarily
    equivalent.
- **(H)** Haagerup, arXiv:1403.7653, Cor. 3.4 and Lemma 3.5 (pp. 7–8 of the arXiv version, read with proofs). A quasitrace is order preserving, extends uniquely
  to every `M_N(A)`, and satisfies `tau(a+b)^{1/2} <= tau(a)^{1/2} + tau(b)^{1/2}`
  on `A_+`.
- **(L)** A quasitrace is linear on every abelian C*-subalgebra.

## 2. Proof of Theorem A

Throughout, `M` is a `II_1` AW*-factor and `tau`, `D` are as in (G3). A *cover* is
a finite family `(c_i, p_i)` with `c_i >= 0`, `p_i` projections and
`sum c_i p_i >= 1`. Its *mass* is `sum c_i D(p_i)`. By (L),
`tau(c_i p_i) = c_i D(p_i)`.

### 2.1 The sublinear functional

For `a in M_sa` put

```text
S(a) = inf { sum_i c_i D(p_i) : c_i >= 0, p_i projections, sum_i c_i p_i >= a }.
```

The empty family is allowed and has sum `0`.

- **Finite.** The family `(||a||, 1)` is admissible, so `S(a) <= max(||a||, 0)`.
  Every mass is `>= 0`, so `S(a) >= 0`.
- **Zero on negatives.** If `a <= 0` the empty family is
  admissible, so `S(a) = 0`.
- **Positively homogeneous.** For `t > 0`, scale all `c_i` by `t`.
- **Subadditive.** If `(c_i, p_i)` is admissible for `a` and `(d_k, q_k)` for `b`,
  the concatenated family is admissible for `a+b` and its mass is the sum. So
  `S(a+b) <= S(a) + S(b)`.

So `S` is a sublinear functional on the real vector space `M_sa`, with
`S(1) = S_M(1)` and `S(p) <= D(p)` for every projection `p` (use the family
`(1, p)`).

### 2.2 (4) ⟹ (1)

Assume `s := S(1) > 0`.

**Step 1: a minorant of mass `s`.** On `R 1` put `phi_0(t 1) = t s`.

- For `t >= 0`, `phi_0(t1) = S(t1)`.
- For `t < 0`, `phi_0(t1) < 0 = S(t1)`.

So `phi_0 <= S` on `R 1`. By Hahn–Banach there is a real-linear
`phi : M_sa -> R` with `phi <= S` and `phi(1) = s`.

- If `a >= 0` then `phi(-a) <= S(-a) = 0`, so `phi` is positive.
- Extend `phi` complex-linearly to `M`. It is a positive functional with
  `||phi|| = phi(1) = s`.
- For every projection `p`, `phi(p) <= S(p) <= D(p)`.

**Step 2: `phi` is CAP.** Let `(p_i)_{i in I}` be orthogonal projections with
supremum `p`, and let `F ⊂ I` be finite. Then `q_F = p - sum_{i in F} p_i` is a
projection, and by finite additivity of `D`,

```text
0 <= phi(p) - sum_{i in F} phi(p_i) = phi(q_F) <= D(q_F) = D(p) - sum_{i in F} D(p_i).
```

By (G3) the right side tends to `0` along finite `F`. So
`phi(p) = sum_i phi(p_i)`.

**Step 3: unitary conjugates separate projections.** For a unitary `u`, put
`phi_u = phi ∘ Ad(u)`. Since `Ad(u)` is a *-automorphism, it preserves
orthogonality and suprema. So `phi_u` is again a CAP positive functional of norm
`s`.

Let `p != 0` be a projection.

1. By (D), `D(p) > 0`. Choose `m` with `1/m <= D(p)` and a subprojection
   `p' <= p` with `D(p') = 1/m`. It exists because `D` takes all values, and
   `D(e) <= D(p)` gives `e ≾ p`.
2. Choose orthogonal projections `e_1, ..., e_m` with `D(e_j) = 1/m` and
   `sum e_j = 1`. Pick them successively below the complement, using that `D`
   takes all values in every corner. The last one is the remainder.
3. By (D), `e_j ~ p'` and `e_j = u_j p' u_j*` for unitaries `u_j`.

Hence

```text
sum_j phi_{u_j*}(p') = sum_j phi(u_j p' u_j*) = phi(1) = s > 0,
```

so `phi_{u_j*}(p) >= phi_{u_j*}(p') > 0` for some `j`.

Every nonzero `a in M_+` dominates `eps e` for some nonzero spectral projection
`e`. It lies in a MASA `C(X)` with `X` Stonean, and (I5) of the three-projection
artifact applies. So `{ phi_u / s : u unitary }` is a separating family of CAP
states.

**Step 4.** By (G2), `M` is a W*-algebra. ∎(4 ⟹ 1)

### 2.3 The remaining implications

- **(1) ⟹ (2).** A `II_1` W*-factor has a faithful normal tracial state `tr`,
  which is a quasitrace. By uniqueness in (G3), `tau = tr`.
- **(2) ⟹ (3), (5), (6).**
  - For (3) take `phi = tau`.
  - For (5), linearity on `M_+` gives `C = 1`.
  - For (6), by uniqueness in (H), `tau_N = Tr (x) tau`. This is linear, and
    `E_N` preserves it, so `C = 1`.
- **(3) ⟹ (4).** For any cover,
  `phi(1) <= phi(sum c_i p_i) = sum c_i phi(p_i) <= sum c_i D(p_i)`.
  So `S(1) >= phi(1) > 0`.
- **(5) ⟹ (4).** By (H), `tau` is order preserving. For any cover,
  `1 = tau(1) <= tau(sum c_i p_i) <= C sum c_i D(p_i)`. So `S(1) >= 1/C`.
- **(6) ⟹ (4).** Given a cover, put `b_i = c_i p_i` (`i = 1..N`) and
  `z = sum_i b_i^{1/2} (x) e_{1i} in M_N(M)`.
  - `z z* = (sum_i b_i) (x) e_11` and `G := z* z = [b_i^{1/2} b_j^{1/2}]_{ij}`.
  - By (H), `tau_N(G) = tau_N(z z*) = tau(sum b_i) >= 1`.
  - `E_N G = diag(b_1, ..., b_N)` is a sum of commuting elements. By (L) and
    unitary invariance, `tau_N(E_N G) = sum_i tau(b_i) = sum_i c_i D(p_i)`.
  - So the mass is `>= 1/C`.

**Zero-one law.**

- If `S(1) > 0`, then (1) and (2) hold. Every cover then has mass
  `tau(sum c_i p_i) >= 1`, and the cover `(1,1)` has mass `1`, so `S(1) = 1`.
- If `S(1) = 0`, then (3), (5) and (6) fail. So the best constants in (5) and (6)
  are infinite, and no nonzero positive functional lies below `D`. ∎

## 3. Proofs of the corollaries

**Corollary B.**

- (I) ⟹ (II), (III): take `phi = q` and `C = 1`.
- (II) ⟹ (I) and (III) ⟹ (I): suppose (I) fails.
  - By (G1) there is a `II_1` AW*-factor `M` that is not W*.
  - Its normalized quasitrace `tau` (G3) is a quasitrace on the unital C*-algebra
    `M`. (For AW*-algebras, Haagerup Def. 3.1 notes that (i)–(iii) imply (iv).)
  - By Theorem A, no nonzero positive `phi` satisfies `phi <= tau` even on
    projections, so (II) fails for `q = tau`.
  - `tau` is not C-subadditive for any `C`, so (III) fails. ∎

The quantifiers can be sharpened. By Theorem A, for a counterexample factor the
best linear minorant has mass exactly `0`, and in all non-counterexamples the
mass is `1`. So (II) with "mass `>= 10^-9`" is still equivalent to (I).

**Corollary C.** Let `M` not be W*. By Theorem A, `S(1) = 0`, which gives covers
of mass `< eps`. Take such a cover with `N` terms and mass `mu`.

- **Number of terms.** Iterating (H) and using Cauchy–Schwarz,
  `1 <= tau(sum b_i) <= (sum_i tau(b_i)^{1/2})^2 <= N sum_i tau(b_i) = N mu`.
  So `N >= 1/mu > 1/eps`.
- **Commuting classes.** Suppose the index set splits into `k` classes whose
  projections pairwise commute. Put `a_j = sum_{i in class j} b_i`. Each class
  generates an abelian C*-algebra, so by (L) `tau(a_j)` is the class mass. The
  same inequality gives `1 <= tau(sum_j a_j) <= k sum_j tau(a_j) = k mu`, so
  `k > 1/eps`. ∎

**Corollary D.**

- (⟹) Take a cover of mass `< eps` and its Gram matrix `G` as in (6) ⟹ (4). Then
  `tau_N(G) >= 1` and `tau_N(E_N G)` equals the mass, so
  `tau_N(E_N G) < eps <= eps tau_N(G)`.
- (⟸) If `M` is W*, then `tau_N = Tr (x) tau` is linear and `E_N`-invariant. So
  `tau_N(E_N G) = tau_N(G)`, and the inequality fails for `eps <= 1`. ∎

`E_N G = N^{-1} sum_k U^k G U^{-k}`, with `U = diag(1, w, ..., w^{N-1})` and
`w = e^{2 pi i/N}`. So Corollary D says a counterexample is exactly a quasitrace
for which averages of `N` unitary conjugates can lose all but an `eps` fraction
of the quasitrace. The loss ratio is either `1` or unbounded; it is never
bounded by a constant `> 1`.

## 4. What this kills, and what it leaves

**Killed (class-level).** Consider any method that, for an arbitrary
counterexample candidate factor, produces a bounded-constant inequality in either
of these forms:

- a lower linear bound `phi <= tau` with `phi != 0`;
- `tau(sum a_j) <= C sum tau(a_j)`, or `tau(unitary average) >= tau/C`.

Such a method already proves Problem I outright. There are no "partially
pathological" factors. In particular, approaches that settle for a lossy
linearization ("`tau` is linear up to constant `C`") are not weaker than the
problem. Proposition 4.1 of the certificates artifact covers only `C = 1`.

**Left open (the reduced statement).** Every `II_1` AW*-factor admits a cover
lower bound `sum c_i p_i >= 1 ⟹ sum c_i D(p_i) >= delta` for one fixed
`delta > 0`. Equivalently, `D` is non-pathological.

- A counterexample requires covers of arbitrarily small mass.
- Such covers must use unboundedly many pairwise non-commuting classes of
  projections (Corollary C).

**Dead ends recorded.**

1. *Noncommutative Kalton–Roberts.* It would give non-pathology from a uniform
   exhaustivity estimate. It dies at the Gleason/Yeadon step for `II_1`
   projection lattices, which extends a finitely additive measure using a normal
   trace, and that trace is exactly what is missing.
2. *Uniform Roe domination.* On propagation-`R` operators,
   `T <= K_R E(T)` for the diagonal expectation, but `K_R` is unbounded in `R`.
   So it gives no dimension-free constant.
3. *Averaging over a dual action* (crossed products by `Z` or `Z/2`). The average
   `tau ∘ E` is linear only if Jensen holds for `E`. That is Corollary D itself.

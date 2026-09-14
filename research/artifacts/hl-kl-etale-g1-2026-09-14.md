# hl-kl-etale-g1 — etale roots for semisimple tuples (2026-09-14)

Lane target: gap G1 of `amplified-algebraic-roots-in-characteristic-zero`, which
feeds `kl-holds-for-char-zero-linear-sofic-groups` through
`kl-char-zero-linear-sofic-via-amplified-roots`. Everything here is unreviewed.

## 1. The gaps as the graph uses them

- **ARR(L)** (`linear-sofic-kl-from-amplified-algebraic-roots`): for every tuple
  `a` in `GL_n(L)^k`, every `w` in `F_k * <t>` with nonzero exponent sum and
  every `epsilon > 0`, there are `r` and `T` in `GL_{nr}(L)` with
  `rho(w(T ; a (x) 1_r) - 1) <= epsilon`.
- **G1** (the "Exact gap left" sentence of
  `etale-roots-of-the-semisimplification-lift-to-exact-roots`): does every
  semisimple tuple have an etale root after amplification? A yes plus Corollary F
  there would give exact roots for every tuple, so `ARR(L)` with `epsilon = 0`.
- **G2**: the approximate premise itself, for tuples without an exact root.

## 2. Verdict

- **G1 is false**, as landed in `etale-roots-lie-in-the-bicommutant-of-the-constants`:
  - **Theorem G:** etale roots commute with the commutant of the constants.
  - **Corollary H:** amplification is inert for etale roots; the etale roots at
    level `r` are `T_0 (x) 1_r` with `T_0` etale at level 1.
  - **Corollary I:** an exact finite criterion for commuting semisimple tuples.
  - **Corollary J:** `(diag(2,1), 1)` with `w = x^2 a x^{-1} a^{-1} b` has no etale
    root at any `r` (char != 2). Its roots over char 0 are `1 + t E_12`.
  - **Remark:** the non-semisimple caution tuple `(diag(2,1), 1 + E_12)` does have
    an etale root (`det D = 9/4`).
- This is not a counterexample to ARR: `T = 1` is an exact root in Corollary J.
- `amplified-algebraic-roots-in-characteristic-zero` and
  `kl-holds-for-char-zero-linear-sofic-groups` stay **OPEN**.

## 3. Degree theory plus transversality (brief, step 2)

- **Source status.** The graph records "unitary constants have exact roots with
  `r = 1`" by the Gerstenhaber–Rothaus degree argument (M. Gerstenhaber,
  O. S. Rothaus, *The solution of sets of equations in groups*, PNAS 48 (1962)
  1531–1533, doi:10.1073/pnas.48.9.1531). The PNAS page returned HTTP 403 on
  2026-09-14, so the theorem text was **not read** here. Nitsche–Thom Theorem 1.2
  (read, see `kervaire-laudenbach-holds-for-hyperlinear-citation`) is a
  group-level statement, not the matrix-root statement.
- **Sketch, conditional on that input, not landed.**
  - `F : U(N) x U(N)^k --> U(N)`, `(T, c) |-> w(T ; c)` is a submersion as soon
    as some constant letter occurs.
  - By parametric transversality, for almost every unitary `c` the value `1` is
    regular for `T |-> w(T ; c)`.
  - For unitary data every `S_i` is unitary, so `D_{T,c}` preserves `u(N)` and is
    the complexification of the real differential. Regular points are exactly
    etale roots.
  - With nonzero degree, almost every unitary tuple has an etale root.
  - The etale locus `E_N` (tuples with an etale root) is the image of the etale
    part of `{w = 1} --> GL_N^k`, hence Zariski open. It is nonempty, so dense.
- **Why "generic" does not upgrade to "every semisimple tuple".** Corollary H:
  `c (x) 1_r` always has `1 (x) M_r` in its commutant, so amplification itself
  forces the root into `M_N (x) 1_r` and cannot leave the bad locus.
- **Clean example of the bad locus.** For `a = diag(zeta, 1)`, `b = 1` and the
  same `w`:
  - the only diagonal root is `T = 1`;
  - `D(Y) = 2Y - a Y a^{-1}` there, with `s_12 = 2 - zeta` and
    `s_21 = 2 - zeta^{-1}`;
  - so an etale root exists if and only if `zeta` is not `2` or `1/2`.

  The bad set avoids the unit circle, as transversality predicts, and
  Corollary J is the point `zeta = 2`.

## 4. Dangerous cases (brief, step 2)

- **Repeated eigenvalues / symmetry.** This is the mechanism of Corollary H.
  Every amplified tuple has a large commutant, and an etale root must commute
  with all of it.
- **Non-unitary eigenvalue.** This is Corollary J (eigenvalue `2`, char 0).
- **Dihedral char-p obstruction moved to char 0.** The permutation constants of
  `D_p` are unitary over `C`, so the recorded unitary root statement gives exact
  roots at `r = 1`. Etaleness was not tested: no computer algebra system was
  available (sympy is absent locally and in the MSI system python).
- **Unitary tuples whose roots are all singular.** Not searched. Corollary I
  gives the finite test for diagonal unitary tuples.

## 5. G2 and barriers (brief, step 3)

- **(R1) Rank-closeness reduction (elementary, proved here).**
  - Statement: if `rho(a'_j - a_j (x) 1_r) <= delta` for all `j` and
    `w(T ; a') = 1`, then `rho(w(T ; a (x) 1_r) - 1) <= l_c delta`, where `l_c`
    is the number of constant letters of `w`.
  - Proof: `rank(prod X_i - prod Y_i) <= sum rank(X_i - Y_i)` by telescoping, and
    `rank(X^{-1} - Y^{-1}) = rank(X^{-1}(Y - X)Y^{-1}) = rank(X - Y)`.
  - So G2 follows if every amplified tuple is rank-close to a tuple with an
    exact, not necessarily etale, root.
- **(B1) Genericity cannot supply that.**
  - Geometric multiplicity is rank-Lipschitz:
    `|dim ker(X - lambda) - dim ker(Y - lambda)| <= rank(X - Y)`.
  - Tuples within normalized rank `delta` of `a (x) 1_r` keep every eigenvalue of
    each `a_j` with normalized geometric multiplicity at least `mu/n - delta`.
    Their conjugation saturation is a proper closed set.
  - So the dense etale locus of §3 says nothing about them. A proof must find
    roots on the strata with prescribed large eigenspaces.
  - This is also why perturbing to unitarizable constants fails in the rank metric
    (hl-kl-arr-char0).
- **(B2) Implicit function theorem.** An etale root persists under Euclidean-small
  perturbations of the constants. Rank-small perturbations are not
  Euclidean-small, so etaleness gives no rank-metric stability. No counterexample
  family was found either.
- **(B3) Fusion barrier (conditional on the unitary root statement, not landed).**
  - Let `Gamma = <a>` and `G_w = (Gamma * <x>)/<<w>>`, and let `gamma, delta` in
    `Gamma` be conjugate in `G_w`.
  - Every unitary irreducible representation of a finite quotient of `Gamma`
    extends to `G_w` at `r = 1`. So `gamma, delta` are conjugate in every finite
    quotient of `Gamma`.
  - Take the finitely generated coefficient domain `R` (entries, inverse
    determinants, eigenvalues). Reduction modulo maximal ideals gives finite
    quotients, and a dense set of maximal ideals preserves the ranks of
    `(a(gamma) - lambda)^j` and `(a(delta) - lambda)^j`. Hence `a(gamma)` and
    `a(delta)` are similar.
  - So in char 0 no approximate-root obstruction can come from a rank-Lipschitz
    spectral invariant of one fused pair; the odd-characteristic mechanism has
    no such transport.
- **(B4) Unit barrier.** For `gamma` of infinite order in any group `G` and
  `lambda != 0`, `gamma - lambda` is not a unit of `C[G]`.
  - If `|lambda| = 1`, left translation by `gamma` on `l^2(G)` is a sum of
    bilateral shifts, with spectrum the whole circle.
  - Otherwise the only inverse in `B(l^2 G)` is a Neumann series with infinite
    support.

  So "a singular constant polynomial becomes a unit in the adjunction" never
  obstructs.

## 6. Exact remaining gaps

- **G1-new: non-etale lifting.** Along the torus degeneration of Corollary F, does
  some root of the semisimplified equation have vanishing obstructions?
  - Candidates are clean roots, whose kernel of `D` is the tangent of the
    centralizer orbit, for example `1 + t E_12`, `t != 0`, for `(diag(2,1), 1)`.
  - First-order computation: differentiating `w(g T g^{-1} ; g c g^{-1}) = g w g^{-1}`
    shows the constant-direction error lies in the image of `D` when the direction
    is `[X, c]`.
  - The degeneration direction is the nilpotent off-diagonal part, which is not a
    conjugation direction of the closed orbit. The obstruction pairing with
    `ker D^t` has to be computed. **OPEN.**
- **G2-new: rank density on eigenspace strata.** For every `a`, `w` and
  `delta > 0` there are `r` and `a'` within normalized rank `delta` of
  `a (x) 1_r` with an exact root. This implies ARR char 0 by (R1). **OPEN.**

## 7. Compute

- Script: `research/artifacts/hl-kl-etale-g1-2026-09-14-fox-operator-check.py`,
  standard-library `fractions`, runs in about a second. It was run locally on
  2026-09-14 and the output is quoted below.
- No MSI jobs ran; no Groebner or CAS tests.

```text
semisimple tuple (diag(2,1),1):
  t= 0  w=1: True  rank D = 3 of 4
  t= 1  w=1: True  rank D = 3 of 4
  t= 3  w=1: True  rank D = 3 of 4
  t= -2/7  w=1: True  rank D = 3 of 4
node tuple (diag(2,1),1+E12): w(T0)=1: True  det D(T0)= 9/4
amplified r=2: w=1: True  rank D = 16 of 16
semisimple amplified r=2 at (1+E12)(x)1: rank D = 12 of 16
sanity D_{1,1} = m id: True
```

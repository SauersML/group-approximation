# Point-norm matricial stability of SL_4(Z): swarm attack, 2026-09-16

- **Lane:** `swarm-sl4z-matricially-stable`.
- **Hole locked and worked:** `sl4z-matricially-stable`, the claim that every operator-norm
  asymptotic homomorphism `SL_4(Z) -> U(k_n)` is pointwise close to genuine representations.
- **Full proofs:** `research/artifacts/sl4z-thin-corona-gap-reduction-2026-09-16.md`.
- **Scripts:** none.  All work is by hand.
- **Outcome:** a reduction.  The lane found no proof or refutation of stability.  It
  proves the following.
  - An unconditional theorem about the maximal C*-algebra (claim B below).
  - A necessary condition for stability, stated as a spectral inequality for one element
    (claim C, open).
  - That condition implies the full algebra is not MF (claim D, open).
  - An explicit refutation criterion for stability.

## Setup

- `Gamma = SL_4(Z)`.
- `C = <g_1,...,g_4>` is the four-generated free profinitely dense subgroup of
  Aka--Gelander--Soifer, used through `sln-z-thin-codense-tau-pair`.  `F` is its symmetric
  generating list.
- `S` is a finite symmetric generating set of `Gamma`, with Kazhdan constant `kappa_S`.
- `p` is the central Kazhdan projection in `C*(Gamma)`, and `mu = (1 + |F|^(-1) sum_c u_c)/2`.
- The test element is `x = mu(1-p)`.
- `Q_k = prod M_(k_n) / sum M_(k_n)` is the matrix corona.  A *corona representation* is a
  unital *-homomorphism `C*(Gamma) -> Q_k`.  By lifting unitaries, these are exactly the
  asymptotic homomorphisms up to pointwise equivalence.

The target had three recorded attempts: Dadarlat's obstruction, uniform stability, and
almost-commuting unipotents.  None settles it.

## Literature gate (2026-09-16)

No source found that proves or refutes point-norm matricial stability of `SL_n(Z)`,
`n >= 3`, or that decides whether `C*(SL_n(Z))` is MF.

**Consulted (arXiv abstract pages fetched 2026-09-16):**

- arXiv:2007.12655, Dadarlat, *Obstructions to matricial stability of discrete groups and
  almost flat K-theory* (v1 2020-07-24, revised 2021-03-18).  It gives an even rational
  cohomology obstruction.  The target's attempt records that the rational cohomology of
  `SL_4(Z)` is reportedly concentrated in degrees 0 and 3 (Lee--Szczarba, not re-read), so
  the obstruction would be void.
- arXiv:1808.06793, Eilers--Shulman--Sorensen, *C*-stability of discrete groups*
  (2018-08-21, revised 2021-04-20).  It gives general criteria.  Nothing specific to
  higher-rank lattices was found in the abstract.
- arXiv:2301.00476, Glebsky--Lubotzky--Monod--Rangarajan, *Asymptotic cohomology and
  uniform stability for lattices in semisimple groups* (2023-01-01, revised 2023-07-09).
  This is uniform stability, which does not control pointwise defect.
- arXiv:2512.09180, Fournier-Facio, *Stability, approximable quotients, and higher property
  (T)* (v1 2025-12-09, v2 2026-06-08).  It is about Frobenius stability of constructed
  groups, not `SL_n(Z)`.
- arXiv:2512.15494, Alekseev--Thom.  Checked earlier in this lane against the repository
  artifact `research/artifacts/alekseev-thom-2512.15494-verified.md`.  It is about stability
  in finite actions and does not address operator-norm stability of `SL_n(Z)`.
- arXiv:2603.13564, Shulman, *The MF property for amalgamated free products* (2026-03-13,
  revised 2026-08-31).  It gives closure properties of MF, and nothing for `SL_n(Z)`.
- arXiv:1711.04584, Doucha--Malicki--Valette, *Property (T), finite-dimensional
  representations, and generic representations* (2017-11-13).  It is about Kazhdan groups
  with RFD full algebra, which `SL_n(Z)` is not.
- arXiv:1006.3365, Bourgain--Varju.  The abstract was fetched for the arbitrary-modulus
  expansion statement.
- arXiv:1205.1140, Aka--Gelander--Soifer.  The abstract was fetched for the profinitely
  dense free subgroup.
- arXiv:math/0609102, Bekka, *Operator-algebraic superrigidity for SL_n(Z), n >= 3*
  (Invent. Math. 169 (2007)).  The abstract was fetched.  It promises "a complete
  description of the tracial states" and says `C*(Gamma)` has no faithful tracial state.
  The body was not read.

**Not re-read and treated as unverified:**
- Bekka, Forum Math. 11 (1999), for non-RFD of `C*(SL_n(Z))`;
- Lee--Szczarba;
- the explicit form of Bekka's trace classification.

The web search budget was exhausted in this lane.  The gate relied on fetched arXiv pages
and the repository's existing literature nodes.

## Results

### B. One element separates the thin quasi-regular representation from matrices (established, conditional only on committed nodes)

Node `sln-z-thin-quasiregular-not-weakly-contained-in-fd`, route
`sln-z-thin-quasiregular-not-weakly-in-fd-proof`, requiring `sln-z-thin-codense-tau-pair`.
Artifact Sections 1--4.

For every `n >= 3` and `x = mu(1-p)`:
- `||rho(x)|| <= 1 - kappa^2/32` for every finite-dimensional `rho`;
- `||sigma_C(x)|| = 1` on `l^2(Gamma/C)`.

**Proof sketch.**
- Finite-dimensional representations factor through congruence quotients, where
  `pi_m(C) = SL_n(Z/m)`.
- Bourgain--Varju gives a uniform gap for `F`.  The Kazhdan projection removes the
  invariant part.
- The coset vector `delta_C` is `C`-fixed, and `sigma_C(p) = 0` because the index is infinite.

**Corollaries.**
- `sigma_C` is not weakly contained in finite-dimensional representations.
- `C*(SL_n(Z))` is not RFD.  This reproves Bekka's theorem with an explicit witness.

**Novelty.**  Modest.  It is the `C*(Gamma)`-level packaging of `(PSG1)` and `(THD2)`.  The
new point is that the witness is a single element, unlike the non-convergent sequence
`y_N`.

### C. The thin corona gap (open hole; necessary for stability)

Node `sl4z-corona-reps-have-thin-relative-spectral-gap`: every corona representation `pi`
of `C*(SL_4(Z))` has `||pi(x)|| < 1`.

- **Stability implies C.**  Route `sl4z-thin-gap-from-matricial-stability`.  Stability
  makes every corona representation a product `q o (rho_n)` of genuine representations.
  Then B gives `||pi(x)|| <= 1 - epsilon`.
- **Equivalent forms, all proved in artifact Section 8.**
  1. **Fixed vectors.**  In every Hilbert space realization of every corona representation,
     `C`-invariant vectors are `Gamma`-invariant: a "thin relative (T) for corona
     representations".
  2. **Linear modulus.**  `(1-t)||(1-pi(p))xi||^2 <= (1/32) sum_c ||pi(c)xi - xi||^2`.  The
     uniformity of `t < 1` over all `pi` is automatic.
  3. **Finite robust form.**  Operator-norm almost-representations with small defect on a
     fixed finite set carry almost `C`-invariant unit vectors to almost `Gamma`-invariant
     ones, uniformly in the dimension.
  4. **States.**  C fails iff some corona-realizable state `omega` has `omega(u_c) = 1` for
     `c in F` and `omega(p) = 0`.
- **Where C holds.**  On product-form corona representations, including permutation models
  and MF embeddings of `C*_r(SL_4(Z))`.  So C does not bear on `sl4z-reduced-cstar-is-not-mf`.

### D. C implies that C*(SL_4(Z)) is not MF (open hole)

Node `sl4z-full-cstar-is-not-mf`, route `sl4z-full-not-mf-from-thin-corona-gap`, requiring
C and B.

- An MF embedding, cut down to its unit corner, is a corona representation.  There
  `||x|| >= ||sigma_C(x)|| = 1` forces `||pi(x)|| = 1`.
- The same argument shows that `C*_(sigma_C)(SL_4(Z))` is not MF, and that no overgroup
  `Lambda >= SL_4(Z)` has MF full algebra.
- The composite "stability implies D" is also immediate from Lemma 5.3 and non-RFD.  C is
  the weaker, single-element hypothesis that suffices.

### Refutation criterion for the target

Any corona representation of `C*(SL_4(Z))` with `||pi(x)|| = 1` refutes
`sl4z-matricially-stable`.  Examples would be an MF model of `C*(SL_4(Z))`, or of
`C*_(sigma_C)(SL_4(Z))`.

In finite terms, the target is refuted by the following data, for some `eta > 0`:
- operator-norm almost-representations `phi_n` with pointwise defect tending to `0`;
- unit vectors `v_n` with `sum_c ||phi_n(c)v_n - v_n||^2 -> 0` but
  `sum_s ||phi_n(s)v_n - v_n||^2 >= eta`.

This lane found no such family.

## Tracial observation (conditional, not a node)

- A failure of C needs only a sequence of single top eigenvectors of lifts `X_n` of
  `pi(x)`.  A normalized trace gives such vectors weight `1/k_n`.
- Bekka (Invent. Math. 169 (2007), arXiv:math/0609102) describes the tracial states of
  `C*(SL_n(Z))`, `n >= 3`.  Only the abstract was checked on 2026-09-16.
- Suppose every trace on `C*(SL_4(Z))` is a limit of finite-dimensional traces, as that
  description is usually recorded.  Then for every corona `pi` with a limit trace `tau`,
  the spectral projection of `X_n` onto `[1 - epsilon + eta, 1]` has normalized rank
  tending to `0`.
- So any counterexample to C is tracially invisible.  This lane did not verify the
  classification, and nothing recorded as a node depends on it.
- The observation does not settle C.  Ozawa's liftable-trace theorem
  (`ozawa-kazhdan-liftable-traces-are-fd-limits`) needs a ucp lift or the LLP for the
  corona trace, and neither is available here.

## Dead ends

1. **Permutation rounding.**  Operator-norm almost-actions by permutation matrices are
   eventually genuine actions: distinct permutation matrices are at distance at least
   `sqrt(2)`.  They factor through congruence quotients and satisfy C.
2. **Sum-of-squares certificate.**  Impossible, since `sigma_C` violates the inequality in
   a genuine representation.  Any proof of C must use matrix origin.
3. **Free restriction.**  `pi|_C = q o (psi_n)` for genuine `psi_n`, since `F_4` is
   matricially stable.  But the Bourgain--Varju gap needs congruence factorization, which
   `psi_n` lacks.
4. **Traces.**  See the tracial observation above.  Traces cannot see single vectors.
5. **Dadarlat's cohomological obstruction** (arXiv:2007.12655).
   - As recorded on the target, it gives non-stability once `H^(2k)(SL_4(Z); Q) != 0` for
     some `k >= 1`.
   - The rational cohomology of `SL_4(Z)` is reportedly concentrated in degrees 0 and 3
     (Lee--Szczarba, not re-read).  If so, the obstruction is void.  Unverified here.
6. **Uniform stability.**  Uniform (operator-norm) stability of Kazhdan groups is a
   different question.  The corona picture has only pointwise defect, and the uniform
   results do not apply.
7. **HS corners.**  Hilbert--Schmidt stability data give no operator-norm asymptotic
   representation, so HS-side nodes cannot feed C directly.
8. **Quotients.**  MF does not pass to quotients: every separable C*-algebra is a quotient
   of `C*(F_infinity)`, and `CO_2 -> O_2` is another example.  So
   `sl4z-reduced-cstar-is-not-mf` and D are logically independent in both directions.
9. **Faithful traces.**  `C*(SL_4(Z))` has no faithful tracial state (Bekka's abstract), so
   a tracial ultraproduct embedding cannot be used to see the whole algebra.

## Adjoint trick versus TRC1

- Artifact Proposition 9.1: C implies the operator-norm-hypothesis case of `(TRC1)` in
  `thin-sln-robust-relative-commutant-transfer`.
  - Given `phi : Gamma -> U(k)` with small operator-norm defect on `E`, the conjugation
    unitaries `Phi(g) T = phi(g) T phi(g)^*` act on the `k^2`-dimensional space
    `L^2(M_k, tr/k)`.
  - `def_E(Phi) <= 2 def_E(phi)`, and `||Phi(g) T - T||_2 = ||[phi(g), T]||_2`.
  - Apply the finite robust form `(b_eta)` of C in dimension `k^2`, with
    `delta = delta'/2`.  Each `T` with `||T||_2 = 1` is a single unit vector there.  So C
    gives the Hilbert--Schmidt commutant transfer whenever the almost-representation
    hypothesis is in operator norm.
- The converse does not obviously hold.  `(TRC1)` controls trace-weighted vectors, in which
  rank-one test vectors have vanishing weight, while C concerns single vectors.
- An operator-norm corona commutant statement `pi(C)' cap Q_k = pi(Gamma)' cap Q_k` does not
  follow from Proposition 9.1.  Whether C transfers across
  `Q_k (x)_max Q_k^op -> Q_(k^2)` was not settled.

## What remains open; weakest step

- **Open.**  C (`sl4z-corona-reps-have-thin-relative-spectral-gap`) is open.  So are D
  and the target.
- **Weakest step in the proved part.**  The transfer from the Bourgain--Varju gap to (KF)
  for all finite-dimensional representations.  It uses:
  - the congruence factorization and co-density from `sln-z-thin-codense-tau-pair`;
  - the discrete Cheeger inequality with explicit constant `h^2/8`;
  - summation over Peter--Weyl isotypic components.
- **Second candidate.**  The lifting argument in Proposition 8.4, `(b') => (a)`: positive
  lifts, Lemma 8.3, and top eigenvectors of lifts.

## Files

- `research/artifacts/sl4z-thin-corona-gap-reduction-2026-09-16.md`
- `research/sln-z-thin-quasiregular-not-weakly-contained-in-fd.md` (claim B)
- `research/sln-z-thin-quasiregular-not-weakly-in-fd-proof.md` (route to B)
- `research/sl4z-corona-reps-have-thin-relative-spectral-gap.md` (claim C, open)
- `research/sl4z-thin-gap-from-matricial-stability.md` (route: target + B => C)
- `research/sl4z-full-cstar-is-not-mf.md` (claim D, open)
- `research/sl4z-full-not-mf-from-thin-corona-gap.md` (route: C + B => D)
- `notes/sl4z-matricially-stable-swarm-2026-09-16.md` (this file)

## Check

- The swarm `check.sh` on all seven research paths exits `0`.
- It prints an informational lane-top warning for `sl4z-full-cstar-is-not-mf`, which is
  not connected to a root node.

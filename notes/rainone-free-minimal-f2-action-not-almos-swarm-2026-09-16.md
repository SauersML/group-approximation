# Rainone's F_2 question: profinite diagonal extensions and covariant certificates (swarm, 2026-09-16)

Target: `rainone-free-minimal-f2-action-not-almost-unperforated` (root, OPEN).
Agent: `swarm-rainone-free-minimal-f2-action` (lock held on the target during
the session).  Nothing is committed; the referee lands the work.

## Setup

`S(X, Gamma)` is the type semigroup: clopens of `X x N` modulo
equidecomposition, ordered algebraically.  It is almost unperforated when
`(n+1)x <= ny` implies `x <= y`.  For a Cantor action `S` is simple iff the
action is minimal.  States normalized at `[1_X]` are the invariant
probability measures.  Tarski's theorem (`kmp-tarski-theorem-preordered-monoids`):
a nonzero element is non-paradoxical iff some state takes the value 1 on it.

A **certificate** is an invariant finitely additive `nu : Clopen(X) -> M` for
a commutative monoid `M`, together with a clopen `A` such that
`2 nu(A) <= nu(A)` fails.

## Literature gate (2026-09-16)

* Boldrini--Prasad, arXiv:2607.01896v1 (2 Jul 2026), read from the LaTeX
  source.  Theorems 6.1, 6.10 and Corollary 6.12 give dense countable
  subgroups of `Aut(B, mu)` that are isomorphic to `F_infinity`, act minimally
  and topologically freely, and have no comparison.
  * The strong refinement property for simple atomless refinement cones is
    cited there to Ortega--Perera--Rørdam (Theorem 3.4, Remark 3.5).  Not
    fetched; unverified.
  * No free action and no finitely generated group.
* Gardella--Geffen--Kranz--Naryshkin, arXiv:2201.03409v3, Theorems B/C:
  amenable minimal actions of groups with paradoxical towers have comparison.
  So any example is non-amenable, consistent with `F_2`.
* Rainone, arXiv:1502.06153v1, p. 33: the question (quoted on the root).
* Web searches earlier in this session (2026-09-16) found no resolution after
  Boldrini--Prasad.  The exact query strings were not kept.
* In-repo: `refinement-monoids-are-topologically-free-cantor-types`
  (ESTABLISHED, `F_infinity`, topologically free), and the "Freeing by
  profinite extensions" attempts on
  `free-minimal-cantor-action-with-finite-clopen-type` and
  `topologically-free-minimal-cantor-action-with-finite-clopen-type`.

## What was proved

### Lemma A (faithfulness; notes only)

Let `Gamma` act minimally on `X`, and let `M` be conical.  An invariant
finitely additive `mu : Clopen(X) -> M` that is not identically zero has
`mu(E) != 0` for every nonempty clopen `E`.

Proof.  The null clopens are closed under finite unions and translates.  If
some nonempty `E` is null, finitely many translates cover `X`, so `mu(X) = 0`.
Conicality then kills every clopen.

Consequences.
* `mu(E)` must be a sum of `n` nonzero terms for every nonempty clopen `E`
  and every `n` (split `E` into `n` nonempty clopens).  Apply this to the
  certificate clopen `A`, whose value must be finite in the sense that
  `2 mu(A) <= mu(A)` fails.  So monoids in which such values have bounded
  decomposition length, such as Boldrini--Prasad's
  `Q_0 = {0,2,3,4,5,6,infinity}` (as transcribed by the solver, not
  rechecked by the referee), cannot certify a minimal action.  Only their
  divisible extensions can.
* Truncated monoids `([0, theta] ∩ D) ∪ {infinity}` are simple and stateless
  with `2u <= u` failing.  But a certificate into them yields a real
  invariant finitely additive measure: cover `X` by finitely many translates
  of a clopen with finite value.  So they are useless for measure-free
  actions.  (Sketch only; the referee did not check this step, in particular
  how sums beyond `theta` are handled.)

### Lemma B (stateless certificate)

Let `Y` be minimal with no invariant probability measure, and let `nu`, `A`
be a certificate.  Then `S(Y, Gamma)` is not almost unperforated.  The proof
is the body of `fn-free-action-via-profinite-diagonal-certificate`:
* `x = [A]` has no state, so `(k+1)x <= kx`, so `(k+1)(2x) <= kx`;
* almost unperforation would give `2x <= x`, and `nu` carries that to `M`.

The committed root attempt "Reduction to a stateless pair" sketches the same
idea; the route now records a complete proof.

### Theorem C (profinite diagonal extensions)

Node: `profinite-diagonal-cantor-type-is-transfer-limit`, proved in
`profinite-diagonal-transfer-limit-proof` (requires the ESTABLISHED induction
claim).  For `Y = X x lim Gamma/N_j` with the diagonal action:
1. it is free;
2. it is minimal iff every `N_j` is minimal;
3. it has an invariant probability iff `X` has one;
4. `S(Y) = lim (S(X, N_j), rho_j)` with the transfer
   `rho_j [A] = sum_(t in N_j/N_(j+1)) [t^(-1) A]`;
5. invariant `M`-valued measures on `Y` are exactly the transfer-compatible
   chains of `N_j`-invariant `mu_j`;
6. **firewall**: if the closures of `N_j` in `Homeo(X)` stabilize, `S(Y)` is
   almost unperforated.

Items 1, 2 and the direct limit were already recorded as unreviewed ideas.
New here: the transfer formula, item 5, and item 6.

Claimed correction of the root (withdrawn by the referee).  The
solver read "exhaustive" in the root's "Profinite diagonal products" attempt
as "minimal".  It means `mu`-exhaustive (Wehrung, Definition 4.7.12), and
under that hypothesis the root's statement is justified: `S(X, N_j) ≅ M` via
`mu` and every transfer is multiplication by the index.  Item 6 is a second,
independent firewall (closure stabilization).  A priori, minimal but not
`mu`-exhaustive `N_j` with shrinking closures can have `S(X, N_j)` strictly
finer than `S(X, Gamma)`; no explicit example was built.  The committed root
file was not edited.

### Reduction

`fn-cantor-action-with-covariant-stateless-certificate` (new OPEN hole) asks
for an action of `F_n` with three properties:
* every `N_j` of a separating chain is minimal;
* there is no invariant measure;
* there is a transfer-compatible chain `mu_j` with `2 mu_0(A) <= mu_0(A)`
  failing.

Route `fn-free-action-via-profinite-diagonal-certificate` shows it implies
`free-minimal-fn-cantor-action-not-almost-unperforated`, hence the root by
the existing induction route.  Freeness, one of the two blockers on the
root's stateless-pair attempt, disappears.  It is replaced by minimal kernels
and covariance of the certificate.

Two necessary conditions follow from the hole's Attempts section.
* **Invariant certificates die.**  If all `mu_j` are `F_n`-invariant, then
  `2 mu_0(A) <= mu_0(A)`.
* **Closures must shrink.**  By the firewall, the closure of `F_n` in
  `Homeo(X)` needs infinitely many strictly shrinking open normal subgroups
  of finite index, i.e. a continuous infinite profinite quotient compatible
  with the chain.

## Approaches and where each dies

1. **Diagonal extension of Boldrini--Prasad dense subgroups.**  A
   finite-index subgroup of a dense `H <= G = Aut(B, mu)` has closure of
   finite index in `G`.  So it is dense unless `G` has a proper open subgroup
   of finite index.  If `G` has none (plausible, unverified), the firewall
   makes every diagonal extension almost unperforated.  This matches the
   committed root attempt.
2. **Level-one covariant structure.**  Take the Fraïssé limit for the conical
   product `M x_c M` with unit `(u, u)`.  Let `G^` be the automorphisms
   preserving the pair `(mu, mu')` up to swap.  `G' = Aut(B, mu, mu')` is
   open, normal and of index 2 in `G^`.  Put `mu_0 = mu + mu'` and
   `mu_1 = mu`.
   * This is one step of a chain.  A full chain needs a measure valued in
     `M`-valued measures on `K = lim F_n/N_j`, with automorphisms covering
     translations of `K`.
   * Its Fraïssé theory (amalgamation, homogeneity, minimality of every
     `G_j`, no invariant measure) was not worked out.
3. **Generic pairs in a K-covariant structure.**  Freeness of the extension
   is automatic.  Where it dies: pairs preserving a common clopen whose
   measure is invariant under the letters' translations form an open set,
   the same obstruction as generic pairs on the root.
   * Side remark for `F_infinity`: sequences with letters in fibres over a
     free dense sequence `kappa_n` in `K` avoid the finite-letter obstruction.
   * If the covariant Fraïssé theory works, a Boldrini--Prasad style argument
     would give a *free* minimal `F_infinity` action whose type semigroup is
     not almost unperforated.
   * Unverified; recorded as a lead for
     `free-minimal-cantor-action-with-finite-clopen-type` (freeness part).
4. **Odometer letter with a Haar-factoring certificate.**  Let `T` be a
   dyadic odometer, and let `mu = phi o Haar` for a monoid map
   `phi : Z[1/2]_+ -> M`.
   * Call `v > 0` absorbing if `phi(v) + phi(d) = phi(v)` for some `d > 0`.
     Absorbing values are upward closed.
   * If every `v > 0` is absorbing, pick `N` with `N d >= v`, and let
     `z = N d - v`.  Then `2 phi(v) + phi(z) = phi(v) + N phi(d) = phi(v)`, so
     `2 phi(v) <= phi(v)` for all `v` and there is no certificate.
   * Otherwise let `v_0 > 0` be non-absorbing.  For any `v <= v_0`,
     `phi(v) = phi(v')` forces `v = v'`, since otherwise the smaller of the two
     would be absorbing.
   * Every clopen of the tower algebra is a disjoint union of levels of Haar
     measure at most `v_0`.  So any partner preserving `mu` preserves Haar
     measure, and there is an invariant probability.
   * Dies either way.  Certificates must not factor through a real measure on
     a cofinal subalgebra.
5. **Additive division.**  A certificate on `X x K` of the form
   `D_([Gamma:N_j])(mu)` with additive division maps forces
   `D_n(n z) = z`, i.e. unique divisibility on the values.  This is the
   invariant-certificate case, which dies (hole Attempts).
6. **A totally minimal letter.**  It makes every kernel minimal at once.  No
   certificate-preserving totally minimal element is known; unexplored.
7. **Shift conjugation `F_infinity = ker(F_2 -> Z)`.**  Fix `T` and vary
   `g_0`, with `g_n = T^n g_0 T^(-n)`.  If `T` preserves a clopen `p`, then
   the `g_0` with `g_0 p = p` form an open set.  So `T` must have no invariant
   clopen, and minimality of `<T, g_0>` then rests on `T`.  Freeness and
   measure-freeness were not reached.
8. **Strong refinement in the root's generic-pairs step.**  The committed
   attempt dies needing a refinement of
   `mu(x_0) + mu(q - x_0) = mu(y_0) + mu(alpha(q) - y_0)` with a nonzero
   corner.
   * For simple atomless refinement cones, strong refinement (per
     Boldrini--Prasad citing OPR, unverified) gives nonzero corners when all
     four terms are nonzero.  The degenerate cases are trivial.
   * So that step looks repairable.  Density of minimality inside the closed
     set `Q` of pairs stays unproved, since perturbations may leave `Q`.
9. **Subshift reformulation.**  Equivalent target: a minimal free
   `F_2`-subshift with no invariant probability and a
   Kolmogorov-consistent, shift-invariant `M`-valued pattern function against
   `2u <= u`.  No construction.
10. **Ara--Exel separated graphs.**  Finite separated graphs give finitely
    generated refinement monoids.  From memory these are separative
    (unverified here), which suggests almost unperforated or non-simple
    types, so minimal examples are unlikely from this source.  Not pursued.

## Where this leaves the root

* Routes into `free-minimal-fn-cantor-action-not-almost-unperforated` now
  include the new covariant-certificate hole.
* Both holes need a finitely generated group whose closure in `Homeo(X)` has
  infinitely many shrinking open normal subgroups of finite index.  It must
  carry a non-invariant, transfer-compatible, stateless certificate.
* The finite-letter open-set obstruction is untouched.  No example is known.

## Files

* `research/profinite-diagonal-cantor-type-is-transfer-limit.md` (claim)
* `research/profinite-diagonal-transfer-limit-proof.md` (route, requires the
  induction claim)
* `research/fn-cantor-action-with-covariant-stateless-certificate.md`
  (OPEN hole)
* `research/fn-free-action-via-profinite-diagonal-certificate.md` (route into
  `free-minimal-fn-cantor-action-not-almost-unperforated`)
* this note.  No experiments were run.

## Referee (2026-09-16)

Checked:
* Every step of `profinite-diagonal-transfer-limit-proof` by hand: Cantor
  and free; both directions of minimality, including invariance of
  `W = ⋃_s g_s Z x [s]`; the homeomorphism `Gamma x_(N_j) X -> X x Gamma/N_j`
  and its inverse; the direct limit (equidecompositions use finitely many
  clopen pieces, so they live at one level, and the algebraic order passes
  to the limit); the transfer formula; the bijection of item 5; and the
  firewall.  In the firewall I checked that `{h : h(D) = gamma D}` is open,
  that `C_(j+1)` is closed, normal and of finite index in `C_j` (hence open),
  and the arithmetic `k n <= P <= k(n+1)` for `k = floor(P/n) >= n`.
* The sign conventions `(t_* mu)(A) = mu(t^(-1) A)` and
  `nu(A x [g N_j]) = mu_j(g^(-1) A)`.  I tested them numerically on a finite
  model (`S_3` acting on ordered pairs, chain `S_3 ⊇ A_3 ⊇ 1`): invariance
  of `nu`, the chain identity and consistency between levels all hold.
* `fn-free-action-via-profinite-diagonal-certificate`.  It is complete given
  its three requirements.  The requirements are the new hole, the new claim
  and the reviewed KMP import (Corollary 2.16).
* The "Invariant certificates die" argument on the hole.  It is correct: it
  uses Tarski in `S(X, F_n)`, the homomorphism given by an `F_n`-invariant
  `mu_j`, and `mu_0 = [F_n : N_j] mu_j` with index at least `k`.
* The totally-minimal-letter remark (`N_j` contains a power of the letter)
  and the dense-subgroup remark (a closed finite-index subgroup is open).
* Duplicates: `bin/cairn search --similar` on both new claims found no
  duplicate.  Status: arXiv listings fetched 2026-09-16 (API query on
  "dynamical comparison", newest first) show nothing after Boldrini--Prasad
  2607.01896 that resolves the question.  Geffen--Hua--Kranz 2608.13000
  proves comparison for local homeomorphisms and does not bear on it.  The
  web-search budget was exhausted, so this check is bounded.

Changed:
* **Withdrew the solver's "correction" of the root's "Profinite diagonal
  products" attempt**, in the claim file and in this note.  The root's
  "exhaustive" means `mu`-exhaustive (Wehrung Definition 4.7.12, recorded on
  `wehrung-countable-refinement-monoids-group-measurable`), not minimal.
  Under that hypothesis Wehrung Theorem 4.7.14(2) gives `S(X, N_j) ≅ M`, so
  the transfers are multiplication by the index and the root's statement
  holds.  The claim now presents item 6 as a second, independent firewall.
* Credited the earlier unreviewed "Freeing by profinite extensions" idea on
  `free-minimal-cantor-action-with-finite-clopen-type` for freeness, the
  direct limit and the class of `1_Y`.
* Added the convention `mu(∅) = 0` to the hole and to item 5.  It is needed
  for "A nonempty" in the route.  Also added `x != 0` before applying Tarski,
  the bound `sigma([1_Y]) >= 1`, the openness justification and the
  `j >= j_0` qualifier in step 6.
* Labelled the "natural replacement" bullet on the hole as heuristic.
  Reworded the Lemma A consequence: the bound applies to the finite value
  `mu(A)`, not to `mu(X)`, which may be `infinity`.  Marked the
  truncated-monoid remark as an unchecked sketch.

Verdict: sound, landed with fixes.
* The transfer-limit theorem, with its firewall, is proved.
* The reduction route is correct.
* The new hole is a sufficient condition, strictly stronger in form than the
  root.  Its value is that it removes freeness from the construction task and
  comes with two proved necessary conditions: certificates that are not
  `F_n`-invariant, and shrinking closures.
* The root remains OPEN.

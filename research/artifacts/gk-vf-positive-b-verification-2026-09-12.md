# Wave-4 positive-side verification (lane w4-vf-positive-b)

Lane `w4-vf-positive-b`, 2026-09-12. This lane verifies `w3-inf-a`, `w3-bern-window`, `w3-bal-prove` and `w4-window-boundary`.
It does not repeat verdicts `w3-vf-positive` has already given in
`research/artifacts/w3-vf-positive-verification-2026-09-12.md`: Section 2 there covers w3-inf-a, and Section 5 covers w3-bern-window.
Section 2 below is an independent second pass on the goal-equivalence. It adds one wording point.

## 1. The finite left-inverse identity and balance (w3-bal-prove, `0ca6899d49`)

Verdicts:

- **`finite-left-inverse-identity-does-not-force-balance`, as landed: FAIL.** The statement over-claims (Section 1.1).
  It is corrected forward at the same id.
- **Route `finite-left-inverse-identity-does-not-force-balance-proof`, as landed: FAIL.** It proves in the wrong setting
  (Section 1.2). It is replaced by a direct tree construction, which passes (Section 1.3).
- **`injective-balance-needs-inf-and-nonlocal-2026-09-12.md`:**
  - Section 1 passes as a proof sketch, with two wording points (Section 1.5).
  - Section 2 is corrected forward.

### 1.1 The landed statement is a Gottschalk counterexample in disguise

The claim asserted three things:

- a group `Gamma` and a finite alphabet `B`;
- an injective cellular automaton `kappa: B^Gamma -> B^Gamma`;
- a local rule for `kappa` that is not balanced.

Over a group, that is exactly a counterexample to the goal:

- **The rule forces non-surjectivity.** An injective automaton with a non-uniform single-site law is not surjective, because
  bijective automata preserve the uniform product measure (`bijective-ca-preserve-uniform-bernoulli-measure`).
- **The identity adds nothing.** Every injective automaton over a group has a finite left-inverse identity
  (Curtis–Hedlund–Lyndon), so the first bullet of the claim carries no extra content.

So the ESTABLISHED claim said, in effect, that some group is not surjunctive. No such group is known, and the route does not
produce one.

### 1.2 Where the route breaks

- **The tree is not a group.** `end-fixing-tree-symmetries-carry-strict-automata` is a calibration off groups.
  - Its automaton lives on `A^V`, where `V` is the vertex set of the 3-regular tree with a fixed end `xi`.
  - It is equivariant for `Aut(T, xi)` acting on `V`, not for a group acting on itself.
  - The node says so itself: over a group acting on itself, equivariant maps of the index set are bijections `g -> gm`, so the
    copying mechanism is absent.
- **The quoted theorem is about groups.** `strict-automata-give-injective-ca-with-skewed-site-marginals` uses blocks `g Omega`,
  anchors on `Omega Omega^-1`, and shift invariance on `A^G`. None of these exist on the tree vertex set.
- **The discrete group fails too.** `Aut(T, xi)`, taken as a discrete group, carries no such automaton either.
  - The kernel of its Busemann character contains no inversions and no hyperbolic elements. So it is the increasing union of the
    stabilizers of the vertices on a ray to `xi`.
  - These stabilizers are profinite, hence residually finite as abstract groups. So the kernel is sofic.
  - The quotient embeds in `Z`. Sofic-by-amenable groups are sofic, and sofic groups are surjunctive.

### 1.3 The correct statement, with a direct proof

**Proposition 1.1.** Setup:

- `T` is the 3-regular tree and `xi` an end.
- `p(v)` is the neighbour of `v` toward `xi`, and `v'` is the other child of `p(v)`.
- `Gamma = Aut(T, xi)` acts on the vertex set `V`.
- `A` is a finite alphabet with `q >= 2` and distinct symbols `0, 1`, and `B = A^2`.

Define `kappa: B^V -> B^V` by

    kappa(x_0, x_1)(v) = ( x_0(v), z(v) ),
    z(v) = 0            if x_0(v) = 1 and x_0(v') = 0     ("v is marked"),
    z(v) = x_1(p(v))    otherwise.

Then:

- `kappa` is continuous, `Gamma`-equivariant, of radius 2, and injective;
- it has an equivariant decoder of radius 1;
- the law of `kappa(x)(v)` under the uniform product measure is not uniform on `B`.

*Proof.*

- **Equivariance and locality.** `Gamma` preserves parents, siblings and symbol values. `kappa(x)(v)` reads `x_0` on `{v, v'}`
  and `x_1` at `p(v)`.
- **Decoder.** Let `c, c'` be the children of `u`.
  - They are never both marked: marking `c` needs `x_0(c') = 0`, and marking `c'` needs `x_0(c') = 1`.
  - Track 0 of the output is `x_0`, so the decoder can see which child is marked.
  - It returns `z` at an unmarked child, which is `x_1(u)`. If exactly one child is marked, it uses the other child. If neither
    is, it returns `min(z(c), z(c'))` for a fixed order on `A`.
  - The rule is symmetric in `c` and `c'`, hence equivariant, and it inverts `kappa` on every input.
- **Site law.** The sites `v`, `v'`, `p(v)` are distinct and the tracks are independent, so

      P(kappa(x)(v) = (1, 0)) = P(marked) + P(x_0(v) = 1, x_0(v') != 0) P(x_1(p(v)) = 0)
                              = q^-2 + (q^-1 - q^-2) q^-1 = 2 q^-2 - q^-3 .

  This exceeds the uniform mass `q^-2` because `q > 1`. QED

For `q = 2` the law on `{0,1}^2` is `(1,0): 3/8`, `(1,1): 1/8`, `(0,0): 1/4`, `(0,1): 1/4`. `kappa` is strict: a marked vertex
with `z != 0` never occurs in its image.

### 1.4 What the example shows, and what it does not

- **Shown.** Read the left-inverse identity `(*)` as an identity on an abstract finite incidence pattern, namely the labelled
  memory maps `m -> eta m` into `EM`. Then `(*)` does not force balance.
- **Not shown.** Anything about groups, or that a proof must be nonlocal.
  - The tree pattern violates right cancellation. The two children `c != c'` read their parent in the same memory position.
  - In a group, `eta m = eta' m` forces `eta = eta'`. That is finite, local data present in every group window.
- **The exact group-level form.**
  - Take a labelled window pattern realized inside a group, with rules `mu` and `rho` satisfying `(*)` at `e`. By equivariance it
    is an injective automaton over that group.
  - So "on every group-realized pattern, `(*)` forces balance" is equivalent to
    `every-injective-ca-has-uniform-single-site-output-law`, and hence to the goal.
  - The example adds one precise sentence to the tree calibration: a counting proof from `(*)` must use right cancellation of
    reads (the read-by count).

### 1.5 Artifact Section 1, the conjugacy-entropy proof. PASS as a proof sketch.

- **Steps 1–3 hold for a countably infinite group.**
  - `tau` is a measure conjugacy onto its image.
  - Rokhlin entropy is a conjugacy invariant of free ergodic p.m.p. actions.
  - The one-site partition of `(Y, nu)` generates.
  - So `h^Rok(A^G, lambda) <= H(p) <= log |A|`, and INF gives balance. This is Proposition 3(a) of
    `finitary-generation-single-site-criterion-2026-09-12.md` at `B = A`.
- **Wording point 1.** The phrase "equivalently, whether `h_fin = h^Rok` on Bernoulli shifts is open" is not equivalent to the
  sentence before it. It is a separate open question, and a positive answer would make FIN and INF the same.
- **Wording point 2.** The "factorised count" paragraph is a heuristic, not a theorem. No node should consume it.
- **Follow-up.** `w3-bal-prove` applied both points at `7b1501fd3e` and changed nothing else. PASS.

## 2. Second pass on the single-site equivalence and window balance (concurs with w3-vf-positive)

This re-derivation was done independently, before the handoff from `w3-vf-positive` arrived. It adds no verdict lines: the verdicts
are in `w3-vf-positive` Sections 2 and 5.

- **Theorem 1, the anchor construction. Concur.** Checked:
  - the three greedy cases: all atoms in one class; an empty class; or a last class holding at most `N - 1` atoms, each of mass
    at most `nu(s_N)`;
  - anchors separate, because `g^-1 h in D \ {e}` would give both `z(h) = 0` and `z(h) = 1`;
  - `kappa` reads `x_0` on `g Omega^-1 D` and `x_j` on `g Omega^-1 Omega M`;
  - the left inverse extends `beta^-1` arbitrarily off `beta(S)`;
  - `P(I = 1) = q^-|D|`, because the points `omega_0^-1 d` are distinct;
  - given `I = 1`, the `k` recoded coordinates are i.i.d. with law `lambda`.
- **Theorem 2 and `bijective-ca-preserve-uniform-bernoulli-measure`. Concur.** One point is worth writing down.
  - `sigma o pi o tau` is not a local permutation in the narrow sense: it changes the coordinates in the finite set `F M^-1` as a
    function of a larger finite context.
  - It is a bijection of `A^G` that fixes every coordinate off `F M^-1`. So over each fixed exterior it permutes the fibre
    `A^(F M^-1)`, and Fubini gives invariance of `mu`.
  - The route's wording ("a bijection of `A^E` times the identity") already covers this.
- **Proposition 3. Concur.** Part (a) holds because the site partition of an injective image generates. Part (c) holds because
  entropy `log |A|` on `A` forces the uniform law.
- **Window balance: a wording point on the calibration.** This is in Section 4 of `window-balance-mass-transport-2026-09-12.md`.
  - Relation (a) is listed there as "totals and translation invariance". Both also hold on the end-fixing tree: totals are just
    counting, and `Aut(T, xi)` acts transitively and preserves `mu`.
  - What the tree lacks is right cancellation of reads. The two children read their parent in the same position, so `|EM| < |E|`
    can occur: take `E` to be the two children of a vertex, so `EM` is the parent alone.
  - The accurate form of (a): each site is read in each memory position by exactly one site, so `|E m| = |E|` for every `m in M`.
  - The artifact's conclusion does not change.

## 3. Numerical window relations (w4-window-boundary, `0d87da248b`)

Verdicts:

- **`numeric-window-relations-do-not-force-balance`: PASS.** There are two wording points (Section 3.7).
- **Route `numeric-window-relations-do-not-force-balance-proof`: PASS.** Every step was re-derived.
- **`balance-from-numeric-window-relations`: correctly marked dead.**
- **A strengthening at `q = 4`** (Section 3.6): the counterexample also satisfies the counts-level shadow of `sigma o tau = id`.

### 3.1 The image of a strict automaton satisfies R1–R4. PASS.

- **R1, R2.** `c_E(p) = q^|EM| nu[p]_E` is the fibre count, an integer. The outputs on `U` read inputs on `UM`.
- **R3.** `c_E(p) <= q^(|EM| - |int_N E|)` by the decoder bound, which is `w3-vf-positive` Section 5.2.
- **R4.** A cylinder is null exactly when the automaton is not surjective. The image is closed, and nonempty open preimages have
  positive mass.

### 3.2 Proposition 1, amenable decoder memory. PASS.

- **Right Følner sets.** Inverting left Følner sets of `H = <N>` gives right Følner sets.
- **Boundary estimate.** If `g` is in `F \ int_N F`, then some `gn` lies outside `F`, so `g` lies outside `F n^-1`.
  - `|F \ F n^-1| = |F n^-1 \ F|`, since both sets have the size of `F`.
  - Right multiplication by `n` maps `F n^-1 \ F` onto `F \ F n`, and `|F \ F n| = |F n \ F|`.
  - So the boundary is `o(|F_k|)`.
- **Entropy.** Every pattern on `F_k` has mass at most `q^(-|int_N F_k|)`, so min-entropy bounds Shannon entropy from below.
  Subadditivity and invariance give `H(y|F_k) <= |F_k| H(y(e))`. Since `e in N`, `int_N F_k` lies in `F_k`, inside `H`.

### 3.3 Lemma 2, nonamenable interiors. PASS.

- **Følner criterion.** Small `|FN \ F|` gives small `|Fn \ F|` and `|F n^-1 \ F| = |F \ Fn|`.
  - Along words, `F s t \ F` lies in `(F s t \ F t) ∪ (F t \ F)`, so the letter bounds add.
  - These sets would be right Følner sets for `H`, which is impossible.
- **Coset splitting.** Right multiplication by `N` preserves left cosets of `H`, and `IN` lies in `E`.

### 3.4 Theorem 3, the merge measure. PASS.

- **Atoms.** `2/q`, `0` and `1/q`.
- **Integrality.** `c_E(p) = q^(|EM| - |E|) prod q lambda(p(g))`, and every factor is in `{0, 1, 2}`. Since `|EM| >= |E|` the count
  is an integer.
- **Decay.** `(2/q)^|E| = q^(-(1 - log_q 2)|E|) <= q^(-theta_N |E|)` exactly when `q^(1-theta_N) >= 2`.
- **Alphabet size.** `q >= 3` is automatic, because `theta_N > 0`.

### 3.5 Proposition 4, the AND measure. PASS.

- **Null pattern.** Outputs `1` at `e` and at `c^2` force `x(c) = x(c^2) = 1`, so the output at `c` is `1`, and `(1,0,1)` is null.
- **Transfer matrices.** The indices are consecutive input bits: `T_0 = [[1,1],[1,0]]`, `T_1 = [[0,0],[0,1]]`, with norms `phi_g`
  and `1`.
  - The count is at most `2 phi_g^l` and there are `2^(l+1)` inputs, so a run has mass at most `(phi_g/2)^l`.
  - Maximal runs on one coset of `<c>` read disjoint inputs, and distinct cosets are independent.
  - `kappa = 1 - log_2 phi_g = 0.3058`.
- **Interiors.**
  - In an induced subforest of the 4-regular tree with `n >= 2` vertices, `2(n-1) >= 4k + (n-k)`, so `k <= (n-2)/3`.
  - `int_(B_1 B_1) C = int_(B_1)(int_(B_1) C)`, so `|int_(B_2) C| <= |C|/9`.
  - Splitting along left cosets of `L` extends this to all of `G`, and `N` containing `B_2` gives `int_N E` inside `int_(B_2) E`.
  - Finally `1/9 <= kappa`.

### 3.6 Strengthening: both pushforward relations hold at `q = 4`

A counts-level form of telescoping `tau`, `sigma`, `tau` would use two relations that R1–R4 do not list:

- **(R5a)** `nu = tau'_* mu` for some automaton `tau'` with memory `M`;
- **(R5b)** `sigma'_* nu = mu` for some automaton `sigma'` with memory `N`.

Together they give `(sigma' o tau')_* mu = mu`. This is the measure shadow of `sigma o tau = id`.

**Claim (checked here, not a node).** Take `q = 4` and `N` containing the radius-2 ball `B_2` of a free pair `a, b`. Then the merge
measure satisfies R1–R4, R5a and R5b, and its site law is not uniform.

- **R1–R4.** Section 3.5 gives `theta_N <= 1/9`, and `4^(8/9) >= 2`, so Theorem 3 applies.
- **R5a.** The merge rule has memory `{e}`, which lies in `M`.
- **R5b.**
  - Identify `A` with `(Z/2)^2`. Let `beta : A -> Z/2` send `a_1, a_2` to `0` and the other two symbols to `1`. Then `beta` pushes
    `lambda` to the uniform law, so `beta(y)` is uniform iid on `Z/2`.
  - Put `sigma'(y)(g) = (beta y(g) + beta y(ga), beta y(g) + beta y(gb))`. It reads `{e, a, b}`, inside `N`.
  - It is the Ornstein–Weiss homomorphism applied to `beta(y)`. On each left coset of `<a, b>` it is surjective: the Cayley graph
    is a tree, so the difference equations can be propagated from one vertex.
  - A continuous surjective homomorphism of compact groups pushes Haar measure to Haar measure.

So at `q = 4` the no-go also covers arguments that use both pushforward relations as numbers. At other alphabet sizes this is not
checked. What still separates injective images from the merge measure is the pointwise identity together with the group law, or
the uniform Gibbs specification the node names.

### 3.7 Wording points

- **Title.** "exactly when the decoder memory group is amenable" is proved in the nonamenable direction only at alphabet sizes
  with `q^(1-theta_N) >= 2`, and at `q = 2` for decoder memories containing a free radius-2 ball. At a fixed small `q` with other
  nonamenable decoders the question is open, as artifact Corollary 5 says. So read the title as "at every alphabet size".
- **`distinct_from` on the tree node.** It says the tree is "where translation totals fail". Totals and invariance hold on the
  tree. What fails there is right cancellation of reads (Sections 1.4 and 2).
- **Not verified here.** The "What remains" bullet on the uniform Gibbs specification cites a 09-08 bridge artifact. No node
  consumes that bullet.
- **Follow-up.** `w4-window-boundary` fixed both wording points at `b3ef22443b`.

### 3.8 Theorem 6, the projection measure (`b3ef22443b`). PASS.

Setup: `M` and `N` generate nonamenable subgroups, `theta = max(theta_N, theta_(M^-1))`, and `q = r^k` with `theta <= 1 - 1/k`.
The measure `nu` is iid and uniform on the `r^(k-1)` symbols of `B^(k-1) x {b_0}`.

- **R1, R2, R4.** Product measure, so R1 holds. `c_E(p) = r^(k|EM| - (k-1)|E|)` is an integer because `|EM| >= |E|`.
  Independence holds for all disjoint sets. A symbol outside the allowed set is null.
- **R3.** `nu[p]_E <= r^(-(k-1)|E|) = q^(-(1 - 1/k)|E|) <= q^(-theta_N |E|) <= q^(-|int_N E|)`, by Lemma 2.
- **Pressure point 1: `I_E`.** The input site `g` is read by the outputs at `g M^-1`, so the bridge's `I_E = {g : g M^-1 ⊆ E}` is
  `int_(M^-1) E`. `M^-1` contains `e` and generates `<M>`, so Lemma 2 applies with `theta_(M^-1)`.
- **G1.** `Y` is the full shift on the allowed symbols, an SFT with memory `{e}`.
  - Every exterior has the whole of `(allowed)^E` as its completion set, and `nu` is uniform on it.
  - A Gibbs measure for this specification has uniform marginals on every finite set, so it equals `nu`.
- **G2.** For every `V` inside `E`, the fraction of completions extending `v` is `r^(-(k-1)|V|) = nu(Y_V = v)`.
- **G3.** `N_Y(E, c) = r^((k-1)|E|)`, `q^|I_E| = r^(k|I_E|)`, and `k|I_E| <= (k-1)|E|` by Lemma 2 for `M^-1`. So
  `b_E = r^((k-1)|E| - k|I_E|)` is a positive integer.
- **G4.** Both bounds hold. The upper bound in the bridge is `|B_out|^|E| = q^|E|`.
- **Bridge relations not listed as G1–G4.** Two more hold.
  - The bridge derives `b_E(c) = |B_E(c)|` with `B_E(c)` a set of assignments on `D_E \ I_E`, where `D_E = E N^-1`. That gives
    `N_Y(E, c) <= q^|E N^-1|`, and `r^((k-1)|E|) <= r^(k|E N^-1|)` holds.
  - The entropy identity (4), `H(Y_E | exterior) = |I_E| log q + log b_E`, reads `(k-1)|E| log r` on both sides.
- **Site law.** The disallowed symbols are null, so the site law is not uniform.

### 3.9 The squeeze (artifact Section 5, claim "What remains", Attempts entry). The rows pass; the "must" sentences are heuristic.

- **The rows.** Each row of the table rests on a proved or verified result:
  - Theorems 3 and 6;
  - the corrected tree fact;
  - `measure-conjugacy-invariants-cannot-certify-surjectivity`;
  - the INF factorization sketch (Section 1.5 above).
- **The "must therefore either" sentences are not a theorem.** This covers artifact Section 5 and the Attempts entry "What a proof must
  use". "Numerical relations" means the specific lists R1–R4 and G1–G4, together with R5 at `q = 4` (Section 3.6), not every
  consequence of injectivity. So the correct form is: "every input examined so far that avoids both of these fails".
- **The Attempts entry drops `h_fin`.** The artifact's second alternative is "maximal Bernoulli Rokhlin entropy, or at least a lower
  bound on `h_fin`". The Attempts entry keeps only INF, but `h_fin` is an intermediate target (Proposition 3 of the single-site
  artifact).
- **Unconditional scope in the Attempts entry.** "cannot remove `q^(|d_N E|)` on any nonamenable decoder group" is proved only at
  large alphabets, and at `q = 2` when the decoder contains a free radius-2 ball. The qualifier is missing.
- **A gap in the squeeze.** It does not cover a numerical proof at small alphabets combined with alphabet descent.
  - `surjunctivity-failure-descends-to-binary-alphabet` is OPEN. If it held, binary surjunctivity would give the goal.
  - The binary case over decoders without a free radius-2 ball is exactly what Proposition 4 leaves out. Section 5 lists that case
    as not reached, but the "must" sentences should mention the descent escape.
- **Follow-up.** `w4-window-boundary` fixed all four points at `832009a617`, and I checked the diff. Artifact Section 5, the claim
  node and the Attempts entry now label the squeeze a classification, and they restore the `h_fin` alternative. Alphabet qualifiers
  appear in the title, the introduction, the Consequence and the Attempts entry. The descent escape is recorded. No new mathematics
  was added. PASS.

## 4. The linear sofic rung as a rank implication (w4-linsofic-surj, `d0f1a8afc`, `85a64ccbe`, `589495a16`)

The lead assigned this lane to me after the others. Everything below is re-derived from
`research/artifacts/linear-sofic-rung-rank-implication-2026-09-12.md`.

Verdicts:

- **`linear-sofic-surjunctivity-is-a-rank-implication-per-datum`: PASS.** I complete one sentence that was proved only over
  finite fields (Section 4.1.4). Three wording points.
- **`gromov-weiss-is-the-monomial-case-of-the-rank-implication`: PASS.** The transfer constants are made precise, and I
  strengthen the transfer (Section 4.2).
- **`site-pullbacks-are-discontinuous-in-the-rank-metric`: PASS for Proposition 3.1.** Its interpretation paragraph is a heuristic
  and mixes up two coordinate algebras (Section 4.3).

### 4.1 Theorem 1.2. PASS.

**4.1.1 Conventions.**
- **Realization.** A labelling realizes `D` when every forward relator is trivial and every reverse word nontrivial. This is
  [RC]'s condition that products coincide along at least `T_f` and at most `T_r`.
- **Finiteness.** `R_f(D)` is finite, since `T_f` lives on `S x M`.
- **Linear soficity.** A countable group is `F`-linear sofic when it embeds in `prod_omega GL_(n_k)(F) / N_omega`, as in
  `sofic-implies-linear-sofic-over-every-field`. So countable subgroups of such a `Q` are `F`-linear sofic.
- **Rank length.** `rk(k g k^-1 - 1) = rk(k(g - 1)k^-1)` and `rk(g^-1 - 1) = rk(g^-1(1 - g))`. The identity
  `gh - 1 = g(h - 1) + (g - 1)` gives subadditivity. So `N_omega` is normal.

**4.1.2 (a) ⇔ (b).** Re-derived using only closure under subgroups and finite direct products.
- **(a) ⇒ (b).** Let `lambda` realize `D` in a linear sofic `K`. Then `ker lambda` contains `R_f`, and `F/ker lambda ≅ lambda(F)`
  is linear sofic. So `ker lambda` contains `N_lin`, and a reverse word in `N_lin` would be trivial at `lambda`.
- **(b) ⇒ (a).** Suppose no reverse word lies in `N_lin`. Pick normal `M_w ⊇ R_f` with `F/M_w` linear sofic and `w` not in `M_w`.
  The diagonal map into `prod_w F/M_w` realizes `D`.
- **Finite products.** Let `G` embed in `prod_omega GL_(n_k)/N` and `H` in `prod_omega' GL_(m_l)/N`.
  - Index by `(k, l)` with the product ultrafilter `omega ⊗ omega'`.
  - Send `(g, h)` to `(a_k ⊗ I_(m_l)) ⊕ (I_(n_k) ⊗ b_l)`, of dimension `2 n_k m_l`.
  - The normalized ranks are `rk(a_k - 1)/(2n_k)` and `rk(b_l - 1)/(2m_l)`. Their limits are half the original limits.
  - So this is an injective homomorphism into one rank ultraproduct.
- **Consequence.** The per-datum equivalence does not use the local-embeddability clause of Proposition 2.5 in the
  metric-ultraproduct artifact.

**4.1.3 (b) ⇔ (c).**
- **(c) ⇒ (b).**
  - Lift the generators to tuples.
  - The finitely many forward relators are infinitesimal along `omega`, and `c = lim_omega rk(rho_k(w) - 1)/n_k > 0`.
  - At `eps = c/2`, for `omega`-almost every `k` all relators lie below `delta n_k`, so the limit is at most `c/2`.
  - Wording point: before embedding, replace `K` by the countable group `lambda(F)`.
- **(b) ⇒ (c).**
  - The negation of (c) has quantifiers `for all w, exists eps_w, for all delta, exists n and rho`, as used.
  - `N_j / n_(w,j)` is an integer.
  - Every forward relator has rank at most `sum_w (N_j/n_(w,j)) (n_(w,j)/j) = |W_r| N_j / j`, so normalized rank at most `1/j`.
  - A reverse word `w'` has rank greater than `(N_j/n_(w',j)) eps_(w') n_(w',j) = eps_(w') N_j`, so normalized rank greater than
    `eps_(w') / |W_r|`.
  - The class of `(sigma_j)` realizes `D` in a countable subgroup of a rank ultraproduct.
- **Corollary 1.3 and the claim's Consequence.** Both follow with [RC] Theorem 1.

**4.1.4 The neighbouring-rung sentence, over every field.**
- **The gap.** The claim node says, for an arbitrary field, that bounded conjugacy width `C` of one reverse word gives
  `rk(rho(w) - 1) <= C max_r rk(rho(r) - 1)`. Remark 1.4 proves this only over finite fields: there `rho(F)` is finite, so closure
  membership puts `w(rho)` in `Cons_C(R_f(rho))`, and the rank length finishes.
- **Specialization.**
  - Let `R` be the subring of `F` generated by the entries of every `rho(x_a)^(±1)`. It is a finitely generated `Z`-algebra and a
    domain, hence a Jacobson ring whose maximal ideals have finite residue fields.
  - Take a nonzero minor `d` of `rho(w) - 1` of size `rk(rho(w) - 1)`. The Jacobson radical equals the nilradical, which is `0`, so
    some maximal ideal `m` does not contain `d`.
  - The determinants `det rho(x_a)` are units of `R`, so reduction mod `m` gives an invertible tuple `rho-bar` over `R/m`.
  - Under reduction, `rk(rho-bar(w) - 1) = rk(rho(w) - 1)` and `rk(rho-bar(r) - 1) <= rk(rho(r) - 1)`.
  - The finite-field case for `rho-bar` gives the inequality for `rho`.
- **Wording point.** Remark 1.4 writes the width as `n`, the same letter as the dimension.

### 4.2 Theorem 2.1 and Remark 2.3. PASS.

- **Assembly.** By Lemma 1.1, amplifications and direct sums of monomial tuples are monomial. So the negation of Theorem 2.1
  realizes `D` in `Q_mon`.
- **Hamming comparison.**
  - `j(A)(lambda, i) = (lambda a_i, pi(i))`, for `A e_i = a_i e_(pi(i))`, is a homomorphism because `F` is commutative.
  - If columns `i` of `A` and `B` agree, then `j(A)` and `j(B)` agree on all of `F^x × {i}`. Otherwise they differ at every point
    of it. So `d_H` is the fraction `t` of differing columns, and `rk(A - B) <= tN`.
  - `rk(A - B) = rk(1 - A^-1 B)`. On a cycle of length `l >= 2` of `A^-1 B` the kernel has dimension at most `1`. A fixed coordinate
    with scalar different from `1` contributes rank `1`. So `rk(A - B) >= tN/2`.
  - Therefore `Q_mon -> prod_omega Sym(X)/N^H` is well defined and injective. Its countable image is sofic, contradicting
    `sofic-groups-are-surjunctive` through [RC].
- **Remark 2.3 constants.**
  - Telescoping also covers inverse letters, since `rk(rho(x)^-1 - rho'(x)^-1) = rk(rho'(x) - rho(x))`.
  - Precise transfer: let `rho` lie within `theta n` of a monomial `rho'`, generator by generator, and let `eps > 4 theta`. The
    monomial implication at `eps - 4 theta`, with its `delta_mon`, gives the implication for `rho` with
    `delta = delta_mon(eps - 4 theta) - 4 theta`, whenever that is positive.
  - The artifact's condition `4 theta < delta(eps)` is the approximate form of this.
- **Strengthening.** Word ranks are invariant under simultaneous conjugation. So the transfer also holds for tuples near
  `g rho' g^-1` with `rho'` monomial. Witnessing tuples stay far from the whole conjugation orbit of monomial tuples, not only from
  the monomial tuples of one basis.
- **Scope.** The transfer concerns the reverse word that Theorem 2.1 supplies. Failure of the rung needs failure at every reverse
  word, so "witnesses stay far from monomial" holds for the witnessing families at that word.

### 4.3 Proposition 3.1. PASS; the interpretation is a heuristic.

- **(b).** `E(a)(e_i ⊗ e_j) = delta_ij a e_i - (a e_i) * (a e_j)`.
- **(a).**
  - Entries are idempotent, supports are disjoint, and columns are nonzero. So the supports are singletons and `a` is a permutation
    matrix.
  - Conversely, permutation matrices are algebra automorphisms.
  - A monomial matrix with a scalar different from `1` has `E ≠ 0`.
- **(c).**
  - `det(I + J) = 1 + n`.
  - `(e_i + 1) * (e_i + 1) = 3 e_i + 1`, and subtracting `e_i + 1` leaves `2 e_i`. For `i ≠ j`, `(e_i + 1) * (e_j + 1) = e_i + e_j + 1`.
  - In characteristic other than two, the `2 e_i` span `F^n`.
  - In characteristic two, `n + 1 ≠ 0` forces `n` even. The coordinate sum of `e_i + e_j + 1` is `n = 0`. The differences
    `e_j + e_k`, which need a third index and so `n >= 3`, span the hyperplane. So the rank is `n - 1`.

**Wording points.**
- **Title.** "jumps to full rank" is `n - 1` in characteristic two.
- **Basis dependence.**
  - `E` is defined relative to one coordinate algebra.
  - Word ranks are conjugation invariant, but `E` is not: `E(g P g^-1)` vanishes relative to the basis `g e_i`.
  - What the proposition shows, after conjugating the example, is that no fixed coordinate algebra is stable under rank-one
    perturbations.
- **Two algebras mixed up.** The claim's Interpretation paragraph and artifact 3.2 "Where evaluation works" mix two algebras.
  - `E(a) = 0` only at permutation matrices.
  - The monomial tuples of Section 2 are counted through their permutation action on `F^x × {1, ..., N}`, not through the
    coordinates of `F^n`.
  - "Counting arguments work on permutation-like models only" and "a proof has to linearize on the group side first" are
    heuristics.
  - The claim node should label that paragraph as a heuristic.

**Follow-up.** `w4-linsofic-surj` applied every point at `42f9fdbadc`, and I checked the diff:
- linear control over every field, citing Section 4.1.4, with the width renamed `b`;
- (c) ⇒ (b) now embeds `lambda(F(D))`;
- the precise transfer constant, stated for the orbit under conjugation;
- the site-pullbacks title now reads "rank at least n minus one";
- Remark 3.2 records the basis dependence;
- the interpretation is relabelled Heuristic 3.3.

PASS.

## 5. Random-order transport and three-point decoders (w3-strategist-pos `bbbb6ba4ee`; w4-three-point `e87f4c60f5`, `e37e1df9b`)

These lanes were reassigned from `w3-vf-positive`. That verifier had commented to w4-three-point by message, and the lane
corrected forward at `e37e1df9b` before this pass. The verdicts below concern the current versions.

- **`injective-ca-random-order-transport-identity`: PASS.**
- **Corollary 2 and the two cycle routes: PASS.** The routes are `full-site-entropy-via-random-order-transport-domination` and
  `random-order-transport-domination-from-full-site-entropy`. They record an intended equivalence and establish nothing.
- **`transport-identity-gives-reciprocal-memory-entropy-bound`, current version: PASS.** One wording point.
- **Lemma 3.1 of `three-point-decoder-transport-obstruction-2026-09-12.md`: PASS.**
- **`skewed-marginal-amplification-enlarges-decoder-memory` (OPEN): stated too broadly.** It fails when the image of `tau` avoids a
  symbol (Section 5.4).

### 5.1 The transport identity. PASS.

- **Input side.** Fix an order realization and list `N` increasingly. The chain rule gives
  `sum_i I(x(e); y(n_i) | y(n_1), ..., y(n_(i-1)), U = u) = I(x(e); y|_N | U = u) = log |A|`, because `U` is independent of `x` and
  `x(e) = nu(y|_N)`. Averaging over `U` keeps the value.
- **Output side.** The joint law of `(x, y, U)` is invariant under left translation, `kappa` is equivariant, and the order is defined
  pointwise from `U`. So `t_n(g) = t_n(e)`, and at `g = n^-1` the term is the one displayed.
- **Check on `Z` (artifact 2.5), recomputed on both sides.**
  - Output terms: `3/2` and `1/2` bits.
  - Input terms: `t_0 = 3/2` (2 bits if `1 ≺ 0`, else 1) and `t_1 = 1/2` (1 bit if `0 ≺ 1`, else 0).
  - Both sides sum to `2`.
- **Tree calibration (2.1).** Mass out of a vertex is `log |A|` and mass in is `(1/2) log |A|`. Re-derived.
- **Proposition 3.** With `1 ≺ 0` and `-1 ≺ 0` the output-side sum is `2 + 1 = 3` bits, while `H(y(0)) = 2`. PASS.
- **3.1.** For independent `X_i`, `sum_i I(X_i; Y) <= I(X_1, ..., X_k; Y)`. PASS.
- **Wording point.** This concerns artifact 3.3 and the Attempts line "Amenable decoder memory. Holds" on the domination node.
  - For `B = A`, `amenable-decoder-memory-forces-surjectivity` gives bijectivity, hence a uniform site law.
  - For `B != A` that theorem does not apply. The conclusion still holds by counting inside `Gamma = <N>`:
    `x|_F` is a function of `y|_(FN)`, so `|F| log |A| <= |FN| H(y(e))`, and right Følner sets of `Gamma` give
    `H(y(e)) >= log |A|`.

### 5.2 The reciprocal bound, current version. PASS.

- **Proofs.** The subadditivity proof is re-derived. The second derivation uses `A_n <= H(y(e) | Z_n, U) <= H(y(e))`, and the
  per-term form in Remark 1.2 is correct.
- **Wording point.** The bound is the case `F = {e}` of the counting bound `H(y(e)) >= log |A| sup_F |F|/|FN|`, already on main in
  Section 4 of the single-site artifact.
  - That bound beats `1/|N|` over some nonamenable decoder memories.
  - Example: `N = {e, s, t}` with `s, t` generating a free semigroup, and `F_L` the positive words of length at most `L`. Then
    `F_L N = F_(L+1)`, so `|F_L| / |F_L N| -> 1/2 > 1/3`.
  - A line in the claim's Attempts would keep `1/|N|` from being read as the best elementary constant.

### 5.3 Lemma 3.1. PASS.

- **No anchors.** A constant track `0` has no anchors. If `|D| >= 2`, an anchor needs the symbols `1` and `0` at once. If
  `D = {e}`, take the constant different from `1`.
- **Restriction.** With constant tracks `2..k`, `kappa(x) = (x_0, tau(x_1), c_2, ..., c_k)`, where `tau` sends constants to
  constants. Substituting the constants gives a left inverse of `tau` that reads within `N`.

### 5.4 The constructed left inverse, and the case `Omega = {e}`

**Memory of the constructed left inverse.**
- To decode `x_j(e) = nu(y_j on N_tau)`, the decoder of Step 4 checks, for each `n` in `N_tau` and `omega` in `Omega`, whether
  `h = n omega^-1` is an anchor. That reads track `0` on `h D`.
- If `h` is an anchor, it inverts `beta` on the block, which reads track `j` on `h Omega`.
- So its memory is `N_tau Omega^-1 (Omega Omega^-1 ∪ Omega)`.

**`Omega = {e}`.**
- If the image of `tau` avoids one symbol at a site, take `Omega = {e}`. Then `D = {e}`, the anchors are the sites where `x_0 = 1`,
  and the blocks are single sites.
- The constructed left inverse then has memory `N_tau`, which is three points when `N_tau = {e, s, t}`.
- Theorem 1 of the single-site artifact still skews the site law: its classes are singletons, and the last class is empty.

**Consequences.**
- **Where the claim fails.** `skewed-marginal-amplification-enlarges-decoder-memory` fails for every strict `tau` that has a
  three-point left inverse and whose image avoids a symbol.
- **What a proof would give.** A proof of the claim as stated would show that no such `tau` exists. Three-point domination would
  also rule them out.
- **Where the reduction works.** For those `tau`, the reduction proposed on `three-point-decoder-memory-injective-ca-are-surjective`
  runs as stated.

**`|Omega| >= 2` and `<s, t>` nonamenable: the constructed memory has more than three points.**
- It contains `N_tau X` with `X = Omega^-1 Omega`, and `X` contains some `x != e`.
- Suppose `N_tau X = N_tau`. Right multiplication gives `N_tau x = N_tau` for each `x` in `X`, so `N_tau` is a union of left cosets
  of the finite group `H = <X>`.
- Then `|H|` divides `3` and `|H| >= 2`, so `H = N_tau` and `<s, t>` is finite. That is a contradiction.
- Other left inverses are not controlled. Lemma 3.1 is the only general lower bound.

**Recommendation.** Restate the claim for strict `tau` whose missing patterns all need at least two sites, or record the exception.

**Follow-ups, checked against the diffs.**
- **w3-strategist-pos, `e38323248a`.**
  - The `B != A` counting argument is cited.
  - The exception `Omega = {e}` is recorded.
  - Relations of the host now enter through the encoder windows.
  - The free decoder-group case is marked open.
- **w4-three-point, `2c463ed440`.**
  - The amplification claim is restated for strict `tau` whose missing patterns all need at least two sites.
  - Artifact Sections 3.1 (the case `Omega = {e}`) and 3.2 (the coset count) are added.
  - The counting-bound line is added to the reciprocal claim's Attempts.

Both PASS.

## 6. Surjunctive normal subgroups and the lamplighter linearization (w5-free-pos-c, `84c543c4a`)

Verdicts:

- **`normal-surjunctive-decoder-memory-forces-surjectivity`: PASS.**
- **`complex-lamplighter-linearizations-are-normal-iff-surjective`: PASS.** Its "exact reach" consequence is interpretation
  (Section 6.2).
- **`surjunctive-by-amenable-extensions-are-surjunctive`:** OPEN, not decision-level, not reviewed beyond its route
  bookkeeping.

### 6.1 Theorem A. PASS.

**Coordinates.**
- `(n' . x)_q(n) = x(n'^-1 n s_q) = x_q(n'^-1 n)`, so left translation by `N` is the shift in each coordinate.
- **Lemma 2.1.** `n s_q m = n n_(q,m) s_(q mbar)`, so `tau(x)_q(n) = mu((x_(q mbar)(n n_(q,m)))_m)`. This is `N`-equivariant, and
  for `q in F` it reads only coordinates in `F^+ = F Mbar`.
- **The decoder acts coordinatewise.** For `d in S`, `s_q d = (s_q d s_q^-1) s_q` with `s_q d s_q^-1 in N`. So `sigma(y)_q` is an
  automaton `sigma_q` over `N` with memory `s_q S s_q^-1`, and `x_q = sigma_q(tau(x)_q)`.

**The map `Psi`.**
- `Psi(x) = (tau_F(x), x|_(F^+ \ F))` recovers `x_q` for `q in F` through `sigma_q`, and copies the other coordinates. So it is
  injective.
- Its domain alphabet `A^(F^+)` and codomain alphabet `A^F × A^(F^+ \ F)` have the same size.

**The image is proper.**
- Write `w = n_w s_(wbar)`. The pattern of `tau(x)` on `nW` is `(tau_F(x)_(wbar)(n n_w))_w`. It is never `p`, because `X` is
  `G`-invariant and misses `p` at every translate.
- The map `w -> (wbar, n_w)` is injective, so `p` can be placed at `n = e` and the avoiding subshift is proper.
- So `Psi` is strict over `N`, which contradicts surjunctivity of `N` at alphabet size `|A|^|F^+|`.

**Remarks.**
- Remark 2 (the filter) follows: the normal closure of the decoder memory of a strict pair is not surjunctive, hence nonsofic
  and outside `S*`.
- Remark 3 is correct: when `S != {e}` over a simple group, the normal closure is the whole group.

### 6.2 Theorem C. PASS.

1. **The endomorphism.** `(g.f) o tau = g.(f o tau)` because `tau` is equivariant. So `Phi_tau` respects the covariance relation
   `u_g f u_g^* = g.f`, and it is a unital *-endomorphism.
   - The characters `chi_xi` span `LC(A^G)`, and the shift permutes them, so `LC(A^G) x|_alg G = C[Z/q wr G]`.
   - The coefficient of `chi_0` is `integral f d lambda`.
2. **Injective and surjective.** Both statements hold.
   - A clopen subset of the closed set `X` extends to a clopen set of `A^G`, since compact disjoint sets in a zero-dimensional
     space are separated by clopens. Finitely many disjoint extensions can be chosen.
   - `A^G \ X` is open, so it contains a cylinder whenever `X` is proper.
3. **Trace and rank.** `L(L) = L^infinity(A^G, lambda)` with the canonical trace. The support projection of `f o tau` is
   `1_(tau^-1(supp f))`, whose trace is `nu(supp f)`.
4. **The four conditions.**
   - (a) ⇒ (b): bijective automata preserve `lambda`.
   - (b) ⇒ (c): a trace-preserving unital *-homomorphism is isometric on `L^2(tr)` and extends normally.
   - (c) ⇒ (d): inner regularity of `nu` gives a compact `lambda`-null `K` with `nu(K) > 0`. Take clopens `C_k` decreasing to
     `K`. The projections `1_(C_k)` decrease to `0` in the finite algebra, a normal extension preserves decreasing limits, and
     so `nu(C_k) = tr(1_(tau^-1 C_k)) -> 0`. That contradicts `nu(C_k) >= nu(K) > 0`.
   - (d) ⇒ (a): `d nu / d lambda` is invariant, hence constant because Bernoulli shifts over infinite groups are ergodic. So
     `nu = lambda`, and the closed set `X` of full measure is `A^G`.

**Wording point.** The claim's Consequence says that every characteristic-zero argument from traces, Sylvester rank functions
of `L(H)`, or normal structure "proves surjectivity exactly when it proves `nu << lambda`", and that Kaplansky-type positivity
"gives no independent access". These sentences interpret Theorem C; they are not a theorem.
- Only the canonical trace and the von Neumann rank are computed.
- Other Sylvester rank functions on `C[H]` are not addressed.
- The claim node should label the paragraph as interpretation.

**Follow-up.** `w5-free-pos-c` applied the fix at `65cc62684f`, and I checked the diff.
- The Consequence now reads "(proved)": a strict automaton is a surjective, non-injective, non-normal endomorphism.
- The rest is labelled "Interpretation (not part of the theorem)". It names the canonical trace and the von Neumann rank as the
  only functionals computed, and says other rank functions are not addressed.

PASS.

**Wiring point (from `w3-vf-positive`).** `complex-lamplighter-linearization-proof` had `requires: []`, but step (a) ⇒ (b) uses
`bijective-ca-preserve-uniform-bernoulli-measure`. This landing adds that claim to its `requires`.

### 6.3 Theorem B, Proposition 3.1 and Corollary 3.2 (`8e52ae695`): second pass, concurring

This concerns `amenable-extensions-of-uqs-groups-are-surjunctive`.
- `w3-vf-positive` gave the verdict (PASS) in Section 19 of `research/artifacts/w3-vf-positive-verification-2026-09-12.md`, with the
  verdict line on the route.
- This section is an independent second pass, done before its handoff arrived. It adds no verdict line.
- Both passes found the same scope point on directed unions.

**The transplant.**
- The decoder obeys Lemma 2.1: `sigma(y)_q` reads the coordinates `q Sbar`. So for `q` in `F^-` it recovers `x_q` from `tau_F(x)`.
- Storing `x` on `F^+ \ F^-` makes `Psi` injective.

**Tiles.** A maximal disjoint family `q_i Wbar` in `F'` gives `|F'| <= n |Wbar Wbar^-1|`.
- On each tile the transported pattern sits at coordinates `(q_i wbar, n n_(i,w))`.
- The map `w -> (q_i wbar, n_(i,w))` is injective, so `Z_i` is proper.

**Bookkeeping.** `j = |F^+| - n|Wbar|` and `j' = |F| - n|Wbar| + |F^+ \ F^-|`, so `j' - j = |F \ F^-|`.

**Part 1.**
- Right multiplication by `s` maps `F \ F s^-1` onto `F s \ F`, so `|F \ F^-| <= sum_(s in Sbar) |F s \ F| <= |Sbar| eps |F|`.
- In the same way `|F \ F'| <= |Wbar| eps |F|`, and so `n >= (1 - |Wbar| eps)|F| / |Wbar Wbar^-1|`.
- UQS at `B = A^(Wbar)`, `w = |W|`, `D = A` gives the contradiction.

**Part 2.**
- Take `F = I_L R`, with `I_L` an interval of length `L` in a finite-index `<c>` and `R` a right transversal.
- Right multiplication by `s` permutes the cosets and shifts each interval by a bounded amount `a(r,s)`. So `|F s \ F|` is bounded
  independently of `L`, while `n -> infinity`, and AQS gives the contradiction.

**Proposition 3.1.**
- **Subgroups.** The memory lies in `H`, so the same local rule over `N` acts coset by coset, and it is injective.
  - `Y~_i` is closed, `N`-invariant and proper. Changing the base point in a coset is a left shift, which `Y_i` absorbs.
- **Directed unions.**
  - The memory and the finitely many missing windows lie in one `N_k`.
  - Restricting to the coset `N_k` gives an injective automaton over `N_k`. Its target restrictions `Y_i|_(N_k)` miss the same
    patterns.

**Corollary 3.2.**
- `phi(N) = t N t^-1 <= N` makes `t^-k N t^k` increasing.
- The copies are isomorphic to `N`, hence share its constants.
- The kernel onto `Z` is their union, and the quotient `Z` is two-ended.

**Wording point.** Proposition 3.1 and the claim's Heredity line say directed unions keep UQS and AQS "with the same constants".
- As proved, the union inherits the property only when all `N_k` share one `delta(B,w)`, or for AQS one `n_0(B,w,K)`.
- A directed union of UQS groups whose constants tend to `0` is not covered.
- Corollary 3.2 is unaffected, because the copies are isomorphic.
- Please state the uniformity hypothesis.

**Follow-up.** `w5-free-pos-c` stated the hypothesis at `eab68ee41`; I checked the diff.
- Proposition 3.1 is split: part 1 covers subgroups, with the same constants; part 2 covers directed unions whose stages share
  one constant function or threshold function.
- The directed-union proof now notes that `n`, `j`, `j'` and `|D|` are unchanged.
- Corollary 3.2 cites isomorphic copies.
- The Heredity lines of the claim, the route and the UQS node match.
- The lamplighter route keeps its `requires` wiring.

PASS.

## 7. w5-inf-c: deficit-window localization, read bound, self-copy collapse

Lane `w5-inf-c`, landed at `03819c251` and `ea92a4bd1`; artifact
`research/artifacts/rokhlin-window-localization-and-read-bound-2026-09-12.md`. The lane came to this verifier in wave 5
(about 18:25). These are its first verdicts.

**Conventions.** These follow `bernoulli-rokhlin-deficit-has-a-finitary-witness`:
- `x` is iid uniform on `A^k` over `G` and `y_f = psi((x(fe))_(e in E))`.
- `Phi = (1/k)[H(psi(x|_E)) + H(x(1) | y_F)]`, and `rho_q(G) = lim_k h^Rok_G((A^k)^G)/k = inf Phi`.
- "Rokhlin-maximal at `q`" means `h^Rok((A^k)^G) = k log q` for every `k`
  (`bernoulli-rokhlin-maximality-passes-to-subgroups`). Equivalently, `Phi >= log q` for every configuration, which is
  the finitary-witness claim's first consequence.
- `F_1 = F ∩ E^-1` and `H = <E E^-1>`.

### 7.1 `bernoulli-deficit-windows-need-a-non-maximal-difference-subgroup` (Theorem 1.1, Corollaries 1.2–1.3)

Re-derived on paper.

**Dropping codewords.**
- Join `f ~ f'` when `fE ∩ f'E` is nonempty, and let `C` be the union of the components that meet `F_1`.
- For `f` outside `C`, `fE` misses every `f'E` with `f' ∈ C` (otherwise `f` would join that component). It also misses `1`,
  because `f ∉ F_1`.
- So `y_(F \ C)` reads sites disjoint from `CE ∪ {1}` and is independent of `(x(1), y_C)`. Hence `H(x(1) | y_F) = H(x(1) | y_C)`,
  and `Phi` is unchanged. If `F_1` is empty, `I(x(1); y_F) = 0` and `Phi >= log q`.

**One coset.**
- `f e = f' e'` gives `f' = f (e e'^-1) ∈ fH`, so each component lies in one left coset of `H`.
- Each `e^-1 ∈ F_1` equals `e_0^-1 (e_0 e^-1)` with `e_0 e^-1 ∈ E E^-1`. So every component of `C` lies in `e_0^-1 H`.

**Transport.** Put `sigma(s) = e_0 s e_0^-1` and `x'(s) = x(sigma^-1(s))`, again iid uniform.
- Take `E' = E e_0^-1` and let `psi'` be `psi` relabelled.
- For `f ∈ C`, `y'_(e_0 f) = psi'((x'(e_0 f e'))_(e' in E')) = psi((x(fe))_e) = y_f`, and `x'(1) = x(1)`. Under this coupling the
  transported pair equals the original pointwise, not only in law.
- Every read `(e_0 f)(e e_0^-1)` lies in `H`, so `(k, E', e_0 C, psi')` is a configuration over `H` with the same `Phi`.

**Maximal `H`.** The finitary-witness claim over `H` gives `Phi >= log q`.

**Finite `H`.**
- With `C'' = e_0 C`, `|H| k log q = H(x_H) <= H(y_H) + sum_h H(x(h) | y_H) <= |H| H(psi) + sum_h H(x(h) | y_(hC''))`.
- Each `y_h` has the law of `psi'(x|_(E'))`, because `hE'` consists of distinct sites. Also `hC'' ⊂ H`.
- Left translation by `h` inside `H` carries `(x(1), y_(C''))` to `(x(h), y_(hC''))` and preserves the iid law, so each summand is
  `H(x(1) | y_(C''))`. Dividing by `|H| k` gives `Phi >= log q`.

**"So nonsofic".** This is item 4 of `seward-per-group-rokhlin-entropy-of-bernoulli-shifts`: countably infinite sofic groups are
Rokhlin-maximal at every `q`.

**Corollary 1.2.** `E E^-1 = {1, e_1 e_2^-1, e_2 e_1^-1}` generates a cyclic group, and `Z` is sofic. PASS.

**Corollary 1.3.**
- `E ⊂ Kg` gives `e e'^-1 = k k'^-1 ∈ K`.
- `E ⊂ gK` gives `e e'^-1 ∈ g K g^-1`, which is isomorphic to `K` and so Rokhlin-maximal.
- Part 1 of `bernoulli-rokhlin-maximality-passes-to-subgroups` covers infinite `H`; the count covers finite `H`. PASS.

**Third corollary.** For `|E| = 3`, `e_2 e_3^-1 = (e_1 e_2^-1)^-1 (e_1 e_3^-1)`, so `H` is two-generated. PASS.

**Subsumption.** `sofic-radical-localizes-bernoulli-deficit-witnesses` finds an invisible difference inside `<E ∪ F>`. Applied
after the transport, it recovers only the sofic case of Theorem 1.1. The Rokhlin-maximal case and the transport itself are new.

**Wording points.**
- "The smallest possible witness windows have `|E| = 3`" is a lower bound. Every witness has `|E| >= 3`, but nothing shows that a
  window of size 3 witnesses. Suggested: "every witness has `|E| >= 3`, and when `|E| = 3` its difference subgroup is two-generated".
- In the title, "lives in" means after dropping disconnected codewords and conjugating by `e_0`. The original reads lie in
  `e_0^-1 H E`, not in `H`. The body says so; the title could say "can be moved into".

PASS.

### 7.2 `bernoulli-witness-information-is-bounded-by-code-reads` (Theorem 2.1, Corollary 2.2)

Re-derived on paper.
- `f e = 1` iff `f = e^-1`, so exactly `m = |F_1| <= |E|` codewords read `1`.
- `y_(F \ F_1)` reads sites other than `1`, so `I(x(1); y_(F \ F_1)) = 0`. The chain rule then gives
  `I(x(1); y_F) = I(x(1); y_(F_1) | y_(F \ F_1)) <= H(y_(F_1)) <= sum_(f in F_1) H(y_f) = m H(psi)`.
- `H(x(1) | y_F) = k log q - I`. With `t = H(psi)/k`, this gives `Phi >= log q - (m-1)t` and `Phi >= t`.
- For `m >= 1`, `max{t, log q - (m-1)t}` is smallest at `t = log q/m`, so `Phi >= log q/m`. For `m = 0`, `Phi >= log q`.

**Corollary 2.2.** Let `n >= 1` be an integer with `Phi < log q/n`.
- `m = 0` is impossible.
- `log q/m <= Phi < log q/n` gives `m > n`, so `|E| >= m > n`.
- `t <= Phi` gives `H(psi) < k log q/n`. PASS.

**Subsumption.** A grep of main's `research/` for the bound finds nothing else except the Attempts on
`bernoulli-rokhlin-entropy-maximal-for-every-group`, which summarize this lane's results. The claim says plainly that it is
Shannon subadditivity only.

**Wording point.**
- The claim's **Consequence** says "a configuration with `Phi < log q / m` has `|E| > m`". But `m` was bound just above to
  `|F ∩ E^-1|` of that same configuration.
- With that binding the hypothesis never holds, because the theorem gives `Phi >= log q/m`.
- The intended statement uses a free integer, as Corollary 2.2 and step 4 of `self-copy-deficit-unbounded-window-proof` do
  implicitly. Please rename it (for example `n`) in the claim and in Corollary 2.2.

PASS.

### 7.3 `self-copy-host-rokhlin-deficits-need-unbounded-windows` (Theorem 3.1)

Re-derived on paper against the imports as stated on main.
- **Item 1.**
  - `Phi < log q` gives `rho_q(G) < log q`. Since `rho_q` is the limit of `h^Rok((A^k)^G)/k`, some `k` has
    `h^Rok((A^k)^G) < k log q`.
  - Seward's item 1 (finite base, `G` countably infinite) makes that value `min{k log q, h_sup(G)}`. So `h_sup(G)` is finite, hence
    `0` by hypothesis, and `min{H(L), 0} = 0` for every finite base.
- **Item 2.** `rho_(q')(G) = 0 = inf Phi` at `q'`, so configurations with `Phi < ε` exist for every `ε > 0`.
- **Item 3.** This is Corollary 2.2 with a free integer, as in 7.2.
- **Unbounded windows.** For each `n`, item 2 supplies a configuration with `Phi < log q'/n`, and item 3 gives it `|E| > n`.
- **Hypothesis.** The corollary of `rokhlin-supremum-dichotomy-with-centralized-self-copies` gives `h_sup ∈ {0, ∞}` for groups that
  contain their own square and finite subgroups of unbounded order, with the binary Leavitt units and `V` as examples. The
  claim's example sentence matches.

**Corollary 3.2 (artifact only).** `leavitt-zero-rokhlin-supremum-from-strict-automaton` turns a strict automaton over `U` into
`h_sup(U) = 0` directly, which gives conclusions 1–3 without first producing a configuration. It is correct as an implication.
Its prerequisite `leavitt-unit-group-nonsurjunctive` is open, as that route says.

**Section 4 (audit).** It is heuristic and makes no graph claims, and its literature items are flagged as not re-read. The normal
form in 4.4 follows from Seward's item 1 and the dichotomy: on self-copy hosts INF is positivity of `h^Rok(2^U)`, and any
uniform `c > 0` upgrades to `log 2`.

PASS. Nothing in Section 7 is decision-level, and nothing is refuted.

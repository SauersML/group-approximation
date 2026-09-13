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

**Follow-up (`31fe1a4e7`).** w5-inf-c applied both wording points in five files. I checked the full diff.
- **Read-degree consequence.** The claim `bernoulli-witness-information-is-bounded-by-code-reads`, artifact Corollary 2.2,
  Theorem 3.1(3), whose proof now cites Corollary 2.2, self-copy item 3, and the Attempts bullet on
  `bernoulli-rokhlin-maximal-on-fg-simple-kazhdan-groups` all use a free integer `n >= 1` now. Re-derived: `m = 0` gives
  `I(x(1); y_F) = 0`, so `Phi >= log q`, and `Phi < log q/n` forces `m >= 1`. Then `log q/m <= Phi < log q/n` gives `m > n`.
  `F ∩ E^-1 ⊆ E^-1` gives `|E| >= m`, and `H(psi)/k <= Phi` gives `H(psi) < k log q/n`.
- **Witness size.** The deficit-windows claim and artifact Section 1 now read "every witness has `|E| >= 3`, and when `|E| = 3`
  its difference subgroup is two-generated and not Rokhlin-maximal". Correct: `e_2 e_3^-1 = (e_1 e_2^-1)^-1 (e_1 e_3^-1)`.
- **Title.** The new title and `distinct_from` say that the witness moves into `<E E^-1>` after dropping codewords and
  conjugating. The proof sketch puts the original reads in `e_0^-1 H E`. Correct: the connected codewords lie in `e_0^-1 H`.

The Attempts entry `c671f5ac1` on `bernoulli-rokhlin-entropy-maximal-for-every-group` uses `m` for the bound read degree, which
is correct as written. Both OPEN nodes stay OPEN. Follow-up PASS.

## 8. w5-quant-surj: quotient restriction and the quantitative surjunctivity residue (`b19ca5490`, `bbaa36844`)

The artifact is `research/artifacts/quantitative-surjunctivity-residue-2026-09-12.md`. The lane drafts were byte-identical
to main for all five nodes and for Sections 1–2 of the artifact, so the derivation below is against main.

**Conventions.**
- Automata are `tau(x)(g) = mu((x(gm))_(m in M))`, and left translation is `(h.x)(g) = x(h^-1 g)`.
- `Fix_H` is the set of configurations constant on the right cosets `Hg`.
- QS is as defined on `surjunctive-groups-are-quantitatively-surjunctive`: for every `B`, proper `Y`, `D`, `n >= 1` and
  `j, j' >= 0`. This matches Section 0 of the artifact.

### 8.1 `product-automata-images-contain-fibre-invariant-configurations` (Proposition 1.1). PASS.

- **Restriction.** `N x 1` is normal with quotient `(G/N) x K`, so `Fix_(N x 1)` is translation invariant and `tau` maps it
  into itself. Put `x(g,k) = y(gN,k)`. Then `tau(x)(g,k) = mu((y(g g_m N, k k_m))_m)`, since `(gN)(g_m N) = g g_m N`. This is
  an automaton over `(G/N) x K` with memory `{(g_m N, k_m)}`. It is conjugate to a restriction of `tau`, so it is injective,
  and it is onto when `(G/N) x K` is surjunctive. So `Fix_(N x 1)` lies in `X`. This is part 4 of
  `injective-automata-restrict-to-schreier-graph-automata` at `H = N x 1`, as the node's `distinct_from` says.
- **Cases.** A pattern extends to `Fix_(N x 1)` iff it is constant on each `(gN x {k}) cap E`. The case `N = G` gives the first
  case and single fibres. When `K` and `G/N` are sofic, `(G/N) x K` is sofic, and `sofic-groups-are-surjunctive` gives the
  second case.
- **Filter.** A Garden of Eden pattern does not extend, so it differs at two sites `(g,k)` and `(g',k)` with `gN = g'N`, that is
  `g' g^-1 in N`.
- **Single fibres.** `strict-product-automata-have-no-single-fibre-garden-of-eden` concludes that patterns on `{g} x F` are
  realized. The case `N = G` gives this for every `G` once `K` is surjunctive, so the paragraph added to that node is correct.
  The symmetric statement follows with `1 x K`.
- **Theorem Q.** `Y` misses a point of `Fix_N` iff `p` extends to `Fix_(N x 1)`.
  - *If:* the column configuration of an extension lies in `Fix_N` and shows `p` at `1`.
  - *Only if:* translating a witness by `g^-1` keeps it in `Fix_N`, because `g N g^-1 = N`, and padding off `G x E_K` keeps it
    invariant.
  - So the subshift of a Garden of Eden pattern contains `Fix_N` for every `N` with `G/N` sofic.

### 8.2 `quantitative-surjunctivity-constants-lift-from-quotients` (Proposition 2.1, Corollaries 2.2–2.5). PASS.

- **Lift.** An injective `Phi` into `Y^n x (D^(j'))^G` commutes with translations. So it maps `Fix_N` of the source into
  `(Y cap Fix_N)^n x Fix_N((D^(j'))^G)`. `G` acts on `Fix_N = B^(G/N)` through `G/N`, so `Y_N` is a subshift, and it is proper
  because `Fix_N` does not lie in `Y`. The restriction is an injective automaton over `G/N` with memory `MN/N` and the same
  parameters, and a constant of `Y_N` excludes it.
- **Constants.** Constant configurations go injectively to constant configurations. So `|B|^n |D|^j <= c_Y^n |D|^(j')`, that is
  `(j'-j) log|D| >= n log(|B|/c_Y)`. When `c_Y = 0` there is no equivariant map at all.
- **Periodic points.** For `H` of index `m`, `Fix_H` has `(|B|^n |D|^j)^m` source points and `|Per_H(Y)|^n |D|^(j' m)` target
  points. Dividing the logarithms by `m` gives the displayed constant.
- **Residually finite groups.**
  - Choose `W` injecting into `G/H`. Then periodic points avoid `r` on every window `gW` of `G/H`.
  - A point lies in at most `|W|` windows, so a window meets at most `|W|^2`. Greedy selection gives `s >= m/|W|^2` disjoint
    windows whose constraints are independent, so `|Per_H(Y)| <= |B|^m (1 - |B|^(-|W|))^s`.
  - Corollary 2.3 then gives at least `-log(1 - |B|^(-|W|))/|W|^2`, and a smaller positive number is still a constant. The
    constants displayed on the node match.
- **Residue.** It follows from Proposition 2.1 and the sofic count `-log(1 - |B|^(-|W|))/(|W|^2 + 1)`.
  - For sofic `G` the residue is empty.
  - If `G` has no nontrivial sofic quotient, `Nsof(G) = {G}`, and the residue is the proper subshifts containing all constant
    configurations.
- **Dependency point (no change needed).** The residue bullet uses the sofic count. That count exists only as prose on the
  OPEN target node and in Section 3 of the fibre artifact, verified in `w3-vf-positive` Section 16.3, and is not an
  ESTABLISHED node.
  - The node says so. The route `quotient-restriction-deficit-proof` rightly covers only Proposition 2.1 and Corollaries 2.2–2.4.
  - With "`G/N` quantitatively surjunctive" in place of "`G/N` sofic", the residue statement needs nothing imported.
- **Subsumption.** None of the 137 surjunctivity titles on main lifts QS constants from quotients or gives the residually
  finite constant. The closest is the sofic count on the target node. Corollary 2.4 reproves its residually finite case with
  `|W|^2` in place of `|W|^2 + 1`.

### 8.3 Sections 3–5 (prose Attempts, `bbaa36844`)

I checked these on paper. They make no graph claims.
- **Proposition 3.1.** An injective `tau` that is not onto is the case `n = 1`, `j = j' = 0`. Conversely, composing with an
  injective symbol map `D^(j') -> D^j` gives an injective automaton that is not onto, since `Y^n` is proper.
- **Sections 4.1–4.5.** Proposition 3.1 forces `|D_i| >= 2` and `j'_i > j_i`, so `m_i >= log 2` and `n_i -> infinity`. The
  bit-interleaving map is injective and equivariant. Sections 4.2 and 4.3 are correct as prose: constant configurations block
  recoding. So is Section 4.5: fixed-point fractions bounded away from `1`, amplified by tensor powers, give soficity.
- **Proposition 5.1.**
  - Part (1) projects the memory to `G`, and the converse is `surjunctivity-passes-to-subgroups`.
  - Part (2) is `products-with-lef-permanence-closure-factors-are-surjunctive`, whose `P(G)` contains every LEF group.
  - Both implications around the candidate equivalence are correct.
- The Attempts added to `surjunctive-groups-are-quantitatively-surjunctive` match these sections.

PASS. Nothing in Section 8 is decision-level, and nothing is refuted.

**Follow-up (`82a4dbf6c`).** w5-quant-surj applied the dependency point to the node and the artifact. I checked the full diff.
- **Residue bullet.** Take a proper subshift that misses a point of `Fix_N`, for a normal `N` with `G/N`
  quantitatively surjunctive. It has a constant by Proposition 2.1. Every proper subshift either misses such a point
  or contains all those `Fix_N`, which gives the iff. Nothing is imported.
- **Sofic quotients.** Only the sub-bullet saying that sofic quotients qualify uses the sofic count, and it names
  where the count is recorded.
- **Simple groups.** The normal subgroups are `1` and `G`.
  - Using `N = 1` needs `G` itself to be quantitatively surjunctive, so it assumes the conclusion.
  - `N = G` needs only the trivial quotient, whose constant `log(|B|/c_Y)` is Corollary 2.2.
  - So `G` is quantitatively surjunctive iff every proper subshift containing all constant configurations has a
    constant. For nonsofic simple groups this matches the old statement.
- **Artifact.** The new paragraph "Import-free form" is Corollary 2.5 with `Nsof(G)` replaced by the normal subgroups
  with quantitatively surjunctive quotient. Correct.

The old sub-bullet covered every group with no nontrivial sofic quotient. The new one covers only simple groups,
which is narrower. The other groups still get the same reduction from the main bullet with `N = G`. I updated the
note on `quotient-restriction-deficit-proof` to match. Follow-up PASS.

## 9. w7-inf-uniform: random-order window transport and the codeword Følner count (`d71ae9349`)

The artifact is `research/artifacts/rokhlin-window-random-order-transport-2026-09-12.md`. I re-derived everything
against main.

**Conventions.**
- The translation rules `y_h(T_g x) = y_(gh)(x)` and `past_(T_g U)(h) = g^-1 past_U(gh)` are correct.
- The finitary witness node gives `rho_q(G) = lim_k h^Rok((A^k)^G)/k = inf Phi`. Its configurations allow `F` to be empty.

### 9.1 `rokhlin-window-random-order-transport-identity` (Theorem 1). PASS.

- **Chain rule.** Fix distinct labels `u` and take the chain rule over `F` in increasing order. `F ∩ past(f)` is exactly
  the set of earlier codewords. `U` is independent of `x`, so integrating gives the `U`-conditioned sum.
- **Translation.** The `f`-term is a functional of the law of `(x, U)`. Under `T_(f^-1)`:
  - `x(1)` goes to `x(f^-1)`, and `y_f` goes to `y_1`;
  - a codeword `y_h` with `U_h < U_f` goes to `y_(f^-1 h)` with `U_(f^-1 h) < U_1`;
  - conditioning on the translated labels is conditioning on `U`.
  
  The law is invariant, so the term is `I(x(f^-1); y_1 | y_(f^-1 F ∩ past(1)), U)`.
- **Check on `Z`.** In the chain-rule frame each reader's term is `1` exactly when the other reader comes later. That has
  probability `1/2`, so the total is `1` bit.
- **`Z/5` calibration.**
  - `(1 + s + s^2)(s + s^2 + s^4) = s + s^5 + s^6 = 1` modulo `s^5 - 1`, and directly `y_1 + y_2 + y_4 = x(0)`.
  - The readers of `0` are `0`, `3` and `4`.
  - Take an order whose first three codewords are `4 < 1 < 2`. The pair `(y_4, y_1)` is uniform and independent of
    `x(0)`, since `x(4)` masks `y_4` and `x(2)` masks `y_1`. So the terms of `4` and `1` vanish, and the term of the
    non-reader `2` is `H(x(0) | y_4, y_1) = 1` bit. Correct.
  - **Wording (optional).** The example should name `F` (for instance `F = Z/5`) and say that `4, 1, 2` come first.
- **Subsumption.** I scanned all 236 Bernoulli and Rokhlin titles on main without truncation, then the 41 about
  transport, orders, decoding, Følner sets or linear codes. The closest is `injective-ca-random-order-transport-identity`,
  which splits the constant `log |A|` over a decoder memory, as the node's `distinct_from` says. Nothing subsumes either
  claim.

### 9.2 Corollary 2 and the two equivalence routes. PASS.

- **Part (1).** `k Phi = H(y_1) + k log q - I(x(1); y_F)`, so `Phi >= log q` is `I <= H(y_1)`. By the finitary witness
  node, maximality is `Phi >= log q` for every configuration. With Theorem 1 this is (D).
- **Part (2).** Here `I <= min{k log q, C H}`.
  - If `C H >= k log q`, then `k Phi >= H >= k log q/C`.
  - Otherwise `k Phi >= k log q - (C-1) H >= k log q/C`.
  - The artifact's strict `>` in the second case is an equality when `C = 1`, which is trivial.
- **Overshoot.** `Phi <= log q/C` gives `H <= H + r <= k log q/C`. So `I = k log q - r >= k log q (1 - 1/C) + H >= C H`.
  Correct.
- **Self-copy hosts.** The target node records `h^Rok(L^G) = min{H(L), h_sup(G)}`. So `rho_q >= log q/C > 0` forces
  `h_sup > 0`, and on a host with `h_sup ∈ {0, ∞}` that is INF. Correct.
- **Routes.** Both pass.
  - `bernoulli-maximality-via-rokhlin-window-domination` combines domination, the identity and the finitary witness node.
  - `rokhlin-window-domination-from-bernoulli-maximality` combines `rho_q <= Phi` with the identity.
  - The cycle between the two OPEN nodes is a normal form and supports neither.
- **Non-reader order.** The non-reader codewords are jointly independent of `x(1)`, so their terms vanish when they come
  first. That order depends on the site and is not translation-invariant. Correct.

### 9.3 Propositions 3 and 4 and Example 5 (Attempts on the OPEN node). Correct.

- **Proposition 3.**
  - Given `x(1)`, the codewords read disjoint coordinates. So `I(X; Y_F) = H(Y_F) - sum H(Y_f | X) <= sum I(X; Y_f)`.
  - By translation each term is `I(x(f^-1); y_1)`, and the `f^-1` are distinct elements of `E`.
  - For independent inputs `I(X_e; Y | X_(<e)) = I(X_e; Y, X_(<e)) >= I(X_e; Y)`. So the sum is at most
    `I(x|_E; y_1) = H(y_1)`.
  - The dichotomy for witnesses is correct, and removing codewords only raises `H(x(1) | y_F)`.
- **Proposition 4.**
  - Given `y_F`, the input is uniform on a coset of `ker L`. So `I = (k - dim pr_1 ker L) log q = (dim V) log q`.
  - A functional vanishing on `ker L` factors through `L`.
  - On a constant input `c` every codeword outputs `Psi c`. So `phi = (Lambda ∘ diag_F) ∘ Psi`, and
    `dim V <= rank Psi <= rank psi`, while `H(y_1) = (rank psi) log q`.
  - Correct, using no group structure. It contains Remark 3.2 of the route artifact, the case `k = 1` with `q` prime.
- **Example 5.**
  - `H(psi) = t + 1`. Given the pointers, the unrevealed center coordinates are uniform and independent, so
    `H(x(s) | y_F) = k (1 - 1/k)^M <= k e^(-M/k) <= 1/k` once `M >= 2 k ln k`.
  - In a group only `f = s e_0^-1` reads `s` at position `e_0`, so the star occurs in no group.
  - With `m = M`, the read-degree bound `1/m` is within a factor `O((log m)^2)` of `Phi`. Correct.

### 9.4 `bernoulli-window-codeword-folner-ratio-bound` (Proposition 6). PASS.

- **Count.**
  - `H(x|_S) <= H(y_(SF)) + sum_s H(x(s) | y_(sF))`.
  - `T_s` carries `(x(1), y_F)` to `(x(s), y_(sF))`, so each term is `r`.
  - With `H(y_(SF)) <= |SF| H(y_1)`, dividing and taking the infimum gives `k log q <= lambda H + r <= lambda k Phi`.
- **Amenability.**
  - Put `K = F f_0^-1`, which contains `1`. Then `|SF| = |SK|` and `S ⊆ SK`. So `|SK| <= (1+eps)|S|` gives
    `|Sk \ S| <= eps |S|` for each `k in K`.
  - Right multiplication by `K` preserves the left cosets `g<K>`. Averaging over them gives a piece `S_g` with
    `sum_k |S_g k \ S_g| <= |K| eps |S_g|`, so `g^-1 S_g` is a right Følner set of `<K>`.
  - Conversely, a right Følner set gives `|SK| <= (1 + |K| eps)|S|`.
  - `<K> = <F F^-1>`, because `f f'^-1 = (f f_0^-1)(f' f_0^-1)^-1` and `K ⊆ F F^-1`. Correct.
- **Wording (optional).**
  - Configurations allow `F = ∅`, where `lambda = 0`. The display still holds, but `Phi >= log q/lambda(F)` needs `F`
    nonempty. When `F` is empty, `Phi >= log q` holds directly.
  - Likewise `Phi >= log q/min{m, lambda(F)}` needs `m >= 1`.
- **Subsumption.** No node bounds `Phi` through `<F F^-1>`.
  - The difference-subgroup filter constrains `<E E^-1>`.
  - `rokhlin-maximality-ascends-co-amenable-subgroups` concerns a subgroup of `G`.
  - The `distinct_from` entries are accurate, and the node's displays match.

### 9.5 Sections 6–8 (prose). Correct, apart from one quotation I did not check.

- **Proposition 7.**
  - Bernoulli shifts over infinite groups are ergodic, so `h^Rok = inf H(alpha)` over generating partitions.
  - For generating `alpha`, `h^Rok <= h^ro(alpha) <= H(alpha)`.
  - With `rho_q = lim_k h^Rok((A^k)^G)/k` and `h^Rok((A^k)^G) <= k log q`, the equivalence is correct given the quoted
    theorem. Inverting `L_xi` preserves its law.
  - I did not check the quotation against Alpeev's paper. No ESTABLISHED node relies on it.
- **Example 8.**
  - `h ∈ gE \ past(g)E` iff `g` is `U`-least in `h E^-1`.
  - The transport `m(g,h)` is diagonally invariant, and the mass transport principle gives
    `E |E \ past(1)E| = E sum_g m(g,1) = 1`.
  - `gamma` of the route artifact's Proposition 4 is the copy code on `S`. Correct.
- **(6.3).**
  - The chain rule along the order, translation on `T°`, and `H(y_1)` on the boundary. `delta_W` decreases to
    `h^ro(y_1)` by martingale convergence, and the amenable conclusion is correct.
  - The label order on a countably infinite set is almost surely dense without endpoints. Correct.
- **Section 8.**
  - Items 1, 2, 4 and 5 follow from the read-degree bound, Proposition 6, Proposition 4, and Corollary 2 with
    Proposition 3.
  - Items 3 and 6 are nodes checked in Section 7.
- **Attempts.** The entries on `bernoulli-rokhlin-entropy-maximal-for-every-group` and
  `injective-ca-random-order-transport-is-dominated` match the artifact.

PASS. The target and `rokhlin-window-transport-is-dominated` stay OPEN. The domination node is a normal form, so nothing
here is decision-level, and nothing is refuted.

**Follow-up (`0a977f4e8`).** The lane took up the optional points.
- Corollary 2(2) now uses `>=`, which is right: the two sides are equal at `C = 1`.
- The `Z/5` calibration names `F = Z/5` and an order that starts `4 < 1 < 2`.
  - The readers of site `0` are `0`, `3` and `4`.
  - `x(4)` enters `y_4` but not `y_1`, and `x(2)` enters `y_1` but not `y_4`. So `(y_4, y_1)` is uniform and
    independent of `x(0)`, and the terms of `4` and `1` vanish.
  - Since `x(0) = y_1 + y_2 + y_4`, the term of `2` is `H(x(0) | y_4, y_1) - 0 = 1` bit.
- Proposition 6 and the Følner node now state the empty cases.
  - For `F = ∅`, `lambda = 0` and `H(x(1) | y_F) = k log q`.
  - For `m = 0`, `y_F` depends only on `x` off site `1`.
  - Both give `Phi >= log q`.
- The two ESTABLISHED nodes cite Sections 9.1 and 9.4. The artifact's status section records that the Seward quotation
  was not checked.

Follow-up PASS.

## 10. w6-free-pos-d: the coprime transfer to finite-stabilizer coset shifts (`3bf9dea0d`, `22506cf72`)

`finite-stabilizer-coset-shifts-inherit-surjunctivity` is OPEN. Its Status bullet for `gcd(m, |H|) = 1` names this
verifier. This section checks Theorem 1 and its remarks (artifact Section 1), then Section 2 and the node's Attempts.
The claim has no proof route on main, so the verdict appears only here.

### 10.1 Theorem 1 (coprime transfer). PASS.

- **Identification.** `iota(g.y)(k) = y(g^-1 kH) = iota(y)(g^-1 k)`. `iota` is a continuous bijection from a compact
  space onto `Y`, so it is a homeomorphism.
- **Averaging.**
  - `P` commutes with the shift, because right multiplication by `h` commutes with left translation.
  - `P(z)(kh') = P(z)(k)` by the reindexing `h -> h'h`, and `P(y) = c|H| y = y` on `Y`.
  - So `P^2 = P` with image `Y`, and `z = Pz + (z - Pz)` splits `X = Y ⊕ ker P`.
- **Extension.**
  - `tau o P` and `z -> z - Pz` are continuous and equivariant, since the shift acts by group automorphisms.
    Curtis–Hedlund–Lyndon holds for every group, so `Phi` is an automaton.
  - `P(Phi z) = tau(Pz)`, because `P` is additive and fixes `tau(Pz) in Y`.
  - Injectivity, `Phi(X) ∩ Y = tau(Y)` and the preimage `z = u + (t - Pt)` all re-derive as written.
  - `Phi` restricted to `Y` is `tau`, which gives the other direction of the node's "injective iff".
- **Remarks.**
  - *Memory:* `tau(Pz)(k)` reads `Pz(kf)`, which reads `z(kfh)`. With `z - Pz` reading `H`, the memory is `FH ∪ H`.
  - *Several orbits:* each `P_i` needs its own inverse of `|H_i|`, and `Phi` acts on `(A^r)^G`. So the hypothesis is
    needed at size `m^r`, as stated.
  - *No per-`H` converse:* over `Z/2 × Z` the normal subgroup `H = Z/2` acts trivially on `B^(G/H)`. An injective
    equivariant `F` would give `F(h.z) = F(z)`, so `h.z = z` for every `z`, which fails.
  - Section 0's restriction argument needs `Y ≠ X`, which holds for `H ≠ 1` and `m >= 2`.
- **Wording (optional).** The node says "a group" and the artifact "a countable group". The proof never uses
  countability, so both are fine.
- **Subsumption.** 24 nodes on main mention coset shifts. None transfers surjunctivity to self-maps of a
  finite-stabilizer coset shift.
  - `compressed-coset-shifts-carry-strict-equivariant-embeddings` needs `u H u^-1` properly inside `H`, which is
    impossible for finite `H`.
  - `site-pullbacks-strict-iff-stabilizer-self-compressed` concerns one-site maps.
  - `full-shift-maps-to-infinite-stabilizer-coset-shifts-are-constant` and
    `bernoulli-factors-to-infinite-stabilizer-coset-shifts-trivial` need infinite stabilizers.
  - `invariant-output-injective-ca-need-torsion` and `invariant-output-injective-automata-need-invisible-symmetry`
    concern automata from `X` into `Y`.
  - `wreath-surjunctivity-reduces-to-stabilizer-products` concerns wreath products.
  - The cited ids exist, and the node's Status bullets match Theorem 1.

### 10.2 Section 2 and the Attempts (shared prime). Correct.

- **Lemma 2.**
  - Cauchy gives `h` of order `p` in `H` and `a` of order `p` in `A`, since `p | m = |A|`.
  - On `F' = <h>F`, the map `f -> hf` has orbits of size exactly `p`.
  - The sites `k h^i r` are distinct. `z(k h^i r) = a^i` gives `z(khf) = z(kf) a`, including the wrap at `i = p - 1`.
  - Output in `Y` and equivariance under constants give `mu'(w) = mu'(wa) = mu'(w) a`, so `a = 1`. Correct.
  - *Also:* at `k = 1` the enlargement can be skipped. Put `z(hx) = z(x) a` on every orbit of `x -> hx` in `G`. Then
    the window at `h` is the window at `1` times `a`, whatever the memory.
- **Corollary 3.** `(Qz)c in Y`, and `zc = ((Qz)c)(z (Qz)^-1)` uses commutativity. Correct.
- **The three properties.**
  - Step 3 of Theorem 1 is the splitting property with `y = tau(Pz)`.
  - Step 5 uses that `P` has image `Y` and fixes `Y`.
  - Step 6 uses splitting and commutativity. Correct.
- **Wording (optional).** "has to depend on `tau`, or has to leave the shape" says more than is shown. Corollary 3
  shows that the proof of Theorem 1 cannot run with a `tau`-independent `P`. It does not show that every
  `tau`-independent extension of that shape fails.
- **Min retraction.** The fibre over base `b` has `(m-b)^|H| - (m-b-1)^|H|` points, and the section limits its
  conclusion to blockwise gauges. Correct.
- **Amenable hosts.**
  - `Y` is of finite type, through the two-cell patterns on `{k, kh}`.
  - `Y` is strongly irreducible with gap `H`: `F_1 H ∩ F_2 H` is empty iff `F_2 ∩ F_1 H` is.
  - `tau(Y)` is conjugate to `Y`, so it has the same entropy.
  - Over amenable groups, a strongly irreducible subshift has no proper subshift of full entropy. This is standard,
    and I did not re-read the source either. Correct.
- **Node Attempts.**
  - *Linear averaging:* with memory `H`, output in `Y` forces equal coefficients (reindex by `h -> h'h`), and fixing
    `Y` forces `c|H| = 1` mod `m`. Correct.
  - *Translation-equivariant retractions* is Lemma 2 with `A = Z/m` and `a = m/p`.
  - `22506cf72` dropped the two "(to land)" markers, matching Section 2.

PASS for Theorem 1. The claim stays OPEN at a shared prime. A transfer lemma between two surjunctivity properties is
not decision-level, and nothing is refuted. The Status bullet can cite Section 10.1 in place of "unverified".

### 10.3 Section 3: reduction to subgroups of index coprime to `m` (`4bcbfcf5b`, `2a0a1cbba`). PASS.

- **Theorem 4.**
  - `P(z)(k) = c sum_(hS) z(kh)` is well defined on `Y_S`, since `z(khs) = z(kh)`.
  - `hS -> h'hS` permutes `H/S`, so `P(z) in Y_H`. On `Y_H` the sum is `[H : S] z(k)`, so `P` fixes `Y_H`.
  - `Pz in Y_H ⊆ Y_S` and `z - Pz in Y_S`, so `Phi` maps `Y_S` to itself.
  - `P(Phi z) = tau(Pz)`, and `Phi z in Y_H` iff `z = Pz` iff `z in Y_H`. The preimage `u + (t - Pt)` lies in `Y_S`.
    Steps 3 to 6 of Theorem 1 run inside `Y_S` as claimed. Correct.
- **Corollary 5.**
  - A strict `tau` on `Y_H` gives a strict `Phi` on `Y_S`, so the claim at `(G, S, m)` gives it at `(G, H, m)`.
  - Indices multiply, so a single step to a minimal `S` suffices.
  - For `m = p^k` the minimal subgroups are exactly the `p`-groups. A group that is not a `p`-group has a proper Sylow
    `p`-subgroup of index coprime to `p`, and proper subgroups of a `p`-group have index a positive power of `p`.
  - The proper subgroups of `S_3` have index 6, 3 and 2, none coprime to 6. Correct.
- **Remark (one step inside a `p`-group).**
  - `R_h` preserves `Y_N`, because `h^-1 N h = N`.
  - `R_h^p` reads `z(kh^p)` with `h^p in N`, so it is the identity on `Y_N`. For `0 < j < p`, `R_h^j` moves any
    configuration that separates the cosets `N` and `h^j N`, so the order is exactly `p`.
  - `Y_H = Fix(R_h) ∩ Y_N`, since `H = <N, h>`.
  - Every nontrivial `p`-group has a normal subgroup of index `p`, so the step is available along a chain. Correct.
- **Node.**
  - The Status bullet "Reduced to `p`-subgroups over prime-power alphabets" matches Theorem 4 and Corollary 5.
  - The new `distinct_from` entries are accurate.
    - `surjectivity-descends-to-centralized-coset-quotients` restricts an automaton over `G` to `Y_B` for `B`
      centralizing the memory.
    - `finite-normal-subgroups-do-not-affect-surjunctivity` is the two-sided statement across finite normal subgroups.
  - Notes (a) and (b) are applied. Note (c) stays optional.
- **Attempts entry on `finite-normal-subgroups-do-not-affect-surjunctivity` (`2a0a1cbba`).**
  - At normal `N`, `A^(E/N)` is the full shift over `E/N`, and its `E`-equivariant self-maps are the automata over
    `E/N`. Theorem 1 at `H = N` gives the quotient direction at sizes coprime to `|N|`, with no separation hypothesis.
    Correct, and the citation of Section 10.1 is right.
  - `separated-finite-normal-subgroups-preserve-surjunctivity` needs separation, and
    `strict-automata-memory-keeps-finite-normal-kernel-residual` concerns the other direction. So the entry records
    something new.
  - *Wording (optional).* "the averaging has no equivariant replacement" says more than Lemma 2 shows.
    - Lemma 2 rules out retractions that commute with constants.
    - The min retraction is a `G`-equivariant retraction onto `Y`.
    - The node's Status line "The averaging step has no replacement there" has the same issue.

### 10.4 Section 4: the linear shadow (`faca304bb`). PASS.

- **Lemma 6.**
  - `(f^* (g.y))(v) = y(g^-1 f v) = (g . f^* y)(v)`, and `f^*` reads `y` on `g . supp w_i`.
  - Conversely, `(Ty)(H e_i)` is a linear functional of finitely many coordinates, so it equals `y(w_i)`.
    - Equivariance under `H` gives `y(h^-1 w_i) = y(w_i)` for all `y`, so `w_i` is `H`-fixed.
    - So `f(gH e_i) = g w_i` is well defined, and `f^* = T` by equivariance.
  - For algebraic duals, `ker f^* = ann(im f)` and `im f^* = ann(ker f)`. The second follows by extending functionals
    from a complement. Correct.
- **Proposition 7.**
  - `he = e`, so `ge` depends only on `gH`, and distinct cosets give disjoint supports. So `K[G]e ≅ K[G/H]`.
  - `K[G] = K[G]e ⊕ K[G](1 - e)` makes `M` a summand of `K[G]^n`.
  - The split surjection `f` gives `K[G]^n ≅ K[G]^n ⊕ ker f`, and the projection has a section.
  - Stable finiteness turns `psi s = 1` into `s psi = 1`, so `ker f = 0`. Correct.
- **Endomorphism ring.**
  - `f` is determined by `f(H) in M^H`, whose basis is the orbit sums over `H\G/H`.
  - Up to the opposite ring, that is the Hecke algebra. When `char K` does not divide `|H|`, it is the corner
    `eK[G]e`. Correct.
- **Lemma 8.**
  - Restriction to `H` preserves projectivity, since `K[G]` is free over `K[H]`.
  - The orbit `{H}` gives the trivial module as a summand.
  - A splitting of the augmentation would give an `H`-fixed vector `c sum_h h` with augmentation `c|H| = 0 ≠ 1`.
    Correct.
- **Question 9.**
  - Theorem 4 runs over `K` with `c = [H : S]^-1` and keeps linearity and finite memory, so the Sylow reduction holds.
  - `stable-finiteness-forces-prime-power-surjunctivity` exists and is OPEN, as cited.
  - The normal-Sylow case follows from the reduction and Proposition 10. Correct.
- **Proposition 10.**
  - With `H` normal, `K[G]` acts on `K[G/H]^n` through `K[Q]`, and the module is free. A surjection has a section,
    which gives `AB = 1` in `M_n(K[Q])`.
  - The direction of `finite-normal-p-subgroups-preserve-modular-stable-finiteness` used here, from `K[G]` to `K[Q]`,
    has a short proof.
    - Lift `A` and `B` to `M_n(K[G])`. Then `A'B' = 1 + j`, with `j` in the nilpotent kernel, so `1 + j` is invertible.
    - Stable finiteness of `K[G]` gives `B'(1 + j)^-1 A' = 1`, and reducing gives `BA = 1`. Correct.
  - I did not re-check the rest of that node. Its verifier is `w3-vf-positive`.
- **Where it stops.**
  - `zxH = f(zH) = H`, so `zx - 1` lies in the kernel `K[G] I_H` of `K[G] -> K[G/H]`.
  - In `<a> * <b>` with `p = 2`, choose `a` from the first factor and `ba` from each of the other `k` factors. This
    gives `a(ba)^k = (ab)^k a`. Every other choice gives a shorter word, so the coefficient is `1`. Correct.
  - *Wording (optional).* "Question 9 holds there" is shown only for finite `K`, by the amenable case. The section
    does not prove it for infinite `K`.
- **Subsumption.** A title scan for stable finiteness, linear automata and permutation modules gives 113 nodes. None
  contains Proposition 7 or 10.
  - `linear-invariant-output-automata-fail-augmentation` is the nearest, and it is cited. It classifies linear automata
    from the full shift `k^G` into `Y`: augmentation rules them out when `p` divides `|H|`, and they are corner
    compressions otherwise. Section 4 concerns self-maps of `K^(G/H)`. So Lemma 8 is a module-theoretic relative of
    that node's item 2, not a copy of it.
  - `finite-normal-p-subgroups-preserve-modular-stable-finiteness` is used by Proposition 10, as cited.
  - `weak-sofic-stable-finiteness-from-surjunctivity` goes the opposite way, from surjunctivity of `G` to stable
    finiteness.
- **Node.** The linear-shadow Attempts bullet matches Section 4 and says "unverified". It can cite Section 10.4.

PASS for Theorem 4, Corollary 5, Lemmas 6 and 8, and Propositions 7 and 10. The claim stays OPEN at a shared prime, and
Question 9 stays open for non-normal `H`. Nothing here is decision-level, and nothing is refuted.

**Follow-up (`6ce9885b8`).** The lane applied the three optional notes. I checked the diff against Sections 10.2 to 10.4.
- (a) At a shared prime, the finite-normal Attempts entry and the claim node's Status now say that no retraction onto
  `Y` commutes with constants, so the averaging proof does not run. This follows from Lemma 2.
  - Let `Q` be an automaton into `Y` that commutes with constants. Take `h` of order `p` in `H`, `a` of order `p` in
    `A`, and `z` with `z(hx) = z(x)a`. Then `Q(z)(1)a = Q(z)(h) = Q(z)(1)`, so `a = 1`, a contradiction.
  - The Status adds that other automaton retractions onto `Y` exist, such as min, and that no extension of `tau`
    through one is known. That is accurate.
- (b) Artifact Section 4 now limits "Question 9 holds there" to finite `K`, which is what the amenable case gives.
- (c) The Status bullets for artifact Sections 3 and 4 now cite Sections 10.3 and 10.4.

The three blobs on main are the ones at `6ce9885b8`. Follow-up PASS.

## 11. w7-quant-residue: markers on subshift tracks (`d58fa0f32`)

This landing has two ESTABLISHED claims, and both proof routes get verdict lines. The source is
`research/artifacts/quantitative-surjunctivity-rokhlin-markers-2026-09-12.md`.

### 11.1 Theorem R (`subshift-track-injections-lower-rokhlin-entropy`). PASS.

- **Normalization.**
  - If `Y_i` misses `r` on `W`, the pattern of `g.y` on `w_0^-1 W` at `w_0^-1 w` is `((w_0 g).y)(w)`. So `Y_i` misses
    the translated pattern.
  - `|W|` is unchanged, and `W W^-1` is replaced by a conjugate.
  - If the translation is chosen per set, `m` does not grow.
- **Amplify and transfer.**
  - `Phi^(k)` has `nk` tracks, the same windows and deficit `k Sigma`.
  - `Phi` is a Borel isomorphism of `(X, u)` with `(Phi(X), nu)`.
  - Freeness transfers, since `g.Phi(x) = Phi(x)` forces `g.x = x`.
- **Markers.** Step 2 of Section 1 of `gottschalk-rokhlin-entropy-route-2026-09-12.md`, re-checked.
  - The sets `W_j` cover `Z_0`, and `g.W_j ∩ W_j` is empty for `g in S`.
  - The greedy `C_n` are independent (cases `m < n`, `m > n`, `m = n`) and maximal. So `(1 + |S|) nu(C) >= 1`, by
    invariance.
  - `w^-1.c = w'^-1.c'` gives `c' in (W W^-1).c`, so `w = w'`. The blocks are disjoint, and each `y in B_W` has
    exactly one `w in W` with `w.y in C_W`.
- **Generating.**
  - `y in B_W` iff some `alpha_W(w.y)` with `w in W` carries the tag `o`, and that `w` is unique.
  - `(w.y)_i(w) = y_i(1)`, so `beta` is measurable for the invariant sigma-algebra of `alpha`.
- **Entropy.**
  - On `C_W`, each `y_i|_W != r_i` (take `g = 1`), so there are at most `(b^|W| - 1)^|T_W|` values.
  - Conditioning on the three sets gives `s|T| log(b^|W| - 1) + (1 - |W| s)|T| log b = |T|(log b - s eta_W)`.
  - `s >= 1/|W W^-1|`. Summing over the windows and adding `H(zeta)` gives the bound.
- **Remarks.**
  - Remark 1.1 is correct. Disjoint pairs `{h, t^-1 h}` make `Fix_N` null, and `Phi(x) in Fix_N` iff `x in Fix_N`, by
    injectivity.
  - Remark 1.2 is correct: `|W W^-1| <= |W|^2 - |W| + 1`. I did not re-derive the sofic and periodic constants it
    compares against.
- **Node.**
  - The display matches Theorem R.
  - The case `n = 1`, `j = j' = 0` is Theorem 1 of the second artifact, with the same bound.
- **Subsumption.** A scan of the Rokhlin-entropy and quantitative titles finds no node that states Theorem R.
  - `strict-automaton-lowers-bernoulli-rokhlin-entropy` is the one-track case.
  - `quantitative-surjunctivity-constants-lift-from-quotients` works through invariant configurations.

PASS.

### 11.2 Corollary U and Proposition U' (`maximal-bernoulli-rokhlin-entropy-makes-groups-uqs`). PASS.

- **Threshold.**
  - Item 1 of `seward-per-group-rokhlin-entropy-of-bernoulli-shifts` gives `h^Rok = min{log|A|, h^Rok_sup}`. It is
    ESTABLISHED and imported, not re-derived.
  - So maximality at every `A` means `h^Rok_sup = infinity`.
  - Theorem R at the base entropy gives `k(Sigma - mu) <= m log 3` for all `k`, so `mu >= Sigma`. Correct.
- **Constants.** They match the definitions of UQS in `amenable-extensions-of-uqs-groups-are-surjunctive` (at most `w`
  sites) and of QS in `surjunctive-groups-are-quantitatively-surjunctive` (`Y^n`).
  - `1 - b^-|W_i| <= 1 - b^-w` gives `eta_i >= -log(1 - b^-w)`.
  - `D_i <= w^2`, so `Sigma >= n delta(B, w)`.
  - For one subshift, `Sigma = n eta_W / |W W^-1|`.
  - Correct.
- **Finite groups.**
  - A maximal `C` with `C C^-1 ∩ S_W` empty has `G = C ∪ S_W C`, since `S_W` is symmetric.
  - The windows `c^-1 W` are disjoint, since `C C^-1 ∩ W W^-1 = {1}`.
  - So `|Y_i| <= b^N (1 - b^-|W_i|)^(N / D_i)`, and counting gives `mu >= Sigma`. Correct.
- **Proposition U'.**
  - `k_0(Sigma - mu) > m log 3` is exactly the strict inequality.
  - Below the base entropy, item 1 makes the Rokhlin entropy equal `h^Rok_sup`.
  - For `n = m = 1`, `k_0` is the least integer above `D log 3 / delta`, as in
    `strict-automaton-bounds-rokhlin-supremum`.
  - Correct.
- **Node item 3.**
  - A group that is not QS has, for some `Y`, an injection with margin below `n eta_W / |W W^-1| = Sigma`. So its
    supremum is finite.
  - The collapse to `0` imports `rokhlin-supremum-dichotomy-with-centralized-self-copies`, which I did not re-derive.
- **Artifact item 3** (`G x K` surjunctive) is Theorem Q of the product-fibre artifact applied to item 2. It is imported,
  and the claim node does not assert it.

PASS.

### 11.3 Section 4 (the converse). Correct.

- **Proposition 4.1** is correct.
  - T gives P through Theorem Q, which is imported.
  - T gives C with `K = 1`.
  - C and P together give T.
- **Proposition 4.2.** Both items follow from `products-with-lef-permanence-closure-factors-are-surjunctive`. Correct.
- **Proposition 4.3** is correct.
  - Finite groups meet the margin bound.
  - Not QS gives `mu < Sigma` for some injection, so U' gives a finite supremum.
  - The product statement imports item 3 of Seward.
- **Scope.** The prose on where constructions die is heuristic. The Scope bullets match the titles of the cited nodes,
  but I did not re-check those nodes.

PASS for Theorem R and Corollary U. T, C and P stay OPEN, and no new group becomes QS. Nothing here is decision-level,
and nothing is refuted.

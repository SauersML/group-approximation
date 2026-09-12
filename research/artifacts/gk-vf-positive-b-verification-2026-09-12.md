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

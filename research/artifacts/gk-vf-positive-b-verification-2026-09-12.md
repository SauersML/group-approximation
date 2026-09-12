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

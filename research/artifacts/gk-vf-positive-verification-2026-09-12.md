# Positive-side verification (lane gk-vf-positive)

Lane `gk-vf-positive`, 2026-09-12, verifier for the positive family (`gk-p-*`) and the
free lanes by topic. Every verdict here is an independent re-derivation on paper, not
a rereading of the author's argument. No computation.

## 1. Positive anchors no verifier had covered (main at `75257fdaba`)

Neither `gk-verify-pos`'s artifact nor any earlier verdict mentions these ids.

### 1.1 `end-fixing-tree-symmetries-carry-strict-automata` (gk-rokhlin, landing gk-free's calibration). Verdict: PASS.

Re-derivation.

* **Setting.** `T` is the 3-regular tree, `xi` an end, `p(v)` the neighbour toward
  `xi`, and `Gamma = Aut(T, xi)`.
  * Every `gamma` fixing `xi` maps the ray from `v` to `xi` onto the ray from
    `gamma v` to `xi`. So `gamma p = p gamma`, and `gamma` maps the children of `w`
    onto the children of `gamma w`.
  * `Gamma` is transitive on vertices: hyperbolic automorphisms along lines through
    `xi` move the Busemann level, and elliptic ones fixing a ray act transitively on
    each horosphere.
* **Amenable.** The Busemann character `beta: Gamma -> Z` has kernel the horocyclic
  subgroup. That kernel is the increasing union of the compact open stabilizers of
  the vertices along a ray to `xi`, so it is amenable, and `Gamma` is an extension of
  `Z` by it. This is amenability as a locally compact group, which is all the claim
  asserts.
* **Not unimodular.** Taking vertex stabilizers, the modular function is
  `Delta(gamma) = 2^{±beta(gamma)}`, nontrivial on hyperbolic elements.
* **Strict automaton.**
  * `tau(x)(v) = x(p(v))` is equivariant, reads one site, and is continuous.
  * `sigma(y)(w) = min(y(c), y(c'))` reads the unordered pair of children, so it is
    equivariant for a totally ordered alphabet.
  * On `tau(x)` both children of `w` carry `x(w)`, so `sigma tau = id`, and `tau` is
    injective.
  * A configuration giving two siblings different symbols is not in the image.
  So `tau` is strict.
* **Calibration scope.** The index set is a homogeneous space of a nondiscrete group,
  not the group itself. Over a group acting on itself, the equivariant self-maps of
  the index set are the right multiplications, and they are bijections, so the copying
  mechanism does not exist there. The claim says exactly this and nothing stronger.

### 1.2 `injective-measure-preserving-ca-is-surjective` (gk-other-hosts). Verdict: PASS.

`Y = tau(A^G)` is compact, hence closed. From `tau_* mu_A = mu_A`,
`mu_A(Y) = mu_A(tau^-1 Y) = 1`. The open complement is `mu_A`-null, and the uniform
Bernoulli measure gives every nonempty cylinder positive mass, so the complement is
empty. The converse direction in the artifact also holds: a proper closed image has
open nonempty complement, of positive mass, so `mu_A(Y) < 1 = tau_* mu_A(Y)`.
Injectivity plays no role, as the route body correctly remarks.

### 1.3 `every-injective-ca-preserves-uniform-bernoulli-measure` and its three routes. Verdict: PASS.

* **Window balance.** With encoder memory `M`,
  `tau_* mu_A(C_p) = |A|^-|Omega M| · #{q in A^(Omega M) : tau(q)|_Omega = p}`.
  Two probability measures that agree on all cylinders are equal. So preservation is
  exactly the count `|A|^(|Omega M| - |Omega|)` for every finite `Omega` and every
  `p`, as stated.
* **`gottschalk-via-universal-bernoulli-preservation`.** Valid: 1.2 applied
  automaton by automaton.
* **`bernoulli-preservation-from-gottschalk`.** Valid. Surjunctivity makes each
  injective automaton bijective. `bijective-ca-preserve-uniform-bernoulli-measure`
  already passed in Section 20 of `gk-verify-pos-permanence-chain-2026-09-12.md`. I
  re-derived it independently:
  * for a local permutation `pi` on a finite `F`, `rho = sigma pi tau` changes only
    the coordinates in `F M_sigma^-1`;
  * for each boundary condition, `rho` permutes `A^(F M_sigma^-1)`, so it preserves
    `mu_A`;
  * then `pi_* tau_* mu_A = tau_* rho_* mu_A = tau_* mu_A`, and invariance under all
    local permutations characterizes `mu_A`.
* **`universal-bernoulli-preservation-covers-leavitt-units`.** Valid, by
  specialization.
* **Not premature.** The goal cycle is intended and cannot fire: its open prerequisite
  is equivalent to the goal.

### 1.4 `injective-cas-over-leavitt-units-preserve-uniform-bernoulli` (open). Verdict: statement and Attempts correct; wiring incomplete, repaired.

The claim is equivalent to `leavitt-unit-group-surjunctive`, not merely sufficient for
it. The converse holds: if `U` is surjunctive, every injective automaton over `U` is
bijective and so preserves `mu_A` (1.3). The graph recorded only the forward direction
(`leavitt-units-surjunctive-via-measure-preservation`) and the specialization from
the universal claim. The converse route
`leavitt-bernoulli-preservation-from-surjunctivity` is landed with this artifact, so
the equivalence is explicit and a later lane cannot mistake the measure claim for a
weaker, easier target.

I also checked the coset-shift witness cited in the Attempts
(`compressed-coset-shifts-carry-strict-equivariant-embeddings`).
* `psi(gV_1) = g u^-1 V_1` is well defined because `u V_1 u^-1 <= V_1`.
* It is equivariant and surjective.
* It is non-injective exactly when the inclusion is strict: equal images mean
  `g^-1 g'` lies in `u^-1 V_1 u`, which strictly contains `V_1`.

So `y -> y o psi` is injective and not surjective on `A^(U/V_1)`. It is a calibration
on a non-free coset shift, not an automaton over `U`, which is exactly how the node
uses it.

### 1.5 `finitely-generated-simple-groups-are-surjunctive` and `gottschalk-via-finitely-generated-simple-groups` (gk-other-hosts). Verdict: PASS.

* **Localization.** The rule reads only `gM`, which lies in `gH` for `H = <M>`. So
  `A^G` is the product over left cosets of copies of `A^H`, and `tau` acts factor by
  factor. Injectivity and surjectivity then pass in both directions between `tau` and
  `tau_H`.
* **Embedding.** `countable-group-embeds-in-two-generator-simple-group` (Schupp 1976)
  is a citation node with its own transcription caveat. It is a trust surface, not
  re-read here.
* **Heredity direction.** Surjunctivity passes from the simple overgroup `S` down to
  `H`, which is the direction used.

### 1.6 Direct-attack artifact, Sections 2–3 (gk-other-hosts). Verdict: correct as scoped.

Section 2 is 1.2 plus its converse. Section 3 is explicitly heuristic prose ("do not,
on their own, prove surjunctivity"), and it asserts no theorem that a node consumes.
Nothing in it is premature.

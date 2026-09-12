# Unbalanced designs: memory letters certify strictness, and the screens a biased rule must pass

Lane `w3-bal-design`, 2026-09-12. Handwritten proofs; nothing was run. Supports
`unbalanced-effective-rule-certifies-strictness`, `unbalanced-forward-tables-identify-memory-letters`,
`gottschalk-via-unbalanced-table-memory-collisions` and
`unbalanced-table-memory-collisions-from-gottschalk`.

## 0. Conventions

These are the conventions of `canonical-table-groups-for-automaton-designs-2026-09-12.md`:
- designs `D = (A, S, M, nu, mu)`;
- realizations `rho`, forward tables `E_rho`, the up-set `𝓕_D`;
- table groups `U_E` with the realization `rho_E(a) = x_a`, where `x_(1_S)` and `x_(1_M)` are the empty word;
- the memory convention `tau(x)(g) = mu((x(g rho(m)))_(m in M))`.

- A rule `mu : A^M -> A` is **balanced** if `|mu^-1(a)| = |A|^(|M|-1)` for every `a`.
- The **collision partition** `kappa_rho` of `M` puts `m ~ m'` iff `rho(m) = rho(m')`. Let `q : M -> M/kappa_rho` be the quotient map. The **effective rule** is
  `mu_rho : A^(M/kappa_rho) -> A`, `mu_rho(z) = mu(z o q)`.
  So `tau_rho` is the automaton whose memory is the set `rho(M)`, of `|M/kappa_rho|` distinct
  elements, with rule `mu_rho`.
- For `E` in `𝓕_D`, write `kappa_E` for the collision partition of the letters `x_m` in `U_E`, and `mu_E` for the effective rule over `U_E`.

Let `lambda` be the uniform product measure. Distinct sites carry independent uniform symbols. So
`tau_rho(x)(g)` has law `(mu_rho)_*` of the uniform law on `A^(M/kappa_rho)`, and that law is
uniform iff `mu_rho` is balanced.

## 1. Balance certifies strictness, and only memory letters need checking

**Proposition 1 (balance certificate).** Let `E` be in `𝓕_D` and let `rho` be a realization with
`E_rho >= E`. If `mu_rho` is not balanced, then `tau_rho` is injective and not surjective.

*Proof.* Lemmas 1 and 2 of the canonical-table artifact give `sigma_rho tau_rho = id`, so `tau_rho`
is injective. Suppose `tau_rho` were surjective. Then it is bijective, and by
`bijective-ca-preserve-uniform-bernoulli-measure`, `(tau_rho)_* lambda = lambda`. The one-site
marginal of `(tau_rho)_* lambda` would then be uniform, so by Section 0 `mu_rho` is balanced. QED

**Corollary 2 (hinge-free strictness over the table group).** Let `E` be in `𝓕_D`. If `mu_E` is not
balanced, then `tau` over `U_E` is strict, and `U_E` is not surjunctive. In particular, if `mu` is
not balanced and the elements `1` and `x_m` (`m` in `M'`) are pairwise distinct in `U_E`, then `U_E`
is not surjunctive.

*Proof.* `E_(rho_E) >= E` by Lemma 5 there, and `kappa_(rho_E) = kappa_E`. Apply Proposition 1. QED

Compare Proposition C of the canonical-table artifact. There, strictness needs a surviving hinge
word `x_s'^-1 x_m'^-1 x_m x_s` for every minimal reverse partition. For an unbalanced rule no reverse
product is examined: the words `x_m^-1 x_m'` (with `x_(1_M) = 1`) suffice. In the holonomy normal
form (`table-groups-are-memory-holonomy-groups`) these are the generators of `Hol_M(E)` and their
pairwise quotients.

**Theorem 3 (Gottschalk as a memory-collision statement).** The following are equivalent.
1. Every group is surjunctive over every finite alphabet.
2. For every design `D` whose encoder rule `mu` is not balanced, and every minimal `E` in `𝓕_D`,
   two of the elements `1`, `x_m` (`m` in `M'`) coincide in `U_E`.

Group by group: `G` is surjunctive over every alphabet iff no design with unbalanced `mu` has a
realization in `G` with forward table in `𝓕_D` and `rho` injective on `M`.

*Proof.*
- **(1) implies (2).** If the elements are pairwise distinct in `U_E`, Corollary 2 makes `U_E` non-surjunctive.
- **(2) implies (1).** Let `tau` on `A^G` be injective and not surjective.
  - By `strict-automata-give-injective-ca-with-skewed-site-marginals` there is an injective `kappa`
    on `B^G`, `B = A^(k+1)`, whose one-site law is not uniform.
  - Let `M ⊂ G` be its memory, adjoining `1` as an unread address if needed, and `mu` its rule. `mu`
    is not balanced, because its pushforward of the uniform law is that one-site law, and adjoining
    an unread uniform coordinate does not change the law.
  - By Lemma 4 of the canonical-table artifact `kappa` has a left inverse with a finite memory `S`
    containing `1` and a rule `nu`. Put `D = (B, S, M, nu, mu)` with `rho` the inclusion.
  - Lemma 1 gives `E_rho` in `𝓕_D`. The lattice of marked partitions of `S x M` is finite, so some
    minimal `E` in `𝓕_D` has `E <= E_rho`.
  - Lemma 5 gives `pi : U_E -> G` with `pi(x_m) = m`. The elements of `M` are distinct in `G`, so
    `1` and the `x_m` are pairwise distinct in `U_E`. This contradicts (2).
- **Group by group.** The second argument produces the realization in `G` itself, with `rho`
  injective on `M`. Conversely, such a realization has `mu_rho = mu`, which is unbalanced, so by
  Proposition 1 `tau_rho` is strict. QED

**Remarks.**
- **What Theorem 3 changes.** Corollary B of the canonical-table artifact asks that, for every
  design and minimal `E`, the reverse table of `U_E` be reverse sufficient. Theorem 3 keeps only
  unbalanced rules and asks for one memory collision instead. Reverse products never enter.
- **Known collisions.**
  - **Triangular `E`.** Theorem D there makes every realization bijective, hence balanced, so an
    unbalanced rule over a triangular `E` collides memory letters.
  - **Amenable decoder holonomy `Hol_S(E)`.** The same holds by `amenable-decoder-memory-forces-surjectivity`.
  - **Connected `Gamma_E` with `b_1 <= 1`.** Distinct letters would give a non-sofic one-relator
    group (`unicyclic-strict-designs-present-nonsofic-one-relator-groups`).
- **Sofic quotients.** Let `Q` be a sofic quotient of `U_E`. The images of the letters realize `D`
  with forward table `>= E`, and `Q` is surjunctive, so by Proposition 1 the effective rule over `Q`
  is balanced. Every sofic quotient therefore identifies memory letters, in a pattern that balances
  `mu`. The abelianization is one such quotient, and it can be computed from `E` by linear algebra.
- **Robustly unbalanced rules.** Call `mu` robustly unbalanced if `mu_kappa` is unbalanced for every
  partition `kappa` of `M` with at least two classes. Then every sofic quotient of `U_E` kills every
  memory letter. When `Gamma_E` is connected, `U_E = Hol_M(E)` is generated by those letters
  (Corollary C' of the holonomy artifact), so `U_E` has no nontrivial sofic quotient.
  - **A criterion over `F_2`.** Write `mu = sum_T c_T x^T` in algebraic normal form. The weight of
    `mu_kappa` is odd iff `sum_(T ⊆ M, q(T) = M/kappa) c_T = 1`, since the weight's parity is the
    coefficient of the top monomial. A rule with at least two variables and odd weight is
    unbalanced.
  - **Examples.** Every rule of the form "affine part plus the top monomial `x^M`" is robustly unbalanced.
  - **Where this bites.** The screen is vacuous over groups with only trivial sofic morphisms, such as
    `R^x` (`leavitt-unit-group-has-only-trivial-sofic-morphisms`). Those are exactly the hosts where
    robustly unbalanced designs are not excluded.

## 2. Screens a biased rule must pass over every group

Throughout, `G` is a group and `tau` is an injective automaton on `A^G`. Its memory `M` is a finite set of
distinct elements, and its rule is `mu : A^M -> A`. A **context** at `m` in `M` is an assignment `r` in
`A^(M \ m)`. The rule is **insensitive at `m` in context `r`** if `mu(., r)` is not injective. Over
`A = {0,1}` this means `mu(., r)` is constant. Write `Ins_m` for the set of such contexts, indexed by
the addresses other than `m`, and `pi_(x_k)` for projection to the coordinate at address `k`.

**Lemma 4 (constant backgrounds).** For every `c != d` in `A` some `m` in `M` has
`mu(c at M \ m, d at m) != mu(c at M)`.

*Proof.* Otherwise let `x` be constant `c`, and let `x'` agree with `x` except `x'(1) = d`.
- An output `h` reads site `1` only when `1 = h m`. That `m` is unique because `M` is a set, and all
  other positions of `h` read `c`. So `h` outputs `mu(c at M \ m, d at m) = mu(c at M)` for both.
- The remaining outputs read only `c`.

So `tau(x) = tau(x')`. QED

The case `c = 0` is the norm-rule kill in Section 9 of
`invariant-output-descent-and-sensitivity-2026-09-12.md`.

**Lemma 5 (monotone binary rules are copies).** Let `A = {0 < 1}` and let `mu` be nondecreasing in
every coordinate. Then `mu = x_t` for one `t`. For nonincreasing rules, `mu = 1 - x_t`. Either way `mu`
is balanced.

*Proof.*
- **Background `0`.** Lemma 4 gives `t` with `mu(e_t) != mu(0)`. Monotonicity forces `mu(0) = 0` and
  `mu(e_t) = 1`, so `mu >= x_t`.
- **Background `1`.** Lemma 4 gives `t'` with `mu(1 - e_t') != mu(1)`. Monotonicity forces
  `mu(1 - e_t') = 0` and `mu(1) = 1`, so `mu <= x_t'`.
- **Conclusion.** Evaluate `x_t <= x_t'` at `e_t` to get `t' = t`, so `mu = x_t`.
- **Nonincreasing rules.** The same steps give `1 - x_t' <= mu <= 1 - x_t`. QED

So thresholds, biased majorities and negation-free AND/OR circuits are injective over no group,
unless they are copies.

**Lemma 6 (unbalanced binary rules need a rectangle relation).** Let `A = {0,1}` and let `mu` be unbalanced.
Then every `Ins_m` is nonempty, and some `m_1 != m_2`, `m_1' != m_1`, `m_2' != m_2` satisfy
`m_1^-1 m_1' = m_2^-1 m_2'` in `G`.

*Proof.*
- **Every `Ins_m` is nonempty.** If every context at `m` were sensitive, each would contribute exactly
  one preimage of `1`, and `mu` would have weight `2^(|M|-1)`.
- **The flip.** Choose `r_m` in `Ins_m`. Suppose the sets `D_m = {m^-1 m' : m' != m}` are pairwise
  disjoint. No `D_m` contains `1`, and each `D_m` has distinct elements.
  - Put `x(m^-1 m') = r_m(m')`, `x(1) = 0`, anything elsewhere, and let `x'` be `x` with site `1`
    flipped.
  - The outputs reading site `1` are `h = m^-1`. At each, the flipped position is `m` and the
    context is `r_m`.
  - So `tau(x) = tau(x')`. QED

In general, the flip at `1` is invisible iff a constraint problem is satisfiable:
- **Variables:** the distinct elements `m^-1 m'`.
- **Constraints:** `(w(m^-1 m'))_(m' != m)` lies in `Ins_m` for every `m`.

**Corollary 7 (three addresses).** Let `A = {0,1}`, `M = {1, a, b}`, `mu` unbalanced and `tau` injective.
Then exactly one of `a^2 = 1`, `b^2 = 1`, `(a^-1 b)^2 = 1` holds, and at the site it glues the
insensitive contexts project to complementary symbols:

| relation | glued site | the two projections that must be disjoint |
|---|---|---|
| `a^2 = 1` | `a` (blocks `1`, `a^-1`) | `pi_(x_a)(Ins_1)` and `pi_(x_1)(Ins_a)` |
| `b^2 = 1` | `b` (blocks `1`, `b^-1`) | `pi_(x_b)(Ins_1)` and `pi_(x_1)(Ins_b)` |
| `(a^-1 b)^2 = 1` | `a^-1 b` (blocks `a^-1`, `b^-1`) | `pi_(x_b)(Ins_a)` and `pi_(x_a)(Ins_b)` |

*Proof.*
- **The possible coincidences.** `D_1 = {a, b}`, `D_a = {a^-1, a^-1 b}`, `D_b = {b^-1, b^-1 a}`. A
  coincidence between different `D_m` is one of `a^2 = 1`, `b^2 = 1`, `(a^-1 b)^2 = 1`, `ab = 1`,
  `b = a^2` or `a = b^2`.
- **At most one of them.** The last three make `H = <a, b>` cyclic, and two of the first three make it a
  quotient of the infinite dihedral group. In both cases `H` is amenable. `tau` acts on each coset of
  `H` as one automaton over `H`. That automaton is injective, hence surjective because amenable groups
  are surjunctive. So `tau` is bijective and `mu` is balanced, a contradiction.
- **At least one.** This is Lemma 6.
- **The projections.** With `a^2 = 1`, the only variable shared by two constraints is the site `a`. The
  block `b^-1` has private variables. So the problem is satisfiable iff the two projections meet. The
  other rows are the same computation. QED

**Theorem 8 (three binary addresses force balance).** Let `A = {0,1}` and let `tau` be injective with
memory of at most three elements. Then `mu` is balanced.

*Proof.*
- **Small or amenable memory.** If `|M| <= 2`, or `<M>` is amenable, argue on cosets as in Corollary 7.
- **Normalization.** Let `|M| = 3`.
  - Replacing `tau` by `x -> tau(x)(. m_0^-1)` moves the memory to `m_0^-1 M` without changing the
    rule or injectivity. So `M = {1, a, b}`.
  - Re-rooting at `a` turns the third row of Corollary 7 into the second, and swapping names turns
    the second into the first. So assume `a^2 = 1` and no other relation of that list.
  - Replacing `tau` by `x -> tau(1 - x)` complements every `Ins_m`, so assume
    `Ins_1 ⊆ {x_a = 1}` and `Ins_a ⊆ {x_1 = 0}`.
- **Normal form.** Every context with `x_a = 0` is sensitive at `1`, so
  `mu(x_1, 0, x_b) = x_1 + f(x_b)`. Every context with `x_1 = 1` is sensitive at `a`, so
  `mu(1, 1, x_b) = 1 + mu(1, 0, x_b) = f(x_b) = mu(0, 0, x_b)`.
- **The eight sites.** Consider `1, a, b, ab, b^-1, b^-1 a, a b^-1, a b^-1 a`. Checking all 28 pairs
  with `a = a^-1`, each coincidence among them gives one of:
  - `a = 1`, `b = 1` or `a = b`;
  - a cyclic relation (`a = b^2` or `a = b^-2`);
  - `b^2 = 1` or `(ba)^2 = 1`;
  - `ab = ba`.

  Each makes `<a, b>` amenable. So the eight sites are distinct.
- **An invisible double flip.**
  - Let `x(1) = x(a) = 0`, let `x'(1) = x'(a) = 1`, and let them agree elsewhere.
  - The outputs reading `1` or `a` are `h = 1, a, b^-1, a b^-1`.
    - Block `1` reads `(x(1), x(a), x(b))` and outputs `f(x(b))` in both cases.
    - Block `a` reads `(x(a), x(1), x(ab))` and outputs `f(x(ab))` in both cases.
    - Blocks `b^-1` and `a b^-1` read a flipped site only at address `b`, with contexts at the
      private sites `b^-1, b^-1 a` and `a b^-1, a b^-1 a`. Choose both contexts in `Ins_b`.
  - Then `tau(x) = tau(x')`, contradicting injectivity. QED

**Example.** `mu = x_1 + x_1 x_a x_b` has weight `3` and is robustly unbalanced in the sense of
Section 1. It already fails Corollary 7: `pi_(x_a)(Ins_1) = {1}`, while every projection of `Ins_a`
and `Ins_b` is `{0,1}`.

**Consequence for designs.** Over `F_2`, a design refuting `unbalanced-forward-tables-identify-memory-letters`
needs an effective memory of at least four elements and a rule that is not monotone. Every screen
here is local: it reads only `mu` and the coincidences among `M^-1 M` and `M^-1 M M^-1 M`.

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

## 3. Where local screens stop, and a ternary architecture

Every screen of Section 2 compares two configurations that differ on a finite set. This section records
one more screen of that kind, and then shows that over larger alphabets such screens can be silent
on small unbalanced rules.

**Proposition 9 (finite subgroups inside a biased binary memory).** Let `A = {0,1}`, `mu`
unbalanced, and `tau` injective. Let `K ⊆ M` be a finite subgroup with `|K| >= 2`. Then one of the
following holds.
- **(G1) fails.** Two distinct elements of `M \ K` lie in a common left coset `mK` or a common right
  coset `Km`.
- **(G2) fails.** Consider the blocks `h` outside `K` that read `K`. Their context sites meet each
  other, or meet the context sites `K(M \ K)` of the blocks in `K`.

*Proof.* Suppose (G1) and (G2) hold.
- **Blocks in `K`.** A block `h` in `K` reads all of `K`, at the addresses `k` with `hk` in `K`. Its
  context sites are `h(M \ K)`. If `hm = h'm'` with `m, m'` in `M \ K`, then `m'` lies in `Km`, so
  `m = m'` and `h = h'` by (G1). So these context sites are pairwise distinct.
- **Blocks outside `K`.** Let `h` be outside `K` with `hm` in `K`. Then `m` is not in `K`, and
  `h = k m^-1`. If also `hm'` is in `K`, then `m^-1 m'` is in `K`, so `m' = m` by (G1). So each
  such block reads `K` at exactly one address.
- **Perturb on `K`.** Change `x` on `K` from `u` to `u' != u`.
  - Give every outside block a context in `Ins_m`. Its sites are private by (G2), and `Ins_m` is
    nonempty by Lemma 6. Then its output does not change.
  - The blocks in `K` output `Phi_r(u) = (mu((u(hk))_(k in K), r_h))_(h in K)`, with independent
    contexts `r_h`. So injectivity makes every `Phi_r` an injective map of `{0,1}^K`, hence a
    bijection.
- **Conclusion.** A bijection pushes the uniform law forward to the uniform law, so the coordinate
  `h = 1` shows `mu(., r_1)` is balanced on the `K`-coordinates for every `r_1`. Then `mu` is
  balanced, a contradiction. QED

Theorem 8 is the case `K = {1, a}`, `M \ K = {b}`. There (G1) is automatic, and (G2) is the check on
the eight sites. So designs over hosts full of finite subgroups, such as `R^x` and `V`, cannot put a
finite subgroup into a biased binary memory generically. The coincidences have to break (G1) or (G2).

**Proposition 10 (pair-distinct ternary rules are pre-injective on free memory).** Let `A = Z/3` and
`M = {1, a, b}`, with `a, b` free generators of `F(a, b)`. Suppose that at each address `m` every
insensitive context identifies exactly one fixed pair `P_m` and is injective otherwise, and that
`P_1`, `P_a`, `P_b` are distinct. Then `tau` over `F(a, b)` is pre-injective.

*Proof.*
- **Setup.** Let `x`, `x'` differ exactly on a finite nonempty set `F`, with `tau(x) = tau(x')`.
  Write `C_g = {x(g), x'(g)}`.
- **Blocks reading one changed site.** Suppose a block reads exactly one changed site `g`, at address
  `m`. Its output is unchanged only if the context is insensitive and `C_g = P_m`. The pairs are
  distinct, so this happens at no more than one of the three blocks `g`, `g a^-1`, `g b^-1` reading
  `g`. Hence each `g` in `F` lies in at least two triangles `hM = {h, ha, hb}` that contain another
  point of `F`.
- **The incidence graph is a forest.** In the Cayley tree of `F(a, b)`, the edges `h — ha` and
  `h — hb` form a claw `C_h`. Claws are edge-disjoint and cover the tree. Suppose the incidence graph
  between elements and triangles had a cycle `g_0, C_0, g_1, ..., C_(k-1), g_0`. Joining geodesics
  inside consecutive claws would give a closed walk in the tree. It has no backtracking inside a claw,
  and none at a junction because claws share no edge. So no such cycle exists.
- **Counting.** Let `T_F` be the set of triangles with at least two points of `F`. The incidence
  forest on `F ⊔ T_F` has at most `|F| + |T_F| - 1` edges. It also has at least `2|F|` and at least
  `2|T_F|` edges, so at least `|F| + |T_F|`. Contradiction. QED

**Example (affine plus one defect).** Put

```text
mu(x_1, x_a, x_b) = x_1 + x_a + x_b + [ (x_1, x_a, x_b) = (0, 1, 2) ]      over Z/3.
```

- **Values.** Moving one table entry from `0` to `1` gives value counts `(8, 10, 9)`, so the rule is
  unbalanced.
- **Insensitive contexts.** Each address has exactly one: `(x_a, x_b) = (1, 2)` at address `1`, with
  pair `{0, 1}`; `(x_1, x_b) = (0, 2)` at `a`, with pair `{1, 2}`; `(x_1, x_a) = (0, 1)` at `b`, with
  pair `{0, 2}`.
- **Consequence.** Proposition 10 applies. So Lemmas 4 and 6, Corollary 7, Theorem 8 and
  Proposition 9, and more generally every screen that compares finitely different configurations,
  say nothing about this rule at three addresses.
- **Over the free group.** The rule is not injective there, since `F(a, b)` is sofic and injectivity
  would force balance. So its failure is global: two configurations differing on an infinite set.

**Architecture (open).** An affine-plus-defect rule has the form
`mu(x) = sum_m c_m x_m + c + t [x|_M = p]`, with `c_m != 0` and `t != 0`.
- **Minimality.** These are the minimal unbalanced deformations of bijective linear rules. Each
  address has exactly one insensitive context, and it identifies the pair `{p_m, p_m + t c_m^-1}`.
- **Over `F_2`.** All these pairs are `{0,1}`, so Lemma 6 applies.
- **Over `F_q` with `q >= 3`.** The pairs can be chosen distinct, and then local screens can be
  silent.
- **What injectivity needs.** A group on which such a rule is injective is not surjunctive, by
  Proposition 1 applied to the group itself. Write `L` for the linear part and `D` for the defect field.
  If `x` has a single defect and `x + L^-1(t delta)` has none, the two share an image. When `L` is
  invertible, injectivity therefore needs every such correction to create a defect somewhere, and the
  same must hold for every infinite cascade of corrections.
- **The decoder.** On hosts whose prime-field matrix algebras are stably finite, the decoder must use
  `x^q = x` (`formal-polynomial-strict-pairs-need-unstable-linearization`).

Recorded as the open construction target `affine-plus-defect-rule-is-injective-on-some-group`.

**Cross-references (w4-bal-census, landed 16:10–16:17 after Section 2).**
- Independent re-derivation of Theorem 8: `binary-three-address-injective-automata-have-balanced-rules`, in
  `small-memory-balance-census-2026-09-12.md`.
- The single-flip part of Lemma 6 as its own node: `binary-unbalanced-rules-on-sidon-memory-are-not-pre-injective`.
- `avoidable-patches-of-affine-rules-inherit-linear-injectivity`. For `q >= 3`, a single-defect affine rule is an
  avoidable patch, so injectivity forces the linear part to be injective. The architecture above therefore needs
  `sum_m c_m m` to be a unit of `F_q[G]`, unless `G` already carries a linear strict automaton. In the ternary example
  that unit is `1 + a + b`.
- Proposition 10 bears on the open census case `ternary-three-address-injective-automata-have-balanced-rules`. Over free
  memory, rigid ternary rules with distinct blind pairs have no finite invisible perturbation. A proof of balance there
  must therefore be global.

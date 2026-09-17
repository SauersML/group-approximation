# Folding act certificates for strict automaton designs (a-gs-pull-2, 2026-09-17)

Lane: transplanter, stability-approximation. Question: Gromov--Weiss counting runs on
permutation models. Does it survive when the letters are arbitrary self-maps of finite
sets, not permutations ("folding" models, allowed to be non-injective, with views allowed
to merge points)? If yes, how much do the extra models buy?

Answers proved here:

1. **Yes, the count survives** (Theorem A). Two-layer finite acts with non-injective
   letters and coarsened views certify non-strictness.
2. **Folding buys nothing on the bijective core** (Theorem B). A syntactic closure of the
   forward table, the *bijective core* `C(D,E)`, is forced to consist of
   near-permutations in every certificate. So every certificate restricts to an
   almost-multiplicative permutation model of the core table group `B(D,E)`. Every
   distinguished window pair expressible through core letters must be moved at density at
   least the window density. A core-expressible pair whose core word is invisible to
   permutation models of `B(D,E)` defeats every exact folding certificate and every
   density family of folding certificates (Corollary B1). The residual sparse-slack regime
   is stated precisely there.
3. **Folding does buy an exact finite filter** (Proposition C). One explicit folded act, the
   total fold, gives a rule-level necessary condition for strictness. It uses no group
   structure and is strictly finer than quotients killing the decoder memory.
4. **Open step** (Section 5). Extend core permutation models to folding acts on the
   non-core letters. It can fail on its own, and if it holds it sharpens the sofic-radical
   localization from the memory group to the core group.

Conventions follow `strict-automata-live-on-canonical-table-groups`.

## 0. Setting

A **design** `D = (A, S, M, nu, mu)`: a finite alphabet `A` with `|A| >= 2`, finite address
sets `S` (decoder) and `M` (encoder) each containing an identity address `1`, and rules
`nu : A^S -> A`, `mu : A^M -> A`.

- **Marked partitions.** A marked partition `E` of `S x M` has one marked class containing
  `(1,1)`.
- **Forward sufficiency.** `E` is **forward sufficient**, written `E in F_D`, if for every
  `z : S x M -> A` constant on `E`-classes,

      nu( ( mu( z(s, .) ) )_(s in S) ) = z(marked class).

- **Window datum.** A window datum is `W = (Omega, Pi, p)`: a finite set `Omega`, an
  equivalence `Pi` on `Omega x M`, and `p in A^Omega`. It is a **Garden-of-Eden datum** for
  `mu` if for every `z : Omega x M -> A` constant on `Pi`-classes,

      ( mu( z(w, .) ) )_(w in Omega) != p.                                  (GoE)

- **A strict pair gives both.** Let `G` carry a strict pair `(tau, sigma)` with rules `mu`,
  `nu`, memories `M`, `S` realized in `G`, and `sigma tau = id`. Write
  `tau(x)(g) = mu((x(gm))_m)` and `sigma(y)(g) = nu((y(gs))_s)`, and let `p` be a
  Garden-of-Eden pattern on `Omega ⊂ G`.
  - The `G`-table `E_G` ( `(s,m) ~ (s',m')` iff `sm = s'm'`, marked iff `sm = 1`) lies in `F_D`.
  - Put `Pi_G` ( `(w,m) ~ (w',m')` iff `wm = w'm'` ). Then `(Omega, Pi_G, p)` is a
    Garden-of-Eden datum: a `z` constant on `Pi_G`-classes is a pattern on `Omega M`, it
    extends to some `x in A^G`, and `tau(x)|_Omega` is not `p`.
  - Coarsening `Pi_G` keeps (GoE), since fewer `z` qualify.

Call `(D, E, W)` **certified** if some finite act model (below) violates the inequality of
Theorem A. Theorem A shows a certified triple has no strict realization.

## 1. Act models and Theorem A

An **act model** `𝔐 = (V, U, b, a, g)` consists of finite sets `V` (sites) and `U` (outputs)
and arbitrary maps

    b_s : V -> U  (s in S),     a_m : U -> V  (m in M),     g_w : U -> U  (w in Omega).

No map needs to be injective or surjective.

- **Good sites.** `V_0` is the set of `v in V` such that
  `a_m b_s v = a_m' b_s' v` whenever `(s,m) ~_E (s',m')`, and `a_m b_s v = v` for `(s,m)`
  marked. Only equalities are demanded. Views may merge more points than `E` does.
- **Window-good outputs.** `u in U` is window-good if
  - `a_m g_w u = a_m' g_w' u` whenever `(w,m) ~_Pi (w',m')`, and
  - `g_w u != g_w' u` whenever `p(w) != p(w')`.

  Put `W_u = { g_w u : w in Omega }`, and let `U_1` be any family of window-good outputs with
  pairwise disjoint `W_u`.
- **Model automata.** Define

      tau_𝔐 : A^V -> A^U,   tau_𝔐(x)(u) = mu( (x(a_m u))_m ),
      sigma_𝔐 : A^U -> A^V, sigma_𝔐(y)(v) = nu( (y(b_s v))_s ).

**Lemma 1 (decoding at good sites).** If `E in F_D` and `v in V_0`, then
`sigma_𝔐 tau_𝔐 (x)(v) = x(v)` for every `x in A^V`.

*Proof.* Put `z(s,m) = x(a_m b_s v)`. By the definition of `V_0`, `z` is constant on
`E`-classes and takes the value `x(v)` on the marked class. The left side is
`nu((mu(z(s,.)))_s)`, which equals `x(v)` by forward sufficiency. ∎

**Lemma 2 (avoidance at window-good outputs).** If `W` satisfies (GoE) and `u` is window-good,
then `( tau_𝔐(x)(g_w u) )_(w in Omega) != p` for every `x`.

*Proof.* Put `z(w,m) = x(a_m g_w u)`. It is constant on `Pi`-classes, and
`tau_𝔐(x)(g_w u) = mu(z(w,.))`. Apply (GoE). ∎

**Theorem A.** Let `E in F_D` and let `W` be a Garden-of-Eden datum. Every act model satisfies

    |V_0|  <=  |U| - kappa |U_1|,     kappa = -log_|A| (1 - |A|^(-|Omega|)) > 0.

*Proof.*
- **Lower bound.** Let `Y = tau_𝔐(A^V)`. By Lemma 1, `x|_(V_0)` is a function of
  `tau_𝔐(x)`, so `|A|^|V_0| <= |Y|`.
- **Upper bound.** Fix `u in U_1`. Restriction `q ↦ (q(g_w u))_w` maps `A^(W_u)` injectively
  into `A^Omega`. The pattern `p` lies in its image, because `g_w u = g_w' u` forces
  `p(w) = p(w')`. So exactly one `q_u in A^(W_u)` restricts to `p`, and by Lemma 2 no `y in Y`
  has `y|_(W_u) = q_u`.
- **Count.** The `W_u` are disjoint and `|W_u| <= |Omega|`, so

      |Y| <= |A|^(|U| - sum |W_u|) * prod_u (|A|^|W_u| - 1) <= |A|^|U| (1 - |A|^(-|Omega|))^|U_1|.

  Take `log_|A|`. ∎

**Corollary A1 (filter).** Suppose `G` carries a strict pair with design `D` and window
`(Omega, Pi_G, p)`. Then for every `E in F_D`, every `Pi ⊇ Pi_G` and every act model for
`(D, E, (Omega, Pi, p))`,

    |U| - |V_0| >= kappa |U_1|.

In particular:
- no finite act has `U = V = V_0` and a window-good output;
- no sequence of act models has `(|U| - |V_0|)/|V| -> 0` with `|U_1|/|V|` bounded below.

`E` is arbitrary in `F_D`, so one may take `E` minimal and impose the fewest equalities.

*Scope check.*
- **Sofic case.** For a sofic group, a sofic approximation `V = U`, `b_s = sigma(s)`,
  `a_m = sigma(m)`, `g_w = sigma(w)` has `|V_0|, |U_1| |Omega|^2 ≳ |V|`. This recovers
  Gromov--Weiss, as in `sofic-radical-localizes-garden-of-eden-windows`.
- **Finite quotients.** A finite quotient `G -> Q` injective on the distinguished cells gives
  `V = U = Q`, `V_0 = V` and one window-good output. This is Lawton's periodic-point argument.
- **What is new** is that the letters may be arbitrary maps.

## 2. Theorem B: the bijective core

**Definition.** The **bijective core** `C = C(D,E) ⊆ S ⊔ M` is the smallest set of letters
such that:

- (C0) `1_S` and `1_M` are in `C`;
- (C1) if `(s,m)` is marked, then `s` and `m` are in `C`;
- (C2) if `(s,m) ~_E (s',m')` with `s'` and `m'` in `C`, then `s` and `m` are in `C`.

It is computed from `E` alone. The **core table group** is

    B(D,E) = < x_c (c in C non-identity) |
               x_s x_m = x_s' x_m' for (s,m) ~_E (s',m') with all four in C,
               x_s x_m = 1 for marked (s,m) >.

A distinguished pair `w, w' in Omega` (`p(w) != p(w')`) is **core-expressible** if there is a
chain `w = w_0, w_1, ..., w_r = w'` and letters `m_i, m_i' in C ∩ M` with
`(w_(i-1), m_i) ~_Pi (w_i, m_i')`. Its **core word** is

    h = x_(m_r')^-1 x_(m_r) ... x_(m_1')^-1 x_(m_1)   in B(D,E).

Note that `C` is typically not the 2-core of `forward-relations-of-a-counterexample-have-a-nonsofic-core`.
- (C2) can pull a private generator into `C`.
- A letter of the 2-core whose relators all have a non-core letter on each side stays outside `C`.

**θ-bijectivity.** Fix a model and write `n = |V|`. A map `f : X -> Y` between sets of size at
most `2n` is **θ-bijective** if some `X' ⊆ X` has `|X \ X'| <= θn`, `f|_X'` is injective, and
`|Y \ f(X')| <= θn`.

**Lemma 3.** Suppose `|U| <= (1+eta) n` and `|V \ V_0| <= eps n`, and put `λ = eps + eta`.
Then `| |U| - n | <= λ n`, and:

- (a) if `f` is `θ1`-bijective and `f'` is `θ2`-bijective and they compose, then `f' f` is
  `(θ1+θ2)`-bijective;
- (b) if `f : V -> U` and `f' : U -> V` satisfy `f' f = h` on `V_0`, and `h` is `θ`-bijective,
  then `f` and `f'` are both `(θ + 2λ)`-bijective.

*Proof.*
- **Sizes.** `a_1 b_1 = id` on `V_0`, since `(1,1)` is marked. So `b_1` is injective on
  `V_0`, which gives `|U| >= (1-eps) n`.
- **(a).** `f'` is injective on `X'' ⊆ Y` with `|Y \ X''| <= θ2 n`. Then `f' f` is injective
  on `X' ∩ f^-1(X'')`. That set misses at most `(θ1 + θ2) n` points, because `f|_X'` is
  injective and at most `θ2 n` points of `f(X')` lie outside `X''`. Its image
  `f'(f(X') ∩ X'')` misses at most `(θ1 + θ2) n` points of the target.
- **(b).** Let `X'` witness `h` and put `X''' = X' ∩ V_0`, which misses at most `(θ + eps) n`
  points.
  - `f` is injective on `X'''`, since `h` is. Then
    `|U \ f(X''')| <= |U| - n + (θ+eps) n <= (θ + 2λ) n`.
  - `f'` is injective on `f(X''')`, since `f' f = h` is injective on `X'''`. Its image
    `h(X''')` misses at most `(θ + eps) n` points of `V`. ∎

**Theorem B.** Suppose `E in F_D`, `|U| <= (1+eta)|V|`, `|V \ V_0| <= eps |V|`, and
`λ = eps + eta`. Then:

1. **Core letters are near-permutations.** Every core letter `c` is `θ_c`-bijective with
   `θ_c <= 3^d · 2λ`, where `d <= |S| + |M|` is the derivation depth of `c` in (C0)--(C2).
2. **Permutation model of the core.** Pad the smaller of `U`, `V` with at most `λ|V|` dummy
   points and fix a bijection `ι : U -> V` extending `(b_1|_(V_0'))^-1` on a large injective
   domain `V_0'`. There are permutations `π_c in Sym(V)`, `c in C`, such that:
   - `π_c` agrees with `b_c` (after `ι`) or with `a_c` (after `ι^-1`) outside `O(θ_c) |V|`
     points;
   - `π_1 = id`;
   - `d_H(π_m π_s, π_m' π_s') = O(λ 3^(|S|+|M|))` for every core relator;
   - `d_H(π_m π_s, id) = O(λ 3^(|S|+|M|))` for marked `(s,m)`.

   So `x_c ↦ π_c` is an almost-multiplicative permutation model of the finite presentation
   `B(D,E)`. No freeness is claimed.
3. **Separation.** For every core-expressible distinguished pair with core word `h` of chain
   length `r`, the permutation `h(π)` moves at least `|U_1| - O(r θ_max) |V|` points.

*Proof.*
- **(1).** Induct along (C0)--(C2).
  - (C0): `a_1 b_1 = id` on `V_0`, so Lemma 3(b) with `h = id` (0-bijective) makes `b_1` and
    `a_1` `2λ`-bijective.
  - (C1): `a_m b_s = id` on `V_0`; the same argument applies.
  - (C2): `a_m b_s = a_m' b_s'` on `V_0`. The right side is `(θ_s' + θ_m')`-bijective by
    Lemma 3(a), so Lemma 3(b) applies.

  Each step at most triples the constant.
- **(2).**
  - **Permutations.** A `θ`-bijective map between sets of equal size agrees with a bijection
    off at most `θ n` points: extend `f|_X'` by any bijection of the complements. Composition
    with `ι` adds `O(λ) n` exceptions.
  - **Relators.** They hold on `V_0` for the letters. Replacing four letters by their
    permutations changes each side on at most `O(θ_max) n` points.
- **(3).** Fix `u in U_1` and a chain. Window-goodness gives
  `a_(m_i) g_(w_(i-1)) u = a_(m_i') g_(w_i) u` for each `i`.
  - Suppose none of the `2r` points involved is an exception for `π_(m_i)` or `π_(m_i')`.
    Then `g_w' u = h(π) g_w u`, and `g_w u != g_w' u` because `p(w) != p(w')`. So `h(π)`
    moves `g_w u`.
  - The `W_u` are disjoint, so a single exception point spoils at most one `u`. The spoiled
    `u` number at most `O(r θ_max) n`. ∎

**Lemma 0 (collapsing bad sites).** Every act model can be replaced by one with the same `U`,
the same `g`, the same `V_0`, the same window-good outputs, and `|V \ V_0| <= 1`.

*Proof.* Collapse `V \ V_0` to one point `*`. Put `a'_m = c ∘ a_m`, where `c` is the collapse
map, `b'_s = b_s` on `V_0`, and `b'_s(*)` arbitrary.
- A site `v in V_0` stays good: an equality `a_m b_s v = a_m' b_s' v` survives `c`, and a
  marked view `a_m b_s v = v` lies in `V_0`, so `c` fixes it.
- Window-goodness survives: the `Pi`-equalities are pushed through `c`, and the
  distinctness conditions live in `U`, which is unchanged. ∎

This step uses the folding freedom (a non-injective view), and it leaves the certificate
inequality of Theorem A unchanged. So write `D_𝔐 = |U| - |V_0|` for the **slack**. After
Lemma 0 and padding with at most `D_𝔐` dummy points, `λ |V| <= D_𝔐 + 1`, and every exception
count in Theorem B is at most `K (D_𝔐 + 1)` points, with `K = O(r 3^(|S|+|M|))` depending
only on `(D, E, W)`. A certificate is exactly a model with `D_𝔐 < kappa |U_1|`.

**Corollary B1 (where folding dies).** Let `(D, E, W)` have a core-expressible distinguished
pair whose core word `h` is **invisible** in `B(D,E)`: for every `ε > 0` there is `δ > 0` such
that every `δ`-almost-multiplicative permutation model moves `h` on at most `ε |V|` points.
This is the sofic radical of `sofic-radical-localizes-garden-of-eden-windows`, applied to the
finitely presented `B(D,E)`. Then:

- **(i) Density families die.** No sequence of act models has `D_𝔐/|V| -> 0` and
  `|U_1|/|V| >= δ_0 > 0`. By Theorem B(3), `h(π)` moves at least `|U_1| - K(D_𝔐+1)` points
  while every relator fails on at most `K(D_𝔐+1)` points. Normalized by `|V|`, the defect
  tends to 0 and the moved fraction stays above `δ_0/2`, which contradicts invisibility.
- **(ii) Exact certificates die.** No model with `D_𝔐 = 0` has a window-good output. Take `N`
  disjoint copies and apply Lemma 0 once. The slack stays 0, exceptions stay at most `K`
  points, and `|U_1|/|V|` is unchanged, so (i) applies as `N -> ∞`.
- **(iii) Residual.** Certificates with `0 < D_𝔐 < kappa |U_1|` and `|U_1| = o(|V|)` are not
  excluded, and neither are those whose slack is a fixed positive fraction of `|V|`.
  Qualitative invisibility compares moved points with `|V|`, not with the defect. Killing them
  needs a **linear modulus**: `h(π)` moves at most `L_h` times the relator defect. That kills
  every certificate once `K (1 + L_h) kappa < 1`, since `|U_1| - K(D+1) <= L_h K (D+1)` and
  `D < kappa |U_1|` contradict each other for large `|U_1|`. This regime is recorded, not
  settled.

Hence, on core letters, non-injective folding is exactly permutation modelling:
- **Invariant:** the sofic radical of the core table group `B(D,E)`, evaluated on core words of
  distinguished window pairs.
- **Step where every folding certificate dies:** the window-good density `|U_1|/|V|` in
  Theorem A, forced to zero by Theorem B(3).

The extra freedom of maps lives only on letters outside `C(D,E)`. There a relation
`a_m ∘ π = a_m`, with `π` a core word, can be absorbed by making `a_m` constant on
`π`-orbits, which a permutation cannot do unless `π ≈ id`.

## 3. Proposition C: the total fold (an exact finite filter)

For the given `E`, let `≈` be the equivalence on `M` generated by:
- `m ≈ m'` whenever `(s,m) ~_E (s',m')` for some `s`, `s'`;
- `m ≈ 1` whenever `(s,m)` is marked.

Let `~` be the smallest equivalence on `Omega x M` such that:
- (i) `~` contains `Pi`;
- (ii) `(w,m) ~ (w,m')` whenever `m ≈ m'`;
- (iii) `(w,1) ~ (w',1)` implies `(w,m) ~ (w',m)` for all `m`.

**Proposition C.** Suppose `E in F_D`, `W` is a Garden-of-Eden datum, and `(w,1) ≁ (w',1)` for
every distinguished pair (`p(w) != p(w')`). Then there is a finite act with `U = V = V_0` and
one window-good output. So `(D, E, W)` has no strict realization.

*Proof.*
- **The act.** Let `V = U = (Omega x M)/~`, write `[w,m]` for a class, and put `o_w = [w,1]`.
  - `b_s = id` for all `s`.
  - `a_m(o_w) = [w,m]`. This is well defined by (iii) when `o_w = o_w'`.
  - `a_m(v) = v` at every other point.
  - `g_w(u_0) = o_w` for one fixed `u_0`, and arbitrary elsewhere.
- **All sites are good.**
  - At `v = o_w`: `a_m b_s v = [w,m]`. If `(s,m) ~_E (s',m')` then `m ≈ m'`, so
    `[w,m] = [w,m']` by (ii). If `(s,m)` is marked then `m ≈ 1`, so `[w,m] = o_w`.
  - At any other point every view is `v` itself.
  - So `V_0 = V`.
- **`u_0` is window-good.** `a_m g_w u_0 = [w,m]` respects `Pi` by (i), and distinguished
  outputs `o_w`, `o_w'` differ by hypothesis.
- **Contradiction.** Theorem A gives `|V| <= |V| - kappa`. ∎

**Remarks.**
- **Why C beats group quotients.** A group quotient with `x_s ↦ 1` gives `x_m = x_m'` for
  `m ≈ m'`, but group cancellation propagates identifications across all letters
  (`wm = w'm'` forces `w m'' = w' m' m^-1 m''`). The act closure (iii) propagates only
  through the identity letter. Each of (i)--(iii) holds for equality in any group quotient
  killing `S`, so `~` is contained in that equality. Separation in such a quotient therefore
  implies the hypothesis of C. C needs no finite or sofic quotient to exist, and it is a
  decidable test on `(E, W)`. Strictness of the inclusion is not claimed.
- **What C forces.** A strict design must identify some distinguished pair through (i)--(iii).
  When `M` is `≈`-connected to `1`, (ii) collapses each row `{w} x M` and (i) links rows
  whenever window translates overlap. So strictness forces overlapping windows, as expected.
- **Other folds.** Folding a subset of sites (setting all `b_s v = b_1 v` at `v`) gives
  further exact acts, each a necessary condition. Theorem B shows that no fold helps on core
  letters.

## 4. Consequence for the Bernoulli Rokhlin lane (target node)

The target `bernoulli-rokhlin-maximal-on-fg-simple-kazhdan-groups` needs lower bounds on
`Phi(k,E,F,psi)` of `bernoulli-rokhlin-deficit-has-a-finitary-witness`. The finite-model proof
of `Phi >= k log q` is the entropy count

    k|V| log q = H(x_V) <= sum_u H(psi(x ∘ e(u))) + sum_v H( x(v) | (psi-codes at f(v))_(f in F) ).

- **The transplant.** The two-layer form (codes on `U`, sites on `V`, `f : V -> U`,
  `e : U -> V` arbitrary maps) survives exactly as in Theorem A, with slack
  `(|U| - |V_0|) · H(psi)` against a fixed deficit.
- **Where it breaks: views must be injective.** Unlike the Garden-of-Eden count, coarsened
  views are not allowed. Merging coordinates can raise `H(psi)`: for `q = 2`,
  `psi(a,b) = 1[a=b=1]` has entropy `h(1/4)` on independent inputs and `1` on merged inputs.
  Merging can also raise the conditional term. So a Phi-certificate needs views injective on
  `E` and on `FE ∪ {1}` at good points.
- **Still dies on the core.** Injectivity does not create bijectivity of non-core letters, and
  Theorem B applies verbatim to the pattern's marked relators (`fe = 1`) and their (C2)
  closure. So folding certificates for Phi reduce, on core letters, to separating permutation
  models of the core subpresentation of the deficit pattern's canonical host.
- **Why it does not help on simple Kazhdan hosts.** A deficit pattern certified this way would
  need its core words visible to permutation models. Nothing in property (T) or simplicity of
  the host enters, since the certificate sees only the canonical host of the pattern
  (Proposition 3 of `median-matching-entropy-translation-2026-09-12.md`), and that host is
  never simple Kazhdan in general.
- **Where the transplant dies for the target:** Theorem B(3) on core words, the same step as
  the surjunctivity count. This is recorded on the target's `## Attempts`.

## 5. The open step (can fail on its own)

**Extension problem.** Suppose permutation models of `B(D,E)` with defect tending to `0` move
every core word of a core-expressible distinguished pair of `W` at density at least
`δ > 0`, uniformly. Does `(D, E, W)` then admit act models with `λ -> 0` and
`|U_1| >= δ'|V|`?

**Why it can fail.**
- Non-core letters are determined along (C2)-type relators by core permutations and other
  non-core maps.
- Cycles of such relators impose `a_m ∘ π = a_m` or `b_s = π ∘ b_s` for core words `π`.
  Absorbing them folds `a_m` along `π`-orbits.
- Folding may merge distinguished window outputs that are not core-expressible.
- The constant-letter fold of Section 3 does merge them (Remark on other folds), so the
  construction must be genuinely non-constant.

**If it holds.** Strict design ⇒ some distinguished window pair is core-expressible, with core
word invisible in `B(D,E)`. This sharpens `sofic-radical-localizes-garden-of-eden-windows`
from `Rad(<M>)` to the sofic radical of the core table group. With trivial core (no marked
pair beyond `(1,1)` and no (C2) propagation), it says the design is never strict.

## 6. Relation to existing nodes

- **`sofic-radical-localizes-garden-of-eden-windows`.**
  - There: permutation models of the memory group, collisions allowed.
  - Here: arbitrary maps and two layers, and Theorem B shows the gain is confined to non-core
    letters.
- **`strict-pairs-transfer-to-table-realizations`.**
  - There: exact homomorphisms into groups.
  - Here: finite transformation acts. The total fold is not a group quotient (Remark in
    Section 3).
- **`strict-automata-live-on-canonical-table-groups`.** That gives the canonical group `U_E`.
  `B(D,E)` is the subpresentation on letters forced invertible in every finite act.
- **`forward-relations-of-a-counterexample-have-a-nonsofic-core`.**
  - There: the 2-core, obtained by peeling private generators (Tietze).
  - Here: the bijective closure, a different set (Section 2).

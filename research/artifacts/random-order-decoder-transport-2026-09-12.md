# Random-order decoder transport: an exact identity for injective automata, and the domination target

Lane `w3-strategist-pos`, 2026-09-12. Mathematics on paper only.

## 0. Setup

- `G` is a countable group and `A`, `B` are finite alphabets. `kappa : A^G -> B^G` is an injective automaton,
  `kappa(x)(g) = mu((x(gm))_(m in M))`.
- `N` is the memory of a left inverse, with `e in N`: `x(g) = nu((y(gn))_(n in N))`, where `y = kappa(x)`.
- `x` has the uniform product law. `U = (U(g))_(g in G)` are i.i.d. uniform labels on `[0,1]`, independent of `x`.
  Put `g ≺ h` iff `U(g) < U(h)`, and `past(h) = {k : k ≺ h}`.
- For `n in N` and `g in G`, the **transport term** is
      t_n(g) = I( x(g) ; y(gn) | y(gN ∩ past(gn)), U ),
  a conditional mutual information averaged over `U`. The joint law of `(x, y, U)` is invariant under left
  translation and `kappa` is equivariant, so `t_n(g) = t_n(e) =: t_n`.

## 1. Theorem 1 (transport identity)

(a) Input side: `sum_(n in N) t_n = log |A|`.

(b) Output side: at the single site `e`,
      sum_(n in N) I( x(n^-1) ; y(e) | y(n^-1 N ∩ past(e)), U ) = log |A| .

*Proof.* (a) Fix `U` and list `N` as `n_1 ≺ ... ≺ n_k`, so that `N ∩ past(n_i) = {n_1, ..., n_(i-1)}`. The chain
rule gives `sum_i I(x(e); y(n_i) | y(n_1), ..., y(n_(i-1))) = I(x(e); y(N)) = H(x(e)) = log |A|`, because `x(e)` is a
function of `y(N)`. `U` is independent of `(x, y)`, so averaging over `U` keeps the value.
(b) Translate by `n^-1`: `t_n(e) = t_n(n^-1)`, and `n^-1 n = e`. So the output-side term at `e` for `n` is `t_n`, and (a)
gives the sum. QED

**Remark 1.1.** This is the mass-transport principle for a countable group with counting measure. The edge mass
`f(g, gn) = t_n` leaves each input site in total `log |A|` and arrives at each output site in total `log |A|`. It uses
exactly two facts: the index set is the group itself, and the symmetry acts on the left while the memory acts on
the right. Theorem 1 holds for every group.

## 2. Calibrations

**2.1 Tree calibration** (`end-fixing-tree-symmetries-carry-strict-automata`).
- Setup: `tau(x)(v) = x(p(v))` on the 3-regular tree, with its decoder over the two children.
- Input side at `v`: `log |A|`.
- Output side at `w`: only `g = p(w)` contributes. The term is `I(x(p(w)); y(w) | y(sibling))` when the sibling is
  in the past, which is `0`, and `log |A|` otherwise. Its expectation is `(1/2) log |A|`.
- So the mass out of a vertex is `log |A|` and the mass into a vertex is `(1/2) log |A|`, and Theorem 1 fails. The
  ratio `2` is the modular function of `Aut(T, xi)` along `p`.
- Meanwhile `H(y(w)) = log |A|`, so the domination inequality of Section 3 holds there.

The strict automaton is paid for by transport imbalance, which is exactly the group-structure input the
calibration demands.

**2.2 Inertness** (`measure-conjugacy-invariants-cannot-certify-surjectivity`). The terms `t_n` are functionals of
the joint coordinate processes `(x, y, U)`, not of the isomorphism class of `G ↷ (B^G, kappa_* mu)`. The
inertness theorem does not apply to them.

**2.3 Finite left-inverse witness** (`finite-left-inverse-identity-does-not-force-balance`). The witness lives on
the tree group, where 2.1 shows the transport identity fails. It does not touch Theorem 1.

**2.4 Trivial-plus-free lesson** (`dyadic-root-displacement-data-admit-trivial-plus-free-models`). A single scalar
with its exact inequalities can be consistent with every value, and `H(y(e))` alone is such a scalar (Corollary 2).
What the plan adds is a vector of `|N|` terms with a fixed sum, together with the joint law that produces them.

**2.5 Check on Z.**
- Setup: `A = B = (Z/2)^2`, with `kappa(a, b)(i) = (a(i), b(i) + a(i+1))`. The decoder is `a(i) = y_1(i)` and
  `b(i) = y_2(i) + y_1(i+1)`, so `N = {0, 1}`.
- Output side at `0`, in bits:
  - `n = 0`: `I(x(0); y(0) | y(1))` is `2` if `1 ≺ 0` and `1` otherwise, so the mean is `3/2`;
  - `n = 1`: `I(x(-1); y(0) | y(-1))` is `1` if `-1 ≺ 0` and `0` otherwise, so the mean is `1/2`.
- The sum is `2 = log_2 |A|`, as Theorem 1 says.

## 3. The domination target

**Corollary 2.** For a fixed injective `kappa`, put `Z_n = y(n^-1 N ∩ past(e))`. Then

      H(y(e)) >= log |A|   iff   sum_(n in N) I(x(n^-1); y(e) | Z_n, U) <= H(y(e)) .

So the claim `injective-ca-random-order-transport-is-dominated` (domination for every group and every injective
automaton) is equivalent to `injective-ca-images-have-full-single-site-entropy`, hence to the goal. It is a normal
form, and the value lies in what it isolates.

**3.1 What is free.** If every `Z_n` were empty, domination would follow from superadditivity of mutual information
over independent sources. The inputs `x(n^-1)`, `n in N`, sit at distinct sites and are independent, so
`sum_n I(x(n^-1); y(e)) <= I(x(N^-1); y(e)) <= H(y(e))`. The whole problem is carried by the conditionings `Z_n`,
which are the other decoder outputs of the input site `n^-1` that lie in the random past of `e`.

**3.2 Averaging is necessary (Proposition 3).** Per-realization domination fails for a bijective automaton on Z.
- In 2.5, take the realization with `1 ≺ 0` and `-1 ≺ 0`.
- The output-side sum is `2 + 1 = 3` bits, while `H(y(0)) = 2`.
- So no pointwise information inequality proves the target. Any proof must average over the invariant random
  order, which is the mass-transport step again.

**3.3 Where the first open case is.**
- Two-point decoder memory is already closed. `amenable-decoder-memory-forces-surjectivity` proves surjectivity
  whenever the decoder memory generates an amenable group, and `{e, s}` generates a cyclic group. So domination
  holds for every injective automaton whose decoder memory group is amenable. This lane first proposed the
  two-point case as open and withdrew it before landing.
- The same theorem says a strict pair needs a nonamenable decoder memory group. The smallest open case is
  therefore three-point decoder memory `N = {e, s, t}` with `<s, t>` nonamenable. Claim:
  `three-point-decoder-memory-injective-ca-are-surjective`.
- In transport form, the output side at `e` has three terms, for the input sites `e`, `s^-1`, `t^-1`. The conditionings
  are the outputs at `{s, t}`, `{s^-1, s^-1 t}` and `{t^-1, t^-1 s}` that lie in the random past of `e`. Domination is a
  finite information inequality among the outputs at those seven sites and the inputs at `e, s^-1, t^-1`. The only
  inputs are the law of `(x, U)` and the fact that `y` is a finite block code of `x`.
- Group structure enters only through the coincidences among the seven sites, for instance `s^-1 t = t^-1 s` when
  `(s^-1 t)^2 = e`. So the lemma can be checked word by word against the relations of `<s, t>`.

**Payoff.**
- A proof of domination in the three-point case would be a surjunctivity theorem for a nonamenable decoder
  memory class over every host, nonsofic ones included, with no finite models and no peeling.
- A strict automaton with three-point decoder memory would be a counterexample of a very rigid shape. Its seven-site
  information pattern is directly checkable against the Leavitt hosts.

## 4. Candidates checked and discarded on the way

- **Exactness transfer.**
  - Plan: replace Folner windows by the almost-equivariant probability vectors `m_x` of a topologically amenable
    action. The Garden-of-Eden count packs left translates `hW`, while the decoder loss is the right boundary
    `d_N E` of `decoder-window-fiber-bound-loses-exactly-the-boundary`.
  - Where it dies: an amenable action controls `||g m_x - m_(gx)||`, which is left equivariance across points, and
    gives no right-Folner set at a fixed point. Averaging over points needs an invariant measure on the boundary,
    and such a measure exists only when `G` is amenable.
- **Free subrelations plus the f-invariant.**
  - Plan: Gaboriau--Lyons put a free `F_2` action inside the Bernoulli orbit relation, as a factor of auxiliary
    labels `u`. Apply the relative f-invariant along it to `(u, x)` versus `(u, kappa x)`.
  - Where it dies: the coordinate partition is not generating for the subrelation, because the `F_2`-orbit misses
    most of the `G`-orbit, and `kappa` is not local in the tree metric. The relative f-invariant is also a
    conjugacy invariant.
- **Symbol symmetrization.**
  - Plan: form `prod_(rho in Sym A) rho tau rho^-1`, which is strict and commutes with `Sym A` acting on `A^(Sym A)`.
  - Where it dies: that action is not transitive, so the site law is uniform only on orbits. Theorem 1 of the
    single-site artifact skews across orbits, and there is no contradiction.
- **Sizes on the monoid.** Not re-derived. `automaton-monoid-intrinsic-sizes-2026-09-12.md` Section 5 already
  closes the intrinsic candidates.

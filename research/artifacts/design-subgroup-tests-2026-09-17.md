# Design subgroup tests: the IRS strengthening as graphing surjunctivity, and where C1 dies (swarm-0917-w7-w7-gs-follow, 2026-09-17)

Lane: follow-through on `gottschalk-surjunctivity-conjecture`, wave-6 item w6-gs-last2 (the IRS route's one open
hole `non-co-sofic-free-group-irs-carry-no-strict-design`, called P1' below). Family: reframing.

Notation is that of `irs-surjunctivity-heretic-2026-09-17.md` (the heretic artifact), Section 2:
`Gamma = F_r`, `X_H = H\Gamma` with the right action, designs `D = (tau, sigma)` of shape-dependent automata with
radii `R_tau`, `R_sigma`, `rho = R_tau + R_sigma`, and the clopen events forward-bad and reverse-bad at the root
with densities `eps_D(mu)` and `delta_D(mu)`. The letter `r` is reserved for the rank. `b_k` is the number of
vertices in the radius-`k` ball of the `2r`-regular tree. `C_D = b_(R_tau) + b_(2 rho) |A|^(b_rho) ln|A|` is the
rank-corrected constant of `co-sofic-free-group-irs-carry-no-strict-design`. "Theorem 4.1 of the heretic artifact"
below always means that corrected inequality `delta_D <= C_D eps_D` on co-sofic IRS: the heretic's literal
constant was refuted. P1 is
`free-group-irs-carry-no-strict-design`, C1 is `some-free-group-irs-carries-a-strict-design`, and C2 is
`irs-strict-designs-yield-nonsurjunctive-groups`.

Nodes written from this artifact:

- `irs-surjunctivity-iff-pmp-graphing-surjunctivity` (Section 1, proved);
- `design-test-universality-forces-surjunctive-groups-sofic` (Section 4, proved);
- `hot-surjunctivity-tools-hold-on-irs-schreier-networks` (Section 5, proved; answers bus need 9f00a635);
- routes `...-proof` for each of the three.

No step of this artifact proves or refutes the goal, P1, P1', C1 or C2. It reformulates P1, audits which tools
can prove it, and kills one class of approaches to C1 with a named obstruction.

## 0. Results in one paragraph each

1. **P1 is Gottschalk for p.m.p. graphings.** P1 over all ranks is equivalent to: for every p.m.p. action of a
   finitely generated free group and every pair of finite-radius cellular rules on its orbits whose local tables are
   arbitrary measurable functions of the point, `sigma tau = id` on a.e. orbit forces `tau` onto on a.e. orbit.
   The colours cost only extra free generators.
2. **P1 is automatically robust.** By compactness of IRS space, P1 holds iff for every design `D` and `eta > 0`
   there is `kappa > 0` such that `delta_D >= eta` forces `eps_D >= kappa` on every IRS.
3. **A C1 witness is an Aldous-Lyons gap of a special test.** It is a design test with perfect forward
   completeness whose IRS value beats every finite Schreier graph.
4. **Obstruction.** Call the closed convex set cut out by all design inequalities `delta_D <= C_D eps_D` the
   design-sofic set `S_des`. At normal Dirac points `S_des` is exactly surjunctivity, and the co-sofic set is exactly
   soficity. So any proof of C1 by showing that design inequalities detect non-co-soficity (universality) also proves
   that every surjunctive group is sofic. Any "compiler" that turns perfect-completeness Aldous-Lyons gaps into
   designs strict on their whole face proves that every finitely presented non-sofic group is non-surjunctive.
   Every such approach must use nonatomicity.
5. **HOT audit.** Mass transport, Bernoulli preservation, the random-order transport identity (with its
   domination target), and the Rokhlin deficit (relative to the base, and with no amplification needed) all hold
   verbatim on IRS Schreier networks with shape-dependent rules. A proof of the goal built from these tools therefore proves P1, and a single C1 witness
   refutes every such proof.
6. **Where C2 dies, localized.** For free actions, a strict measurable-rule pair whose table process has full
   support is an ordinary strict automaton over the group, with a product alphabet. C2 therefore dies exactly at
   fibred injective maps over a proper subshift base. For non-free actions the base is the shape process, which is
   never a full shift.

## 1. P1 is Gottschalk for p.m.p. graphings

**Conventions.**
- The heretic artifact fixes the notions for one Schreier graph `X_H`. The design is strict on `X_H` iff
  `sigma tau = id` and `tau` is not onto on `A^{X_H}`.
- Its Lemma 2.1 says this holds iff every vertex is forward-good and some vertex is reverse-bad.
  - Forward-good at `v`: `sigma(tau x)(v) = x(v)` for all `x`.
  - Reverse-bad at `v`: `tau(sigma y)(v) != y(v)` for some `y`.
  - Both are conditions on the rooted `rho`-ball at `v` only.
- By invariance of `mu`, the vertex `Hg` of `X_H` is forward-bad with probability `eps_D(mu)` (substitute
  `H -> g^-1 H g`). So `eps_D(mu) = 0` iff a.e. graph has no forward-bad vertex. Hence `D` is strict for `mu`
  (strict on a positive-measure set of graphs, `sigma tau = id` on a.e. graph) iff `eps_D(mu) = 0 < delta_D(mu)`.

**Definition (measurable-table rules).**
- Let `Gamma = F_r` act on a standard probability space `(Omega, nu)`, measure preservingly and on the right. The
  action need not be free.
- The orbit graph of `w` has vertex set `w.Gamma` and edges `u -- u.s` for the generators `s`. The ball
  `B_R(w)` is `{w.g : |g| <= R}`.
- A *measurable-table rule* of radius `R` is a measurable `w -> tau_w`. Here `tau_w` is a map from `A^{B_R(w)}` to
  `A`, recorded as a function of the word-indexed tuple `(x(w.g))_{|g| <= R}`, and the tuple has repeated entries
  when words coincide at `w`.
- The rule acts on configurations `x : w.Gamma -> A` by `(tau x)(u) = tau_u(x|B_R(u))`.
- A *strict measurable pair* is `(tau, sigma)` such that `sigma tau = id` on `A^{w.Gamma}` for a.e. `w`, and `tau`
  is not onto `A^{w.Gamma}` for a positive-measure set of `w`.
- **GG(r)**: no p.m.p. action of `F_r`, no finite `A` and no pair of measurable-table rules gives a strict
  measurable pair. **P1(r)** is P1 at rank `r`.
- Only finitely many local maps of each radius exist. So a pair of rules is a measurable colouring
  `c : Omega -> T`, where `T` is the finite set of table pairs actually used, `L = |T|`.

**Theorem 1.**
- (a) GG(r) implies P1(r).
- (b) P1(r + L) implies GG(r) for pairs using at most `L` table pairs.
- Hence P1 at all ranks is equivalent to GG at all ranks.

**Lemma 1.1 (realization).**
- Statement: let `mu` be an IRS of `Gamma`. Then there is a p.m.p. action `Gamma -> (Omega, nu)` with
  `Stab(w) ~ mu`, in fact `Stab(w) = H(w)` a.s. for a factor map `H : Omega -> Sub(Gamma)` pushing `nu` to `mu`.
  The orbit graph of `w` is then isomorphic to `X_{H(w)}` by `w.g <-> H(w)g`, rooted at `w <-> H(w)`.
- Construction: `Omega` is the set of pairs `(H, xi)` with `H in Sub(Gamma)` and `xi in [0,1]^Gamma` constant on
  every right coset `Hk`. The action is `(H, xi).g = (g^-1 H g, k -> xi(gk))`.
- Well defined: if `k' = g^-1 h g k` then `g k' = h g k`, so the new label is constant on cosets of `g^-1 H g`.
- Right action: `((H, xi).g).g' = (g'^-1 g^-1 H g g', k -> xi(g g' k))`.
- The measure: `nu` draws `H ~ mu`, then i.i.d. uniform labels on `H\Gamma`.
- `nu` is invariant: `mu` is conjugation invariant, and `Hgk -> (g^-1Hg)k` is a bijection
  `H\Gamma -> (g^-1Hg)\Gamma` carrying the i.i.d. labels to i.i.d. labels.
- The stabilizer is `H`. It clearly contains `H`. If `g` stabilizes, then `g in N(H)`, and `xi` is invariant under
  the permutation `Hk -> Hgk` of `H\Gamma`. For `g notin H` this permutation moves the coset `H` to `Hg != H`, so it
  forces `xi(H) = xi(Hg)`, an event of probability `0`. There are countably many `g`.
- The orbit identification is standard once `Stab = H`. QED

*Proof of (a).*
- Let `D` be strict for `mu`. Realize `mu` by Lemma 1.1.
- The heretic tables at the vertex `H g` depend on the rooted shape `(X_H, Hg)`, which is the rooted ball at
  `w.g` of the orbit graph. So `tau_w := (heretic table at the shape of Stab(w))` is a measurable-table rule, and
  likewise `sigma_w`.
- Under the orbit identification, the pair acts on `A^{w.Gamma}` exactly as `D` acts on `A^{X_{H(w)}}`.
- Strictness for `mu` transfers verbatim, which contradicts GG(r). QED

*Proof of (b) (colour lemma).*
- Let `(tau, sigma)` be a strict measurable pair for `F_r -> (Omega, nu)`, with colouring `c : Omega -> T`.
- Put `Gamma' = F(s_1, ..., s_r, b_t : t in T)`, of rank `r + L`, acting on `Omega' = Omega x [0,1]` with
  `nu x Leb`:
  - `(p, s).s_i = (p.s_i, s)`;
  - `(p, s).b_t = (p, s)` if `c(p) = t`, and `(p, s + alpha mod 1)` otherwise, with `alpha` irrational.
- Each generator is a measure-preserving bijection, so this is a p.m.p. action of the free group `Gamma'`.
- Colours are visible. `b_t^k` fixes `(p, s)` for `k != 0` iff `c(p) = t`. So in the orbit graph, the vertex
  `(p, s)` carries exactly one generator loop among the `b`'s, namely `b_{c(p)}`.
- Structure of orbits: `Gamma` changes only `p`, and the `b`'s change only `s`. So the `Gamma'`-orbit of `(p, s)`
  lies in `(p.Gamma) x (s + Z alpha)`. Its `Gamma`-components are the sets `{(q.g, s') : g in F_r}` with `q` in
  `p.Gamma`. Each is isomorphic, as an `s`-labelled and `c`-coloured graph, to the coloured orbit graph of `p` via
  `(q.g, s') -> q.g`.
- The design `D'` on `Gamma'` has radius `max(R, 1)`. At a vertex `v`, `tau'` reads the unique `b`-loop at `v`,
  which gives the colour `t`. It then applies `tau_t` to the tuple `(x(v.g))_{g in F_r, |g| <= R}`, and `sigma'`
  works the same way. These tables are functions of the rooted ball shape, as the heretic designs require.
- `D'` acts on each `Gamma`-component separately, as `(tau, sigma)` acts on `A^{p.Gamma}`.
- So `sigma' tau' = id` on the `Gamma'`-orbit of `(p, s)` iff `sigma tau = id` on `A^{p.Gamma}`, and `tau'` is not
  onto iff `tau` is not onto `A^{p.Gamma}`.
- The good set of `p` is conull and the bad set has positive measure, and both are `Gamma`-invariant. The same then
  holds for `(p, s)` under `nu x Leb`.
- The orbit graph of `w` is always `X_{Stab(w)}`. So `D'` is strict for the IRS `Stab_*(nu x Leb)` of `F_{r+L}`,
  which contradicts P1(r + L). QED

**Proposition 1.2 (full-support tables make C2 hold for free actions).**
- Setting: let `G` be a finitely generated group with a finite generating set, acting freely and measure
  preservingly on `(Omega, nu)`. Let `(tau, sigma)` be a strict measurable pair on its orbit graphs, which are
  Cayley graphs of `G`.
- Let `c(w) = (colour of w.g)_{g in G}` be the table process, a `G`-equivariant map `Omega -> T^G`.
- Claim: if `c_* nu` has full support in `T^G`, then `G` is not surjunctive.

*Proof.*
- On `(T x A)^G` put `Tt(c, x) = (c, tau_c x)` and `Ss(c, y) = (c, sigma_c y)`, where `tau_c x(g)` applies the
  table `c(g)_tau` to `x` on `g B_R`. These are cellular automata over `G`.
- `Ss Tt = id` everywhere. Forward-goodness at the root is a condition on the pattern `c|B_rho`. It holds at
  `nu`-a.e. point, so it holds for every pattern of positive probability. By full support that is every pattern,
  and translating gives every site.
- `Tt` is not onto. A reverse-bad point has positive probability, so some pattern `P` on `B_rho` with positive
  probability admits `y` with `tau_c sigma_c y(e) != y(e)` for every `c` extending `P`.
  - If `Tt(c, x) = (c, y)` then `y = tau_c x`, so `tau_c sigma_c y = tau_c sigma_c tau_c x = tau_c x = y`.
  - So `(c, y)` is not in the image.
- Hence `Tt` is strict over `G`, with alphabet `T x A`. QED

**Where C2 dies.**
- Without full support, `Y = supp(c_* nu)` is a proper subshift of `T^G`. The pair is then an injective,
  non-surjective map fibred over `Y` and commuting with the shift.
- Extending the tables off `Y` destroys `Ss Tt = id` at patterns outside `Y`.
- So C2 for free actions reduces exactly to the question: does a strict fibred pair over some proper subshift base
  `Y`, carrying an invariant measure of full support on `Y`, produce a strict pair over a full shift? The heretic
  C2 programme has no step for this.
- For non-free actions the base is the stabilizer process `w -> Stab(w)`. It is not the full shift over any group
  acting freely, so even Proposition 1.2 has no analogue. This is where the atomic-hull route of the heretic
  artifact has to pass through normalizer quotients (its Theorem 3.1).

**Remark 1.3 (a new place to look for C1).**
- Let `G = F_r / N` be sofic. Suppose some free p.m.p. action of `G` carries a strict measurable pair. Pull it back
  to `F_r` and apply the colour lemma. This gives a C1 witness on `F_{r+L}`.
- Proposition 1.2 and Gromov-Weiss force such a pair to have a table process without full support.
- The heretic Theorem 4.1 forces the resulting IRS to be non-co-sofic.
- Whether such coloured actions exist is open. The search is for non-sofic free actions of sofic groups with a
  strict pair of proper-subshift tables. It uses no non-sofic group.

## 2. P1 is automatically robust

**Proposition 2.1.**
- P1 holds iff for every design `D` and every `eta > 0` there is `kappa > 0` such that every IRS `mu` with
  `delta_D(mu) >= eta` has `eps_D(mu) >= kappa`.
- Equivalently, C1 holds iff some design `D` has *approximate witnesses*: IRS `mu_n` with `delta_D(mu_n) >= eta > 0`
  and `eps_D(mu_n) -> 0`.

*Proof.*
- `IRS(Gamma)` is weak-* compact: it is a closed subset of `Prob(Sub(Gamma))`, and `Sub(Gamma)` is compact.
- `eps_D` and `delta_D` integrate indicators of clopen sets, so they are continuous.
- A limit point of approximate witnesses has `delta_D >= eta` and `eps_D = 0`. By the conventions of Section 1 it
  carries the strict design `D`.
- Conversely, a strict design is a constant approximate witness. QED

**The linear form.**
- QP1 says: for every `D` there is `C` with `delta_D <= C eps_D` on all IRS. The heretic Theorem 4.1 is QP1 with
  `C = C_D` on the co-sofic IRS.
- QP1 implies P1.
- The converse would need a *repair* step R: from IRS on which `delta_D / eps_D` is unbounded, produce IRS with
  `eps_D -> 0` and `delta_D` bounded below, possibly for a different design.
- No mechanism for R is known.
  - Tensoring `D` with itself does not lower the forward error: a product site is forward-bad whenever either
    factor is.
  - Iterating `tau` does not reduce it.
  - Forward-badness quantifies over all inputs, so marker surgery at the bad sites cannot remove it.

## 3. A C1 witness is an Aldous-Lyons gap of a design test

**The test.**
- For a design `D` and `p in (0,1)`, let `T_{D,p}` be the one-round local test on a rooted Schreier graph:
  - with probability `p` it checks that the root is forward-good;
  - with probability `1 - p` it checks that the root is reverse-bad.
- Its value on an IRS is `val_{D,p}(mu) = p (1 - eps_D(mu)) + (1 - p) delta_D(mu)`. This is an affine continuous
  functional, given by the integral of a clopen function of the rooted `rho`-ball.
- The shape matches the local-statistic tests in the Aldous-Lyons framework. Nothing from the literature is used
  here; in particular no formal definition from Bowen-Chapman-Lubotzky-Vidick (arXiv 2408.00110) is relied on.

**Proposition 3.1.** Put `p_D = C_D / (1 + C_D)`, and let `p >= p_D`.
- (a) `val_{D,p} <= p` on every co-sofic IRS.
  - By Theorem 4.1 of the heretic artifact, `val <= p - p eps + (1 - p) C_D eps <= p`, because `(1 - p) C_D <= p`.
  - This holds on finite Schreier graphs, and passes to the closure by continuity.
- (b) If `D` is strict for `mu` then `val_{D,p}(mu) = p + (1 - p) delta_D(mu) > p`.
  - So a C1 witness is a *perfect-completeness* gap: the forward half of the test is passed with probability 1,
    and the total beats every finite graph.
- (c) Let DIV(D) say that some IRS has `delta_D > C_D eps_D`. Then DIV(D) holds iff some IRS has
  `val_{D, p_D} > p_D`, since `(1 - p_D) delta > p_D eps` iff `delta > C_D eps`.
- (d) Hence: some `D` has DIV(D) iff QP1 fails with the heretic constants. And C1 holds iff DIV holds together with
  the repair step R.

**Comparison with the repository's quantum gap.**
- `perfect-zpc-irs-quantum-gap-game` is established: it is a finite game with perfect ZPC-IRS value and quantum
  value below `1/2`.
- It shows that perfect IRS values can separate from finite-dimensional behaviour for *some* local tests.
- The design tests are a specific family. Their "finite" side is controlled by a counting inequality (Theorem 4.1)
  rather than by operator algebra, and nothing transfers from that game to them.
- Section 4 shows that the family cannot be made universal cheaply.

## 4. Obstruction: the design-sofic set at normal Dirac points

**Definition.** `S_des = { mu in IRS(Gamma) : delta_D(mu) <= C_D eps_D(mu) for every design D }`.
- `S_des` is closed, because each constraint is continuous.
- It is convex, because each constraint is affine.
- It contains the co-sofic set, because Theorem 4.1 of the heretic artifact gives the constraints on finite
  Schreier graphs, and closedness and convexity pass them to the closed convex hull.

**Theorem 4.** Let `N` be a normal subgroup of `F_r` and `G = F_r / N`.
- (a) `delta_N in S_des` iff `G` is surjunctive.
- (b) `delta_N` is co-sofic iff `G` is sofic.

*Proof of (a).*
- **Setup.** Left multiplication `Nk -> N g^-1 k` commutes with the right action, and carries the root `Ng` to `N`.
  So all rooted shapes of `X_N` are equal. A design therefore has constant tables on `X_N`: it is a pair of
  cellular automata over `G`, and `eps_D(delta_N)` and `delta_D(delta_N)` each lie in `{0, 1}`.
- **If `G` is surjunctive.**
  - If `eps = 0`, then `sigma tau = id`, so `tau` is injective, hence onto, hence `tau sigma = id` and `delta = 0`.
  - If `eps = 1`, then `delta <= 1 <= C_D`, since `C_D >= b_(R_tau) >= 1`.
  - Either way `delta_N` satisfies every constraint.
- **If `G` is not surjunctive.**
  - Take an injective, non-surjective automaton `tau` over `G`.
  - Its image is closed and invariant, and the inverse on the image is continuous and equivariant. So it has a
    local rule on image patterns. Extend that rule arbitrarily to all patterns. This gives an automaton `sigma`
    with `sigma tau = id`.
  - Lift each memory element to a word of `F_r`. This gives a shape-independent design with `eps = 0` and
    `delta = 1 > 0 = C_D eps`.
  - So `delta_N notin S_des`. QED

*Proof of (b)* (standard; included for completeness).
- **If finite Schreier graphs `X_n = (V_n)` converge to `delta_N`.**
  - For every finite `W subset F_r`, the fraction of `v` with `[v.w = v iff w in N]` for all `w in W` tends to `1`.
  - Fix a lift `w_g in F_r` of each `g in G`, and put `phi_n(g)(v) = v.w_g^-1`.
  - `w_h^-1 w_g^-1 (w_{gh})` lies in `N`, so `phi_n(g) phi_n(h)` and `phi_n(gh)` agree at most points.
  - For `g != e`, `phi_n(g)` has few fixed points.
  - So `phi_n` is a sofic approximation of `G`.
- **If `G` is sofic.**
  - Given a sofic approximation `psi_n : G -> Sym(V_n)`, let the generator `s_i` act by `psi_n(s_i bar)^{-1}`, read
    as a right action.
  - Every fixed word then acts, at most points, as `psi_n` of its image in `G`. So `v.w = v` at most points iff
    `w in N`.
  - The IRS of these finite actions converge to `delta_N`. QED

**Corollary 4.1 (universality is a group-theoretic statement).**
- Suppose `S_des` equals the co-sofic set, which is the natural way to prove C1 from the non-co-sofic IRS of
  `non-cohyperlinear-irs-exists`.
- Then Theorem 4 makes every finitely generated surjunctive group sofic.
- Gromov-Weiss gives the converse inclusion. So universality at normal Dirac points is *equivalent* to
  "surjunctive iff sofic" for finitely generated groups.
- In particular, universality together with the goal would make every finitely generated group sofic.
- Universality restricted to any family of IRS containing the normal Dirac points is at least this strong.

**Corollary 4.2 (compilers from perfect-completeness gaps).**
- *Definition.* A *perfect-completeness gap* is a clopen `F subset Sub(F_r)` and an IRS `mu` with `mu(F) = 0` and
  `inf_X mu_X(F) > 0` over finite Schreier graphs `X`.
- *Definition.* A *compiler* assigns to every such gap a design `D` that is strict for `mu`. (Strict on the whole
  face `{mu : mu(F) = 0}` is a stronger version.)
- *Claim.* If a compiler exists, every finitely presented non-sofic group is non-surjunctive.

*Proof.*
- Let `G = <S | R>` be finitely presented and non-sofic, with `N` the normal closure of the finite set `R`.
- For finite `W subset F_r \ N`, put `F_{R,W} = { H : some r in R is not in H, or some w in W is in H }`. It is
  clopen, and `delta_N(F_{R,W}) = 0`.
- **Step 1: some `W` and `c > 0` give `mu_X(F_{R,W}) >= c` on every finite `X`.**
  - Suppose not. Take `W_n` = the words of length `<= n` outside `N`, `c_n -> 0`, and finite actions `V_n` with
    `mu_{V_n}(F_{R,W_n}) < c_n`.
  - Write a fixed `m in N` as a product of `k` conjugates `u_i r_i^{+-1} u_i^-1`.
  - The point `v` is fixed by `m` if each of `k` successive points, obtained from `v` by fixed bijections of
    `V_n`, is fixed by the corresponding relator.
  - Each such condition fails on less than a `c_n` fraction, so `m` fails on at most `k c_n`.
  - A fixed `w notin N` lies in `W_n` for large `n`, so it fixes less than a `c_n` fraction.
  - Hence `mu_{V_n} -> delta_N`. So `delta_N` is co-sofic, contradicting Theorem 4(b).
- **Step 2.** `(F_{R,W}, delta_N)` is a perfect-completeness gap.
  - The compiler gives a design strict for `delta_N`.
  - By Theorem 3.1 of the heretic artifact (`N(N)/N = G`), `G` is not surjunctive. QED

**What the obstruction kills, and what survives.**
- Killed:
  - every argument for C1 that proves *universality* of design inequalities;
  - every argument that *compiles* Aldous-Lyons gaps into strict designs.
- Each of these, applied at normal Dirac points, decides surjunctivity of groups. It refutes the goal as soon as
  some finitely presented non-sofic group exists.
- The invariant is the value pair `(eps, delta) in {0,1}^2` at normal Dirac points. It dies at the step
  "non-co-sofic implies violates a design inequality", which at Dirac points is the step "non-sofic implies
  non-surjunctive".
- Surviving C1 routes must use *nonatomicity*: designs whose strictness uses an IRS with `0 < delta_D < 1`, off the
  atomic hull or at least off the normal Dirac points.
- `hull-irs-strict-designs-force-nonsurjunctive-or-non-uqs-groups` already shows that the atomic hull gives
  nothing without non-UQS or non-surjunctive groups.

## 5. HOT audit: the tools hold on IRS Schreier networks (answers bus need 9f00a635)

Throughout, `mu` is an IRS of `F_r`, and `D = (tau, sigma)` is a design with `eps_D(mu) = 0`. So a.e. `X_H` has
`sigma tau = id`. Write `q = |A|`, and let `o = H` be the root of `X_H`.

**5.1 Mass transport principle.**
- Statement: let `f(X, u, v) >= 0` be a Borel function of doubly rooted Schreier graphs, invariant under rooted
  isomorphism. Then `E_mu sum_v f(X_H, o, v) = E_mu sum_u f(X_H, u, o)`.
- This is standard (unimodularity of IRS). A self-contained proof follows.

*Proof.*
- **Choose representatives.** Fix an enumeration order `<` of `Gamma`. A vertex `v` of `X_H` is a coset, a subset of
  `Gamma`. Let `g_v` be its `<`-least element. Then
  `E sum_v f(X_H, o, v) = sum_g E[ f(X_H, H, Hg) 1[g = min Hg] ]`.
- **Substitute.** Put `H' = g^-1 H g`, which has law `mu`. The map `Hk -> H' g^-1 k` is an isomorphism
  `X_H -> X_{H'}` sending `(H, Hg)` to `(H' g^-1, H')`, and the coset `Hg` equals `g H'`.
- **Rewrite.** Substituting `u = g^-1`, the sum becomes
  `sum_u E[ f(X_{H'}, H'u, H') 1[u^-1 = min u^-1 H'] ]`.
- **Count once.** As `u'` ranges over the coset `H'u`, `u'^-1` ranges over `u^-1 H'`. So exactly one `u'` per vertex
  satisfies the indicator, and the sum is `E sum_w f(X_{H'}, w, o)`. QED

**5.2 Bernoulli preservation, per graph.**
- Statement: on any countable bounded-degree graph `X`, let a pair of finite-radius rules with arbitrary vertex
  tables satisfy `sigma tau = tau sigma = id`. Then `tau` preserves the uniform product measure on `A^X`.
- Proof: this is the proof of `bijective-ca-preserve-uniform-bernoulli-measure`, with no group used.
  - For a permutation `pi` of patterns on a finite window `W`, `sigma pi tau` fixes all coordinates outside
    `W B_{R_sigma}`.
  - On that finite set it is, for each outside configuration, a bijection. So it preserves the product measure.
  - Hence `tau_*` of the uniform product measure is invariant under every local permutation. So it is the uniform
    product measure.

**5.3 Random-order transport identity.**
- *Setup.*
  - Take `x` uniform on `A^{X_H}`, `y = tau x`, and i.i.d. uniform labels `U` on the vertices, with `u < v` iff
    `U(u) < U(v)`.
  - For `v in B_{R_sigma}(u)`, put `f(X, u, v) = I( x(u) ; y(v) | y(B_{R_sigma}(u) cap past(v)), U )`, computed
    given the graph `X`. Put `f = 0` otherwise.
  - `f` is a function of the rooted isomorphism class of `(X, u, v)`, because the tables are shape-dependent.
- *Input side.* `x(u)` is a function of `y|B_{R_sigma}(u)`. The chain rule in the order `<` gives
  `sum_v f(X, u, v) = I(x(u) ; y|B(u) | U) = log q`.
- *Output side.* By 5.1, `E_mu sum_u f(X_H, u, o) = log q`. This is the identity of
  `injective-ca-random-order-transport-identity`, with `n^-1` replaced by the input vertices `u` whose decoder ball
  contains `o`.
- *Corollary 2 carries over.* The same algebra gives: domination `E sum_u f(X_H, u, o) <= E H(y(o) | X_H)` holds iff
  `E H(y(o) | X_H) >= log q`.

**5.4 Rokhlin deficit, relative to the base.**
- *Setup.*
  - Realize `mu` as in Lemma 1.1 on `(Omega, nu)`, with coset labels `xi`.
  - Let `B` be its Bernoulli extension: add `x in A^Gamma`, constant on `H`-cosets, i.i.d. uniform on cosets.
  - Let `beta` be the base sigma-algebra.
- *Statement.* If `D` is strict for `mu`, then
  `h^Rok(B | beta) <= log q - (delta_D(mu) / b_{2 rho}) q^{-b_rho} < log q`.

*Proof.*
- **Markers.** Declare `v` a marker iff `v` is reverse-bad and `xi(v) < xi(u)` for every other reverse-bad `u`
  within distance `2 rho`.
  - Markers are `beta`-measurable: reverse-badness depends on the shape only.
  - Markers are pairwise more than `2 rho` apart, so their `rho`-balls are disjoint.
  - A reverse-bad `v` with `k <= b_{2 rho}` reverse-bad vertices within distance `2 rho` is a marker with conditional
    probability `1/k`.
  - So the marker density satisfies `lambda >= delta_D / b_{2 rho}`.
- **Missing pattern.** Let `c` be a marker. Reverse-badness gives a pattern `y_0|B_rho(c)` with
  `tau sigma y_0 (c) != y_0(c)`. Every image `y = tau x` satisfies `tau sigma y = y`. So `y|B_rho(c)` takes at most
  `q^m - 1` values, where `m = |B_rho(c)| <= b_rho`.
- **The partition `P` at a vertex.**
  - At a marker: `y|B_rho(c)`, recorded word-indexed.
  - Elsewhere in a marker ball: a blank.
  - Elsewhere: `y(v)`.
- **Generating.** Given `beta`, which knows the graph and the markers, the translates of `P` recover `y`, and hence
  `x = sigma y`. So `P` is generating relative to `beta`.
- **Entropy.** Apply mass transport (5.1), with each marker sending mass `1` to each vertex of its ball. This gives
  `H(P | beta) <= log q - E[ 1_{o marker} (m log q - log(q^m - 1)) ]`.
  - `-log(1 - q^{-m}) >= q^{-m} >= q^{-b_rho}`.
  - So the bound follows. QED
- *Why no amplification is needed.* In the group case the base is trivial, so markers cost `log 3`, and
  `strict-automaton-lowers-bernoulli-rokhlin-entropy-proof` amplifies the alphabet to pay for them. Here the markers
  are free, because the base carries the labels `xi`.
- *The robust HOT target.* The Rokhlin tool's IRS form is **relative maximality**: the Bernoulli extension of every
  p.m.p. base has relative Rokhlin entropy `log q`.
  - On finite orbits this is counting, and it is consistent with Theorem 4.1 of the heretic artifact.
  - Relative maximality over all IRS bases implies P1, by 5.4.

**5.5 Not audited in full.** Amenable-decoder-memory counting transfers in its counting form to pieces of a
hyperfinite subgraph. Over `F_r`, however, the decoder memory group is amenable only when it is cyclic. This is
recorded, not claimed.

**Conclusion for need 9f00a635.**
- Yes. Mass transport, Bernoulli preservation, the random-order transport identity with its domination target, and
  the Rokhlin deficit (relative to the base) all hold verbatim for shape-dependent designs on IRS Schreier networks.
- A contradiction derived from these tools alone, with no input false on IRS, therefore rules out strict designs on
  every IRS.
- So these tools can prove the goal only by proving P1. They are refuted as a proof method by a single C1 witness,
  which would have to be non-co-sofic.

## 6. Decomposition of the hole, and where this attempt stops

P1' (no non-co-sofic IRS carries a strict design) is the only open hole of the IRS route. This artifact leaves it
OPEN. It records the following.

**Equivalent forms of P1.** P1 is equivalent to each of:
- GG, over all ranks (Theorem 1);
- robust P1 (Proposition 2.1);
- "no design test `T_{D,p}` with `p >= p_D` has a perfect-completeness IRS value above `p`" (Proposition 3.1).

**Decomposition of C1** (the refutation side). C1 holds iff DIV and R both hold. Each can fail on its own.
- **DIV**: some IRS violates some co-sofic design inequality, `delta_D > C_D eps_D`. This is a quantitative
  Aldous-Lyons gap for one design test. It fails iff QP1 holds with the heretic constants.
- **R** (repair): the violation can be sharpened to approximate witnesses, meaning `eps -> 0` with `delta`
  bounded below. By compactness these give an exact witness.
- **Nonatomic requirement** (Section 4). Neither step can be proved by an argument that is uniform over normal
  Dirac points, unless that argument decides "surjunctive implies sofic" for finitely generated groups.
- **The cheapest open search target** (Remark 1.3). A non-sofic free action of a sofic group, carrying a strict
  pair with proper-subshift tables.

**Where C2 dies** (Section 1). At fibred injective maps over a proper subshift base, or over the stabilizer
process. Proposition 1.2 closes the full-support case.

**Status of what is proved here.**
- Theorem 1, Proposition 1.2, Proposition 2.1, Proposition 3.1, Theorem 4 and its corollaries, and 5.1-5.4 are
  complete proofs.
- They are elementary modulo the heretic artifact's Lemma 2.1, Theorem 3.1 and Theorem 4.1, and the standard
  Gromov-Weiss theorem.
- None of them proves or refutes P1, P1', C1, C2 or the goal.

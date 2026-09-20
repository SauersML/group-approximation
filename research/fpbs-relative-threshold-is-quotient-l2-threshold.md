---
rg: 2
id: fpbs-relative-threshold-is-quotient-l2-threshold
kind: claim
title: The relative threshold of an infinite normal subgroup equals the l2 threshold of its fibre-summed connectivity kernel, and where this holds the percolation Kesten gap is critical fibre l2 in disguise
distinct_from:
  fpbs-quotient-l2-threshold-sandwich: that proves the unconditional sandwich p_c <= p^Q_(2->2)(N;G) <= min{p_(2->2), p_c(N;G)}; this asserts the right inequality is an equality, and proves what that equality does to every proof of the Kesten premise.
  fpbs-percolation-kesten-normal-gap: that asserts p_c < p_c(N;G) for nonamenable Gamma/N; this is an identification of p_c(N;G) that holds or fails independently of that gap (it holds on amenable quotients, where the gap fails), and under which the gap becomes exactly boundedness of the critical fibre operator.
  fpbs-bk-majorant-kesten-gap-is-quotient-critical-l2: that kills Russo-BK proofs of the premise by the invariant ||S_(p_c)||; this extends the same invariant to every method, on each graph where the equality (even its weak form E') holds, and names the only escape: a graph with p_c = p^Q_(2->2)(N;G) < p_c(N;G).
  fpbs-amenable-wq-normal-pu-is-relative-pc: that identifies p_u with p_c(H;G) for amenable H; this asserts, for amenable normal N, that the common value is also p_(2->2)(G), which is the open equality p_(2->2) = p_u on that graph.
  fpbs-critical-sphere-fibre-operator-below-one: that is the open critical fibre operator condition over hyperbolic quotients; this does not assert it anywhere, and says the Kesten premise cannot be proved without it on graphs where the thresholds coincide.
---

**OPEN.**

**Notation.** As in `fpbs-quotient-l2-threshold-sandwich`:
`G = Cay(Gamma,S)`, `N` an infinite normal subgroup, `Q = Gamma/N`,
`sigma^N_p(q) = sum_(x in q) tau_p(o,x)`, and
`p^Q_(2->2)(N;G) = sup{p : ||sigma^N_p||_Q < infinity}`. By part 1 of that
node,

```text
||sigma^N_p||_Q = limsup_m (chi^(N,m)_p)^(1/m),     chi^(N,m)_p = sum_(y in N) T_p^m(o,y).
```

**Claim E.** For every finitely generated `Gamma`, every finite symmetric
generating set `S` and every infinite normal subgroup `N`,

```text
p_c(N;G) = p^Q_(2->2)(N;G).
```

In words: clusters start to meet `N` infinitely exactly when the multi-chain
relative susceptibilities `chi^(N,m)_p` stop growing at most exponentially
in `m`. The case `m = 1` is `chi^N_p`.

**Weak form E'(G,N).** If `p_c(G) < p_c(N;G)`, then
`p_c(G) < p^Q_(2->2)(N;G)`. By the sandwich, `E(G,N)` implies `E'(G,N)`.

## Consequences (proved here, from ESTABLISHED nodes)

**C1. The class-free conditional obstruction.**

*Statement.* Unconditionally, for each `(G,N)` with `N` infinite, exactly one
of the following holds:

* **(i)** `||sigma^N_(p_c)||_Q < infinity`, the critical fibre l2 condition;
* **(ii)** `p_c(G) = p^Q_(2->2)(N;G) < p_c(N;G)`, a strict failure of `E'` at `(G,N)`;
* **(iii)** `p_c(G) = p_c(N;G)`, no gap.

The gap `p_c < p_c(N;G)` is (i) or (ii). Under `E'(G,N)` it is (i), and (i)
implies `p_c < p_(2->2)(G)`.

*Proof.* By part 6 of the sandwich, (i) is equivalent to
`p_c < p^Q_(2->2)(N;G)`. By part 4 it then gives `p_c < p_c(N;G)`, and by
part 3 it gives `p_c < p_(2->2)(G)`. If (i) fails, `p^Q_(2->2) = p_c` by
part 3, and either `p_c(N;G) > p_c`, which is (ii), or not, which is (iii).
The three cases are disjoint by construction. ∎

*The invariant and the step where every method dies.* Let `M` be any argument
that proves the Kesten premise `p_c(G) < p_c(N;G)` for a class of pairs
`(G,N)` on which `E'` holds. Then `M` proves
`limsup_m (chi^(N,m)_(p_c))^(1/m) < infinity` on that class, and with it
Hutchcroft's `p_c < p_(2->2)`
(`fpbs-nonamenability-bounds-critical-connectivity-operator` on those
graphs). The invariant is `||sigma^N_(p_c)||_Q >= ||T_(p_c)||`.

`M` dies unless it bounds the exponential growth of the multi-chain critical
relative susceptibilities. The only way around this is for `M` to operate on
graphs of type (ii). There the Kesten gap holds while the critical fibre
operator is unbounded, so `M` must see a relative gap that is not an l2 gap.

This generalises the Russo-BK kill of
`fpbs-bk-majorant-kesten-gap-is-quotient-critical-l2` from one class of
proofs to every proof. The price is the hypothesis `E'`, which is supported
by the evidence below.

**C2. Amenable normal subgroups: E is p_(2->2) = p_u.** If `N` is amenable,
then `p^Q_(2->2)(N;G) = p_(2->2)(G)` (sandwich, part 3). Also
`p_c(N;G) = p_u(G)` (`fpbs-amenable-wq-normal-pu-is-relative-pc`; normal
subgroups are wq-normal). So `E(G,N)` is equivalent to `p_(2->2)(G) = p_u(G)`,
and `E'(G,N)` to [`p_c < p_u` implies `p_c < p_(2->2)`] on `G`. So Claim E
contains the equality of the l2 and uniqueness thresholds on every Cayley
graph with an infinite amenable normal subgroup.

**C3. Amenable quotients: E holds.** If `Q` is amenable, part 3 gives
`p^Q_(2->2)(N;G) = p_c(G)`. So `E(G,N)` is equivalent to `p_c(N;G) = p_c(G)`.
That converse direction was posted as ESTABLISHED on the live bus
(`fpbs-amenable-quotient-normal-relative-threshold-is-pc`, swarm-0917 w5,
not yet landed at the time of writing). Granting it, Claim E holds for all
amenable quotients. So Claim E is a real extension of a proved identity, not
a guess about a new regime.

**C4. Blindness to amenable extensions.** Let `N <= M` be infinite normal
subgroups with `M/N` amenable. By part 2 of the sandwich,
`p^(Gamma/N)_(2->2)(N;G) = p^(Gamma/M)_(2->2)(M;G)`. So `E(G,N)` and `E(G,M)`
together give `p_c(N;G) = p_c(M;G)`. Since `p_c(M;G) <= p_c(N;G)` always
holds, a pair with `p_c(M;G) < p_c(N;G)` refutes `E` at `N` or at `M`. This is
the cheapest test for a disproof.

**C5. Effect on the route.** In `fpbs-bs-via-percolation-kesten-split`,
premise (alpha) for a pair `(G,N)` satisfying `E'` is equivalent to
`||sigma^N_(p_c)||_Q < infinity` (by C1). This condition implies
`||T_(p_c)|| < infinity` on `G`, so on those graphs (alpha) is at least as hard
as the whole-graph critical l2 conjecture restricted to `G`, which already gives
`p_c < p_u` without the split. The split can therefore add something only on
graphs of type (ii) in C1, or through premise (beta).

## Evidence

1. **Amenable quotients (proved, given C3).** Claim E holds whenever `Q` is
   amenable.
2. **Free-group trees (computation sketch).** Take `F_d` on its standard basis,
   with `N` normal and `rho_Q > 2 sqrt(q)/(q+1)`, and use the notation of
   `fpbs-tree-normal-relative-threshold-is-inverse-cogrowth`.
   - The tree Green function identity is
     `sum_n s^n 1_(S_n) = phi(s) sum_k ((q+1) z(s))^k mu^(*k)`, pointwise on
     `F_d` for `s <= 1/sqrt q`. It holds because
     `G_T(x|w) = G_T(e|w) F(w)^|x|` with `F((q+1)z(s)) = s`.
   - Pushing this forward gives
     `sigma^N_p = phi(p) sum_k w^k mu_Q^(*k)` with `w = (q+1) z(p)`.
   - Its norm is `phi(p)/(1 - w rho_Q)` when `w rho_Q < 1`, since
     `||lambda_Q(mu_Q)|| = rho_Q` by Kesten, and it is infinite at
     `w rho_Q = 1`.
   - So `p^Q_(2->2)(N;T) = s_N = p_c(N;T)`, the latter from part 2 of that
     node.

   Not written as a full proof here.
3. **Products with an amenable factor (literature, amenable `N`).**
   Hutchcroft and Pan, arXiv:2412.15895, Theorem 1.2, prove
   `p_(2->2)(G) = p_u(G)` for `G = T x H` with `H` an amenable Cayley graph
   (and for `LL(T)`). For `Gamma = F_d x H` with the product generating set
   and `N = H`, C2 turns this into `E(G,N)`.
4. **Mean field.** Model slightly supercritical clusters as branching random
   walk with offspring kernel `m mu`, projected to `Q`.
   - The expected occupation of `e` is finite iff `m rho_Q <= 1`, with
     equality allowed when the walk is rho-transient.
   - The occupation convolution operator is bounded iff `m rho_Q < 1`.
   - Both thresholds sit at `m rho_Q = 1`, and at that point the occupation of
     `e` may stay finite while the operator is unbounded, exactly as in
     item 3 of the tree node.

## Attempts

**Where it can fail (independent failure modes).**

* **Heavy fibre profiles along a nonamenable `N`.** A type-(ii) graph needs a
  window `(p_c, p_c(N;G))` where `chi^N_p < infinity` but `chi^(N,m)_p` grows
  super-exponentially in `m`. For `m = 2` this is
  `sum_q sigma_p(q)^2 = infinity`, a fibre profile that is not square-summable
  over `Q`.
  - The unconditional bounds on the board do not exclude this. They give the
    first and second fibre moments at most those on `N` itself
    (`fpbs-normal-fibre-second-moment-maximal`), which bounds `sigma_p` in
    `l-infinity`, not in `l2(Q)`.
  - The natural test case is `F_2 x F_2`, taking `N` to be one factor.
* **p_(2->2) < p_u with an amenable normal subgroup.** By C2, any Cayley graph
  with an infinite amenable normal subgroup and `p_(2->2) < p_u` refutes E.
  None is known to me. The known equalities are item 3 above.
* **Amenable extensions.** By C4, `p_c(M;G) < p_c(N;G)` with `M/N` amenable
  refutes E. On free-group trees this cannot happen, since
  `rho_(Gamma/N) = rho_(Gamma/M)` by Kesten, and that is consistent with item 2.

**What does not prove it.**

* **Monotone upper bounds.** Upper bounds on `chi^N_p` alone do not help: on
  `Z^d` along `Z^k` with codimension at least 3, critical relative finiteness
  gives no gap (the board lemma of the calibration wave). So `m = 1` data
  cannot control `m >= 2`.
* **Russo-BK integration.** Integrating upward from a `p_0` where the fibre
  operator is bounded is part 5 of the sandwich. It preserves boundedness but
  cannot create it.

**Tree products with product generators (probability-random, 2026-09-17,
swarm-0917 w12).**

* `fpbs-tree-product-fibre-operator-is-half-tilted-susceptibility`
  (ESTABLISHED) covers `Gamma = Lambda x H_grp` with product generators,
  where `Cay(Lambda)` is the `k`-regular tree (`k >= 3`), `H_grp` is
  arbitrary and `N = H_grp`. It proves
  `||sigma^N_p||_Q = chi_(p,1/2)`, Hutchcroft's half-tilted susceptibility
  for the end-fixing group, so `p^Q_(2->2)(N;G) = p_t`. With Hutchcroft's
  `p_c < p_t` (`fpbs-hutchcroft-nonunimodular-pc-below-pt`), every such pair
  is of **type (i)**.
* **Test case settled.** `F_2 x F_2` along either factor (standard product
  generators) is type (i), not type (ii). `E'` holds on all these pairs, and
  none of them is an escape from C1.
* **Reduction of E there.** `E(G,N)` is equivalent to the fibre square-root
  law: `sum_n n (k-1)^(n/2) f_p(n) < infinity` for all `p < p_c(N;G)`, where
  `f_p(n)` is the mean cluster mass on one fibre at tree distance `n`. This
  holds for amenable `H_grp`, and is open for nonamenable `H_grp`:
  `fpbs-tree-product-fibre-square-root-law-below-relative-threshold`.
  A counterexample to E of this form needs nonamenable `H_grp` and a window
  `(p_t, p_c(N;G))`, strictly above `p_c`.
* **Where the HP transfer stops.** Hutchcroft--Pan's point-to-point Lemma 2.8
  uses Kesten's return bound for amenable `H`. The invariant is the gap
  between the point rate and the fibre rate. Details are in the open node.
* **Next test.** A type-(ii) pair, if one exists, must have a quotient whose
  Cayley graph is not a tree, or a generating set that is not a product. The
  open node's smallest case, `F_2 x F_2`, tests E only, not E'.
* **C4 via Schreier Folner cuts (2026-09-18, dead; swarm-0917-w13-w13-bs-break).**
  - *Idea.* Prove C4, `p_c(N;G) = p_c(M;G)` for `M/N` amenable, by running the
    trifurcation count of `fpbs-co-amenable-subgroup-relative-threshold-is-pc-proof`
    relative to `N` at a level `p in (p_c(M;G), p_c(N;G))`.
  - *What survives.* The established node
    `fpbs-relative-threshold-continuous-at-co-amenability` gives
    `p_c(N;G) <= min{ p_tri(h(Gamma/M)), p_u(M;G) }`. Here `p_tri(h)` is the
    infimum of the `p` with `delta(p) > p h`. It also proves that
    `h(Gamma/N) = h(Gamma/M)`. Together with part 2 of the sandwich, this gives
    a two-sided bound with both ends unchanged under amenable extension:

    ```text
    p^Q(M) <= p_c(M;G) <= p_c(N;G) <= min{ p_tri(h(Gamma/M)), p_u(M;G) } .
    ```

    So C4 holds whenever `p_c(M;G)` equals either end. A C4 counterexample
    must have:
    - `p_c(N;G) < p_u(M;G)`;
    - `delta(p) <= p h(Gamma/M)` for every `p in (p_c(G), p_c(N;G))`.
  - *Where it dies.* Step 4 of the trifurcation count needs an `N`-invariant
    cut with finitely many `N`-orbits and expected open boundary below
    `delta |W/N|`. The best ratio available is `p h(Gamma/N) = p h(Gamma/M)`,
    so Step 4 yields only `delta <= p h`. Cutting inside one `M`-coset along a
    Folner set of `M/N` pays `p |S \ M|` per vertex. Branches leaving `M`
    re-enter at far `N`-cosets, so Step 5 (sprinkling onto one coset) has
    nothing to act on. The invariant is `h(Gamma/M) > 0`. The method is as
    blind to amenable extensions as `p^Q` is, so it cannot decide C4.
* **Counterexample search on free products (2026-09-19, swarm-0917-w17-w17-bs-break,
  minimal-counterexample).** No counterexample exists there. E is proved on the
  class: `fpbs-free-product-commuting-quotients-satisfy-identity-e`
  (ESTABLISHED).
  - *Class.* `Gamma = A * H` with union generators, and any normal `N`
    containing `[A,H]`. This includes `Q = H` for an arbitrary nonamenable
    `H`, so the quotient need not be a tree, and it includes `Q = A x H`.
    The w12 "next test" (a non-tree quotient or a non-product generating set)
    is answered negatively on this class.
  - *Result.* Write `alpha` and `beta` for the pushforwards of `tau^A - delta`
    and `tau^H - delta`. Cut vertices of the block tree and commuting images
    give the renewal formula
    `sigma^N_p = (1+alpha)(1+beta) sum_k (alpha beta)^k`. From it,
    `p_c(N;G) = p^Q_(2->2)(N;G) = sup{p : ||alpha_p beta_p||_Q < 1}`, and the
    pair is of type (i) iff `Q` is nonamenable.
  - *Invariant.* The renewal structure: `sigma^N` is a resolvent of one
    symmetric kernel `f`, with prefactor at least `delta_e`.
  - *Step that forces E.* `sigma(e) < infinity` makes `f^(*2k)(e)` summable,
    so `||f||_Q <= 1` by the diagonal lemma. Thinning gives
    `f_p <= c f_(p')` with `c < 1`, so every smaller `p` is in the l2 regime.
  - *Consequence for a disproof.* A type-(ii) pair, or any failure of E, needs
    a fibre kernel that is not dominated by a resolvent with diagonal
    controlled by `sigma(e)`. That excludes gluing at single cut vertices over
    commuting images. The remaining free-product-like tests are:
    - amalgams `A *_C H` over infinite amenable normal `C`, which are also
      C2 tests;
    - normal subgroups of `A * H` not containing `[A,H]`, where the fibre sum
      is an alternating word sum in two non-commuting kernels.
* **Every normal subgroup of complete-block free products (2026-09-19,
  swarm-0917-w17-w17-bs-follow, operator-algebras).** This settles the second
  remaining test above for finite factors and lines. The result is
  `fpbs-complete-block-free-products-satisfy-identity-e` (ESTABLISHED; route
  `fpbs-complete-block-free-products-identity-e-proof`).
  - *Class.* `Gamma = A_1 * ... * A_m`. Each factor is either finite with
    generators `A_i \ {e}` (a `K_n` block) or `Z` with `+-1`. `N` is any
    infinite normal subgroup, with no commutation hypothesis. This includes
    `PSL_2(Z)` with `{s, r, r^2}` along every infinite quotient.
  - *Result.* On `Gamma`, `tau_p = c_p G_(mu_p)` for all `p < p_(2->2)(G)`.
    Here `mu_p` has explicit factor weights `w_i(p)`, and the local identity
    `(delta - mu_p) * tau_p = c_p delta` holds for every `p`. Pushing forward
    gives `sigma^N_p = c_p G_(pi_* mu_p)` on `Q`. Then Kesten plus Brouwer
    invariance of domain in weight space give
    `p_c(N;G) = p^Q_(2->2) = min{p : ||lambda_Q(pi_* mu_p)|| = 1}`.
    The pair is of type (i) iff `Q` is nonamenable and of type (iii) otherwise;
    type (ii) never occurs on this class.
  - *Invariant.* Green representability: `tau_p` is the Green function of a
    finite-range walk in a finite-parameter family `W(t)`, and `W` is injective.
  - *Where the method dies in general.* At Step 1 of the route, the local
    identity with finitely many free weights. It comes from the cut vertices
    of the block tree. On a graph with cycles through several blocks,
    `tau_p` is not the Green function of any finite-range walk, and the
    softer positivity and variational facts do not replace this.
    Theorem B of the new node states the abstract mechanism that any other
    class would need.
* **Harris chain domination of the multi-chain powers (2026-09-19,
  swarm-0917-w20-w20-bs-pull, probability-random; dead, obstruction
  recorded).**
  - *Idea.* Prove `E'` by bounding `sigma_p^(*m)(e)` exponentially in `m` at
    some `p >= p_c`, through Harris--FKG
    `prod tau <= P(all chain points in one cluster)`. The bound would use the
    finite fibre mass or relative sharpness in a gap window.
  - *Result.* `fpbs-harris-chain-majorant-is-superexponential`
    (ESTABLISHED) proves that the majorant
    `H_m(p) = E_p[|K_o|^(m-1)|K_o ∩ N|]` is infinite when `theta(p) > 0`, and
    that `H_m(p) >= (m p)^(m-1)` at every `p`, on every infinite transitive
    graph and for every `N` containing `o`. For `p < p_c` the true chain sum is
    at most `chi_p^m`. The same holds for any single-parameter count of tuples
    in one cluster, including superposition of the factors.
  - *Where it dies.* At the passage from `sigma^(*m)(e) <= E_(p')[Phi_m(K_o)]`
    to `C^m`, for every `p'`. The invariant is the ratio of ordered tuples in
    one cluster to chains of independent connections, which grows like
    `(m p/chi_p)^m`. It dies even on trees and below `p_c`, where the
    statement is trivial.
  - *Consequence.* BK and Reimer bound `sigma^(*m)(e)` only from below. So a
    proof of `E'` or of critical fibre l2 cannot come from correlation
    inequalities on events. It needs a product-preserving identity (renewal or
    resolvent) or a spectral cluster functional (the Gram bound of the w18
    bus lemma, which is not yet in this tree).

* **Nonunimodular calibration (2026-09-19, swarm-0917-w19-w19-bs-pull,
  calibration).** Result: `fpbs-nonunimodular-level-sets-break-identity-e`
  (ESTABLISHED).
  - *Setting.* A transitive nonunimodular `Gamma ⊆ Aut(G)` and
    `N_Delta = ker(gamma -> Delta(o, gamma o))`. This is normal, contains every
    stabilizer, has abelian quotient `D`, and its orbits are the infinite
    level sets of `Delta`.
  - *Result.* The fibre kernel satisfies `sigma(c^(-1)) = c sigma(c)`, so
    `||S_p||_(l2(D)) = chi_p`. The chain is
    `p^(l2) = p_T <= p_c < p_t <= p^(diag) <= p_c(L;G)` (Hutchcroft
    `thm:pcpt`). On `T_k` it is `1/(k-1) < 1/sqrt(k-1)` with no import.
  - *What fails off Cayley graphs.* C3 fails (abelian quotient, strict gap).
    E and E' fail: every such pair is literally type (ii). The sandwich
    diagonal formula fails on the whole window `(p_c, p_t)`.
  - *Invariant.* The modular function, seen as the defect of `sigma` under
    inversion.
  - *Step where every member dies.* Any proof of C3 or of E (l2 form) that
    does not use unimodular mass transport would prove a false statement on
    `(T_k, Aut(T_k)_xi, N_Delta)`. The recorded proofs use it at Step 5 of the
    C3 proof and at (0d) of the sandwich proof.
  - *Survivor.* `E_diag`: `p_c(N;G) = p^(diag)(N;G)`, the multi-chain
    formulation. It equals E on Cayley graphs and holds on `T_k`.
* **Every tree Cayley graph, every infinite normal N (2026-09-19,
  swarm-0917-w20-w20-bs-break, census-computation).** E holds on the whole
  class: `fpbs-tree-cayley-graphs-satisfy-identity-e` (ESTABLISHED).
  - *Class.* Every `(Gamma,S)` whose Cayley graph is the `(q+1)`-regular tree:
    `F_d` on a free basis, `(Z/2)^{*b}`, and the mixed products
    `Z^{*a} * (Z/2)^{*b}`. `N` is any infinite normal subgroup, in particular
    one not containing `[A,H]`. This is the w17 "next test" for factors `Z`
    and `Z/2`, and it turns item 2 of the Evidence into a proof.
  - *Result.* The pointwise identity `s^|x| = phi(s) G_(w(s))(e,x)` on the
    tree pushes forward to
    `sigma_p = phi(p) (1 - w(p) lambda_Q(mu_Q))^(-1) delta_e`, so
    `||sigma_p||_Q = phi(p)/(1 - w(p) rho_Q)` for `p < s_N`, and
    `p_c(N;T) = p^Q_(2->2)(N;T) = s_N`. The pair is type (i) iff `Q` is
    nonamenable, and type (iii) otherwise. No tree pair is type (ii).
  - *Census outcome.* No normal subgroup of a tree group escapes the
    resolvent form. The alternating word sums in two non-commuting kernels,
    which the renewal method of w17 could not handle, are resolvents here,
    because `tau_p` is already a Green function on `Gamma` before the
    quotient is taken.
  - *Invariant for a disproof.* Green representability of `tau_p` on `Gamma`
    by a single symmetric walk. Where it holds up to `p^Q_(2->2)`, every
    quotient inherits a resolvent, and E follows. So a type-(ii) pair must
    live on a graph whose two-point function in the window
    `(p_c, p_c(N;G))` is not a Green function of any one walk on `Gamma`.
    Among the tested classes this rules out trees, free products along
    commuting quotients (w17) and, per the w17 follow-up on the live bus,
    complete-block free products. What remains are one-ended graphs
    (`F_2 x F_2` along the diagonal-free normal subgroups, `T x H`) and
    amalgams over infinite amenable `C`.

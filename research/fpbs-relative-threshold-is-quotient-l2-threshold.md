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


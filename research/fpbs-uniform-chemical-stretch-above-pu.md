---
rg: 2
id: fpbs-uniform-chemical-stretch-above-pu
kind: claim
title: On every nonamenable Cayley graph with p_u < 1 one linear chemical stretch constant works at every parameter above p_u
distinct_from:
  fpbs-intrinsic-l2-rate-bounded-below-above-pu: that is the operator statement Lambda(p_u) > 0; this is a geometric sufficient condition for it, which can fail while it holds
  fpbs-benjamini-schramm-universal: this implies p_c < p_u through the intrinsic-rate chain, and is strictly stronger
---

**OPEN.**

Notation as in `fpbs-intrinsic-l2-rate-closed-zero-set`. A linear stretch
constant at `t` is a `K` with `inf_(u,v) P_t(d_omega(u,v) <= K(d(u,v)+1)) > 0`,
and `K_*(t)` is the infimum of such `K`.

**Claim (UCS).** Let `G` be a Cayley graph of a finitely generated nonamenable
group with `p_u(G) < 1`. Then `sup_(t > p_u) K_*(t) < infinity`.

`K_*` is nonincreasing (item 4 of the established claim). So (UCS) is
equivalent to `lim_(t↓p_u) K_*(t) < infinity`, and to the existence of one
`K` that is a stretch constant on some interval `(p_u, p_u+epsilon)`. The
positivity constant `c(t)` may depend on `t` and may tend to `0`.

**Prerequisites that can each fail.**

- **(S-fix)** `K_*(t) < infinity` for every `t in (p_u,1)`: linear chemical
  distance in the uniqueness phase at a fixed parameter. This is not in the
  graph for general nonamenable Cayley graphs, even for `t` near `1`.
- **(S-unif)** No blow-up at `p_u+`. On any graph where (S-fix) holds, (UCS)
  fails exactly when `K_*(t) -> infinity` as `t ↓ p_u`.

**Forced behaviour at `p_c`.** Item 6 of the established claim says
`K_*(t) >= log(gr)/(2 lambda_1(t)) -> infinity` as `t ↓ p_c`. So the
analogue of (UCS) at `p_c` is false on every nonamenable Cayley graph.

## Attempts

1. **Monotone reduction, and the class it kills (2026-09-17).** Since `K_*`
   is nonincreasing, (UCS) is equivalent to `K_*(p_u+) < infinity`.
   - **Sufficient condition:** uniqueness at `p_u` itself together with
     `K_*(p_u) < infinity`. *Where it dies:* it needs uniqueness at `p_u`.
     Nonuniqueness at `p_u` is reported for some nonamenable products (Peres,
     Ann. IHP 2000; recalled, not imported), and in a hypothetical
     counterexample `p_c = p_u` there is no infinite cluster at `p_u` at all.
   - **Invariant:** the right limit `lambda_1(q+)`. If `sup_(t>q) K_*(t) <= K`,
     then `lambda_1(q) >= log(gr)/(2K) > 0` by items 4, 1 and 5, hence
     `q > p_c`.
   - **Class killed:** arguments that give a stretch constant uniform on
     `(q, q+epsilon)` from hypotheses on `q` that `q = p_c` satisfies on
     *every* nonamenable Cayley graph. Examples: supercritical sharpness,
     insertion tolerance, Harris-FKG, the Hermon--Hutchcroft tail,
     `theta(t) >= K(t-q)`, and the ball laws at a fixed radius.
   - **Where every member dies:** at item 6 of
     `fpbs-intrinsic-l2-rate-closed-zero-set`. It proves
     `K_*(t) -> infinity` as `t ↓ p_c` on every graph, so such an argument
     would contradict an established theorem.
   - **What survives, and why it is not cheaper.** An argument that uses
     uniqueness on `(q,1]` escapes the kill, but it proves `q > p_c` as a
     by-product. So it is at least as strong as the flagship statement.
   - **Consequence:** a proof must feed in a quantitative feature of how the
     infinitely many infinite clusters present below `p_u` merge. That
     feature has no counterpart at a threshold equal to `p_c`.
2. **Sprinkling at `p_u` (2026-09-17, stalled).** Write
   `omega_(p_u+epsilon) = omega_(p_u) ∪ eta_epsilon`, with `eta_epsilon`
   independent Bernoulli of density about `epsilon`. Along a geodesic from `u`
   to `v`, a short open route has to cross between infinite `p_u`-clusters.
   Each crossing needs a sprinkled edge joining two such clusters within
   bounded distance of the geodesic.
   - **Plausible regime:** if infinite `p_u`-clusters come within distance `1`
     of each other at a positive density `rho` of places, the extrinsic merge
     scale is about `1/(rho epsilon)`. If the stretch inside `p_u`-clusters is
     linear, the detour per merge is comparable to the merge scale. Then `K`
     stays bounded as `epsilon -> 0`, because both lengths scale together.
   - **Where it stops.** Two inputs are missing, and neither is established
     here.
     - (i) A linear stretch estimate inside the infinite clusters at `p_u`,
       conditional on connection. This is harder than (S-fix), since
       `P_(p_u)(u <-> v) -> 0` as `d(u,v) -> infinity` under nonuniqueness.
     - (ii) A lower bound, uniform in `epsilon`, on the probability that a
       merge happens within the next `C/epsilon` steps of the geodesic, rather
       than far off to the side.
   - **No renormalization.** The Antal--Pisztora renormalization that gives
     linear chemical distance on `Z^d` uses good boxes in amenable geometry and
     does not transfer.
   - **Averaged form.** The averaged hypothesis recorded in
     `fpbs-intrinsic-l2-rate-via-uniform-stretch` removes the worst-case pairs
     but not (i) or (ii).

# Relative rank collapse: the folding model for relC(E_L ; E_K)

**Metadata.** September 18–19, 2026. Worker swarm-0917-w14-w14-fp-break,
belief-breaker role, family finite-models.

**Setting.** Let `L = F(a, b)` and `K = <a, c>` with `c = b a b^{-2}`. The
target node is `fpbs-mal-bernoulli-single-stage-floor`. The established part is
`fpbs-profinite-relcost-equals-relative-rank-gradient`.

## 1. The model

Let `Q` be a finite transitive `L`-set of size `n`. We build the labelled graph
`Γ_K` over `Q` and fold it.
- It has real vertices `Q`.
- There is an `a`-edge `p → p·a`.
- At every `p` there is a `c`-path
  `p -b-> x1 -a-> x2 -B-> x3 -B-> p·c`, with `B = b^{-1}`.

After folding, `Γ_K` is the Stallings graph of `Stab_K(q)`. When `K` is
transitive, it has exactly `n` real vertices and `2n` non-real vertices. This
was confirmed in every run, where `extras0 = 2n`.

**Chords.** A chord `(p, w)` of any length has the same effect as identifying
two vertices of the folded graph that lie over the same point of `Q`. One
case is a non-real vertex and a real vertex.

**The number d(Q).** `d(Q)` is the least number of identifications after which
the graph folds down to `n` vertices. By the node, `d(Q)/n` is the exact
relative cost on every essentially free profinite action at level `Q`. It is
also an upper bound on every action with factor `Q`, and
`d(Q) = rk(Stab_L(q) : Stab_K(q))`.

**Single chords.** A single chord either reads completely, giving one merge
`u ~ u'`, or leaves an arc of degree-2 vertices. An arc adds vertices and can
only lengthen later cascades. So `d(Q) = 1` iff a single pair merge collapses
everything. This can be tested exhaustively, and `checks.py` does so.

**Cascade structure (observation, not used in the proof).** Consider the
fibre product `Γ_K ×_Q Γ_K`.
- Malnormality of `K` makes every non-diagonal component a finite tree. Call
  these components *blocks*.
- One merge closes the whole block containing the merged pair.
- Each point of `Q` carries a 3-element fibre `{p, x, x'}`, and transitivity of
  identification inside it gives a 2-of-3 rule on pairs. This is the
  bootstrap rule of the w7 fold-bootstrap artifact.
- Blocks grow as merges accumulate. The late cascades seen in §2 are giant
  blocks forming.

## 2. Numerics (upper bounds on d only)

| experiment | n | d/n |
|---|---|---|
| random non-real-to-real merges (`fold.py`) | 500 | 0.148–0.158 |
| random non-real-to-real merges (`fold.py`) | 3000 | 0.151–0.160 |
| greedy best-of-80 merges (`greedy.py`) | 200 | 0.115–0.120 |
| greedy best-of-60 merges (`greedy.py`) | 600 | 0.108–0.110 |

The random-merge value matches the iid single-site threshold `5/32 = 0.156`.

**Greedy cascades.** Early gains are 3–7 vertices per merge. Late gains reach
111–489, as giant blocks close.

**Odometers.** Take `Q = Z/N` with `a: +1` and `b: +k`. The greedy search gives

| N | k | d |
|---|---|---|
| 30 | 0 | 1 |
| 30 | 1 | 1 |
| 30 | 7 | 5 |
| 101 | 5 | 5 |
| 400 | 13 | 13 |

So `d` stays bounded in `N`. This is consistent with relC = 0 on odometer
products. Odometer towers are not free, so the node does not apply to them.

**Single chords.** An exhaustive check found no single chord that works: 0/8
at `n = 8`, and 0/10 each at `n = 12, 20, 40, 80`. So `d ≥ 2` on every sampled
transitive `Q`.

**Outputs.** `checks_out.txt`, `greedy_out.txt` and `fold_out.txt`, in
`experiments/fpbs-relative-rank-collapse-2026-09-17/`.

## 3. Decomposition of `Q_0 > 0` (the D0 half of the floor)

The node gives `Q_0 ≥ lim d(Q_m)/|Q_m|` for every essentially free tower. So
`Q_0 > 0` follows from the prerequisite below, which may fail.

**(RR) A linear lower bound on the relative rank along one tower.** Find one
essentially free tower `(Q_m)` of finite transitive `L`-sets, with `K`
transitive, such that
`rk(Stab_L(q) : Stab_K(q)) ≥ c |Q_m|`.
Random lifts, congruence towers of `SL_2(F_p)`-type quotients, and `p`-towers
are all candidates.

**Where the standard lower bounds die.**
- **Euler characteristic.** Both stabilizers have rank `n + 1`, so the rank
  count gives `d ≥ 0`.
- **Untwisted mod-`p` homology.** One has
  `d ≥ dim_{F_p} coker( H_1(Stab_K; F_p) → H_1(Stab_L; F_p) )`.
  The w12/w13 lanes report on the live bus, not landed, that mod-`p`
  Fox-annihilator certificates of this kind are `o(n)`.
- **Finite quotients of `Stab_L(q)`.** These bound only the *profinite*
  relative rank. The number `d(Q)` is the abstract relative rank, which can be
  larger.
- **Chief factors (heuristic, not proved here).** The standard chief-factor
  bounds on generator numbers suggest that, in a finite quotient, the number
  of extra generators is linear only through abelian chief factors, and that
  non-abelian chief factors contribute `O(log)`. If so, a finite-quotient
  proof of (RR) must come from
  twisted mod-`p` homology `H_1(Stab_L(q); M)` relative to `Stab_K(q)`, for
  modules `M` of bounded dimension.
- **What is left.** Either twisted homology with a linear cokernel, or a
  genuinely abstract, non-profinite lower bound on relative rank.

**The refutation side predicts** `d(Q_m) = o(|Q_m|)` along *every* essentially
free tower. The greedy data at `n ≤ 600` shows no decay yet: 0.115 at
`n = 200` and 0.109 at `n = 600`. Each Q there is random, not a tower, and each
value is only an upper bound. A decreasing sequence of exact `d(Q_m)` along a
tower would be evidence for the refutation side, and exact values are
computable by merge search for small `n`.

## 4. What this settles and what it does not

**Settled.**
- `relC` on free profinite actions is an exact finite invariant, the relative
  rank gradient. This is the relative Abert–Nikolov theorem. With
  `K = 1`, the same argument gives `d(Q) = rk Stab_L(q) + n − 1 = rn` chords,
  so `d/n = r`, matching the cost of `F_r` and Abert–Nikolov.
- Bernoulli sits above every free profinite action.

**Not settled.** No lower bound on `d` is proved. D1, the depth product, is
untouched.

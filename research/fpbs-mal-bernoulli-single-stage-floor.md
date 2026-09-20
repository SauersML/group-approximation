---
rg: 2
id: fpbs-mal-bernoulli-single-stage-floor
kind: claim
title: The Bernoulli shift of Gamma_mal has positive relative cost over the orbit relation of one free stage
distinct_from:
  fpbs-locally-free-free-actions-have-finite-cost: that is the statement that every free action has finite cost; this is a single-stage lower bound for one action, and it refutes that claim.
  fpbs-malnormal-coset-cycles-linear-perimeter: that gives a positive floor for packing certificates only; this asks for a positive floor over all graphings.
  fpbs-mal-long-generator-packing-growth: that would imply the negation of this claim for the Bernoulli shift.
artifacts:
  - research/artifacts/fpbs-shifted-stage-relative-cost-zero-or-infinite-2026-09-17.md
  - research/artifacts/fpbs-deep-promotion-reduction-2026-09-18.md
  - research/artifacts/fpbs-promotion-cost-weak-containment-2026-09-18.md
  - research/artifacts/fpbs-mal-mapping-torus-2026-09-18.md
  - experiments/mal-mapping-torus-2026-09-17/twisted_double_coset.py
  - research/artifacts/fpbs-congruence-fold-census-2026-09-18.md
  - research/artifacts/fpbs-spectral-fold-seed-floor-2026-09-18.md
  - research/artifacts/fpbs-relative-rank-collapse-2026-09-18.md
  - research/artifacts/fpbs-iid-chord-union-bound-2026-09-19.md
  - research/fpbs-mal-pushout-fold-certificates-vanish-on-random-levels-proof.md
  - experiments/fpbs-depth-overfolding-2026-09-17/exact_search.py
  - experiments/fpbs-depth-overfolding-2026-09-17/check_surjective_n12.txt
  - research/artifacts/fpbs-mal-bernoulli-height-defect-2026-09-20.md
---

**OPEN.** Let `beta` be the Bernoulli shift of
`Gamma_mal = <a, b_1, b_2, ... | b_k = b_{k+1} a b_{k+1}^{-2}>`, and let
`H_1 = <a, b_1>`, which is free of rank 2. Prove that

```text
relC( E_beta ; E_{beta|H_1} ) > 0.
```

**Equivalent forms.** By [[fpbs-shifted-stage-relative-cost-zero-or-infinite]]
the following are equivalent:
- this claim;
- `C(beta) = infinity`;
- `relC(E_beta; E_{beta|H_n}) = infinity` for all `n`.

The negation is `C(beta) = 2`.

**If it holds.**
- `(E_{beta|H_n})_n` is an increasing sequence of cost-2 relations whose union
  has infinite cost. That answers Gaboriau's Q 2.66 positively.
- It answers the second part of Q 2.65, since
  `C - 1 = infinity > beta_1^(2)(Gamma_mal) = 1`.
- It refutes `fpbs-locally-free-free-actions-have-finite-cost`.
- By Tucker-Drob Cor 6.8(2), `E_beta` is not treeable.

**If it fails.** The Bernoulli shift of `Gamma_mal` has cost 2. Any graphing
certificate must use labels outside every fixed stage, with mass tending to 0.

**Known not to prove it.**
- No `l2` or first-Betti bound. All stages and the union have
  `beta_1^(2) = 1`.
- No packing floor. `fpbs-malnormal-coset-cycles-linear-perimeter` bounds
  only packing certificates.
- No zero-cost absorption argument. `fpbs-malnormal-measured-absorption-cap`
  shows that zero-cost absorption cannot leave a stage. That is compatible
  with relative cost 0, which is an infimum that is never attained.

## Attempts

**Homological and packing floors (September 17, 2026, swarm-0917-w5-pull-fp-2).**
- **Linnell ranks.** A relative `D`-rank floor for `(Gamma_mal, H_1)` would
  give a positive floor. It dies at the stage map
  `H_1(H_n, D) -> H_1(H_{n+1}, D)`. That map is an isomorphism, because the
  Fox derivative of `b_{n+1} a b_{n+1}^{-2}` in `b_{n+1}` is nonzero, hence
  invertible in `D`. So the relative invariant is `0`.
- **Packing certificates.** Their floor `delta_mal` bounds only the
  certificate, not `relC`.
- **What a proof would need.** Something that sees label length: the
  unbounded labels a small-mass generating graphing must carry.

**Sprinkle then absorb, attacked from the relC = 0 side (September 17–18,
2026, swarm-0917-w7-w7-fp-last1, host-geometry).**
- **Shape tested.** A cheap proof of the negation: pay a sparse block-factor
  sprinkle `Theta_B` of `b_2` over `E_{H_1}`, at mass `epsilon`, then absorb
  for free by infinite-contact steps. This is the one shape that
  `fpbs-malnormal-measured-absorption-cap` lists as not excluded.
- **Where it dies.** At the first absorption step. By
  [[fpbs-mal-sprinkle-then-absorb-inert]] (route
  `fpbs-mal-sprinkle-then-absorb-inert-proof`, artifact
  `research/artifacts/fpbs-mal-sprinkle-then-absorb-inert-2026-09-17.md`):
  - If `epsilon^{1/|W|^2} < 1/A`, the cluster graph of `E_{H_1} v Theta_B` is
    a.s. fine. This follows from `M(k) <= A^k` of
    [[fpbs-malnormal-coset-cycles-linear-perimeter]].
  - Hence every infinite-contact step with a bounded number of closed-edge
    crossings adds nothing.
  - Labels outside `H_2` are excluded by the cap's Theorem A.
  - If `epsilon^{1/|W|^2} <= 1/(4 A^2)`, the resulting relation misses
    `(x, b_2 x)` on mass `> 1/2`.
- **Invariant.** Almost-sure Bowditch fineness of the cluster graph.
- **What survives.**
  - kappa-escaping contact classes, where the crossing count tends to
    infinity along the class;
  - growing windows;
  - long-generator payments, with constants unbounded in `m`;
  - countably many payments;
  - certificates not built as chains.
- **Next decomposition that can fail.** Show that no `phi` has a non-null set
  of kappa-escaping infinite contact classes joining distinct clusters of a
  sparse block sprinkle. This does not decide the claim, which stays OPEN.

**Sofic sparsity floor for fold seeds (September 18, 2026,
swarm-0917-w8-w8-fp-break, finite-models).**
- **Result.** [[fpbs-weakly-bernoulli-fold-seeds-have-density-floor]]
  (route `fpbs-weakly-bernoulli-fold-seeds-have-density-floor-proof`,
  artifact
  `research/artifacts/fpbs-weakly-bernoulli-fold-seed-floor-2026-09-17.md`).
  For every action of `F(a, b)` weakly contained in Bernoulli, `σ_b ≥ 1/80`.
  So `σ_b(Bernoulli) ∈ [1/80, 5/32]`. The fold artifact had recorded that no
  positive lower bound was known for any free action.
- **Invariant.** Small-set slot sparsity of random Schreier graphs of `F_2`
  at the crossing size `α n`. With high probability, no `m`-set spans
  `(1+η) m` slots when `H(α) + 2αH((1+η)/2) + (1+η)α ln α < 0`. Every
  closure from `S` that crosses size `m` produces `2(m − |S|)` slots.
  Weak containment and the local structure of random permutation models carry
  this to all of `W_b`.
- **What it kills (with Theorem 1.2 of the fold artifact).** On `W_b`, every
  graphing with labels in one double coset `K b^{±1} K` has mass `≥ 1/80`
  at each stage `H_n ≤ H_{n+1}`, uniformly in `n`. So every stagewise
  telescoping scheme `E_{H_n} ∨ b_{n+1}|_{A_n} = E_{H_{n+1}}` has infinite
  total mass. This covers iid, block and factor-of-iid seeds. The odometer
  mechanism of `fpbs-mal-odometer-product-actions-have-cost-two` therefore
  cannot be transported to the Bernoulli shift, and `σ_b` separates the
  odometer products (`0`) from `W_b` (`≥ 1/80`).
- **What survives.**
  - graphings that mix several double cosets `K g K`;
  - labels from deeper stages `b_{n+2}, …`;
  - graphings that do not factor stagewise.
- **Next decomposition that can fail.** A finite-model reduction. Prove that
  the local relative combinatorial cost of random Schreier graphs of `L` over
  the `K`-components is bounded below uniformly in the witness length `T`.
  The cost is taken with extra edges of word length `≤ T`. Lemmas 1 to 3 of
  the artifact transfer any such bound to `W_b`. The missing count is the
  multi-coset analogue of slot sparsity. The claim stays OPEN.

**Chord unfolding: a `b`-length weighted floor for all double cosets
(September 18, 2026, swarm-0917-w9-w9-fp-break, reframing).** Artifact
`research/artifacts/fpbs-chord-unfolding-length-floor-2026-09-18.md`.
Scripts in `experiments/fpbs-chord-unfolding-2026-09-17/`.
- **Result.** [[fpbs-mal-graphing-b-length-weighted-floor]] is ESTABLISHED,
  from the w8 floor and [[fpbs-mal-fold-closure-exactness]] (which I
  re-verified and recorded as its own node). Let `Φ = ⊔ h|_{D_h}` be a
  graphing with `E_{H_1} ∨ Φ = E_{H_2}` on `β|H_2`, or on any free action
  weakly contained in Bernoulli. Then
  `Σ_h |h|_{H_1, b_2} μ(D_h) ≥ 1/80`, where `|h|` is the number of
  letters `b_2^{±1}` in a shortest expression in
  `H_1 b_2^{±1} H_1 ⋯ H_1`.
- **Invariant, and the step where members die.** Each chord unfolds into
  `|h|` translates of `D_h`, used as `b`-seeds. Fold exactness makes their
  union a seed set with conull 2-of-3 closure. Every graphing with bounded
  `b_2`-length `r` dies there, with mass `≥ 1/(80 r)`. This is uniform in:
  - the number of double cosets;
  - the `H_1`-letters;
  - the word length.

  Every stagewise scheme with `Σ 1/r_n = ∞` has infinite mass. This settles
  the survivor "graphings that mix several double cosets" whenever the
  `b`-length is bounded. It is stronger than the uniform-in-`T` count asked
  for above, because only `b`-letters modulo `H_1` on both sides are
  counted. At `r = 1`, `relC_{≤1} = σ_b` exactly.
- **Evidence.** Exact double-coset lengths are computed in
  `coset_b_length.py`: `b^2 = c^{-1} b a` has length 1, `bab` has length 2,
  `babab` has length 3. In iid chord experiments, labels of length 2 or 3
  do worse per unit mass than `b`.
- **What survives.**
  - Per stage, graphings with average `b_2`-length `≥ 1/(80 ε)` at mass `ε`
    whose unfolded seeds are heavily shared.
  - Non-stagewise graphings with deep labels.
- **Next decomposition, each part able to fail on its own** (artifact §5.5).
  - (P1) Geodesic bundling: `μ(A) ≤ C · mass(Φ)` for some choice of
    unfoldings. This would prove this claim with floor `1/(80 C)`.
  - (P2) Refutation form: a factor-of-iid chord graphing of mass `ε` with
    `b`-length about `1/ε` and shared seeds. By Theorem B this is the only
    possible shape of a single-stage counterexample.
  - (P3) Pushing deep-label graphings into stagewise form at a constant-factor
    loss.

  The claim stays OPEN.

**Quantifier shift: the floor is a uniform one-step deep-promotion floor
on `F_2` (September 18, 2026, swarm-0917-w9-w9-fp-follow,
quantifier-shift).** Artifact
`research/artifacts/fpbs-deep-promotion-reduction-2026-09-18.md`. Script
`experiments/fpbs-deep-promotion-2026-09-17/core_size.py`.
- **Result.** [[fpbs-mal-floor-iff-deep-promotion-floor]] is ESTABLISHED,
  through its route. Let `rho` be the Bernoulli shift of `L = F(a, b)`,
  `L_j = phi^j(L)` and `S_j = E_{rho|L_j}`. Let `Q_j` be the least cost of a
  graphing inside `E_rho` that promotes `S_{j+1}` to `S_j`. Then this claim
  holds iff `inf_j Q_j > 0`, with `Q_0 = r = relC(E_rho; S_1)` and `Q_j`
  nonincreasing.
  - The proof telescopes cheap promotions with the stage shift.
  - It truncates labels to a finite stage.
  - It transports `(H_m, H_2, H_1)` to `(L, L_{m-2}, L_{m-1})`.
- **What it changes.**
  - Chord §3(c) had only "claim implies `r > 0`". Now the claim is
    equivalent to a statement about one finitely generated group.
  - A refutation needs no infinite scheme. Cheap one-step promotions at
    growing depth suffice.
  - Survivor P3 becomes exactly `inf_j Q_j >= c r`. With
    `Q_{j+1} = (1 - eps_j) Q_j`, the claim is (D0) `r > 0` together with
    (D1) `prod (1 - eps_j) > 0`. Here `eps_j` is the saving from the single
    extra label level `L \ L_1`. The step from `Q_j` to `Q_{j+1}` uses `phi`,
    which carries the depth-`j` problem inside `L` onto the depth-`(j+1)`
    problem inside `L_1`.
- **Where the attack on (D1) died.**
  - *Coset-hull projection.* Replace each deep edge by one shallow chord per
    coset hull it crosses. The charge per deep edge is up to `|h|` times the
    Stallings core size of `L_j`, which grows like `(1 + sqrt 2)^j`:
    1, 3, 8, 20, 49, 119, 288, 696 (`core_size_out.txt`).
  - The replacement chords are path-dependent, so the resulting bound
    `Q_j >= r / M_j` decays.
  - Compact and character obstructions, and zero-cost splitting moves, give
    no leverage (artifact §5).
- **What survives.**
  - (D1) via a P1-type bundling inequality for crossings of deep edges.
  - The refutation shape: factor-of-iid promotions at depth `j -> infinity`.

  The claim stays OPEN.

**Weak containment: promotion costs are maximal at Bernoulli, so each
depth needs only some free witness (September 18, 2026,
swarm-0917-w10-w10-fp-last1, stability-approximation).** Artifact
`research/artifacts/fpbs-promotion-cost-weak-containment-2026-09-18.md`.
- **Result.** [[fpbs-mal-promotion-cost-monotone-under-weak-containment]] is
  ESTABLISHED, through its route.
  - *Theorem M.* Promotion cost `P(a; H', H)`, with labels anywhere in `Γ`
    and `H` finitely generated over `H'`, is antitone along `a ≼ b` for
    free `a`. The proof needs one conjugator, finitely many words, and a
    fix-up piece.
  - With Abért–Weiss, `Q_j(ρ) = max Q_j(c)` over free actions `c` of `F_2`,
    and `Q_j(c) <= Q_0(ρ)`.
  - So this claim holds iff there is `c > 0` such that each depth `j` has
    **some** free `F_2`-action `a_j` with `Q_j(a_j) >= c`. The `a_j` may be
    unrelated, profinite, and need not extend to `Gamma_mal`.
- **What it changes.** Every earlier lower-bound attempt used iid seeds or
  the Bernoulli weak class (w8 Theorem A, w9 Theorem B). Lower bounds may
  now use any free action. Only a refutation is tied to actions `≼ ρ`.
- **Profinite reduction** (artifact §3, Proposition F). For a free profinite
  tower `G_n = L/N_n`, `Q_j = lim_n Q_j^{(n)}`. Here `Q_j^{(n)}` is a
  finite-colouring covering problem on the tree of `L`: realise
  `t_j = phi^j(b)` over `L_{j+1}` at every point of `G_n`.
- **Where it stops.** No witness can beat `ρ`, so witnesses are proof
  devices only. No depth-`j` bound was proved for any action.
  - Rank counting at level `n` gives `e >= 0`, since
    `rk L_j = rk L_{j+1}`. So a profinite bound must use the fold
    structure. This is a heuristic, not a kill.
  - The sofic route needs a relative Carderi–Gaboriau–de la Salle identity,
    which is not in the graph.
- **What survives.** Hole (W): uniform per-depth witnesses, split as
  (W-prof) and (W-sof). (D1) via bundling is unchanged. The claim stays OPEN.
**Ascending HNN overgroup (September 18, 2026, swarm-0917-w10-w10-fp-break,
reframing).** Artifact `research/artifacts/fpbs-mal-mapping-torus-2026-09-18.md`,
script `experiments/mal-mapping-torus-2026-09-17/twisted_double_coset.py`.
- **Shape tested.** Decide the price of `Gamma_mal`, and so this claim through
  [[fpbs-mal-fixed-price-iff-bernoulli-finite-cost]], inside the mapping torus
  `G = <a, b, t | [a, t], t^{-1} b t = b a b^{-2}> = Gamma_mal ⋊ Z`. This
  group has two generators and one relator. It has `G^ab = Z^2`,
  `relC(R_G; R_{<a,b>}) = 0` in every free action, and infimal cost 1.
- **Lemma (proved).** `Z^2 = <a, t>` is malnormal in `G`.
  - An infinite intersection `g Z^2 g^{-1} ∩ Z^2` with `g ∉ Z^2` forces
    `phi^j(u) ∈ <a> u <a>` for some `u ∉ <a>` that begins and ends with
    `b^{±1}`.
  - But `|phi(u)|_b = |u|_b + 2s`, where `s` is the number of `b`-syllables.
  - The search finds no solution for `|u| ≤ 10` and `j ≤ 4`.
  - Consequently `G` has trivial centre.
- **Where it dies.**
  - *(K1) Chains stall.* The Gaboriau chain and wq-normal criteria started
    from `<a>`, `<t>` or `<a, t>` stop at `Z^2`.
  - *(K2) Twice-used letters are excluded.* The twice-used-letter theorem
    fails in every basis: the relator lies in the commutator subgroup, so it
    would have the form `s x^p s^{-1} x^{-p}`, and then `x^p` would be
    central.
  - *(K3) No transfer to this claim.* The price of `G` and this claim do not
    constrain each other. Going from the failure of the floor to price one for
    `G` needs a cost bound on every free `N`-action. That is the OPEN
    [[fpbs-normal-subgroup-bounded-cost-fixed-price-one]] with `K = 2`, since
    Gaboriau's normal-subgroup theorem gives only infimal cost.
- **Invariant.** The strict growth of `b`-length under `phi`, and the one-way
  character of cost transfer through normal subgroups.

The claim stays OPEN.
**Finite-piece bridges pay the length floor (September 18, 2026,
swarm-0917-w10-w10-fp-follow, minimal-counterexample).** Artifact
`research/artifacts/fpbs-finite-piece-bridges-length-floor-2026-09-18.md`.
- **Result.** [[fpbs-mal-finite-piece-bridges-pay-length-floor]] is
  ESTABLISHED, through its route. Let `E ⊆ R_L` be a bridge, meaning
  `R_K ∨ E = R_L`, whose pieces `E ∩ R_K` are finite. Suppose `E` is
  hyperfinite, or is treed by `G` with connected pieces. If `E` is generated
  by labels of `b`-length `≤ r`, then `relC(E; E ∩ R_K) ≥ σ_b/r ≥ 1/80r`.
- **Invariant, and the step where members die.** The invariant is the
  `b`-length of a generating graphing of `E`.
  - Projecting that graphing to a transversal of the pieces and running a
    nested Kruskal extraction gives a treeing of `E|_Y`. Its labels are
    `K`-double translates of the generators.
  - By Gaboriau's treeing theorem, its cost is at most `relC(E; E ∩ R_K)`.
  - Every such bridge dies at Theorem B, Step 3 (fold exactness).
- **What it kills.** The approximate-bridge route left open by
  [[fpbs-malnormal-cosets-admit-no-amenable-bridges]], namely amenable `E`
  whose trace on `R_K` has large finite classes.
  - Cayley-subgraph bridges (`a`, `c` and `b` edges) die outright, with
    value `≥ σ_b`.
  - The remaining approximate bridges produce witnesses of exactly the P2
    shape. So they are not an independent route to the negation of this
    claim.
- **What survives.**
  - P2 (long labels shared across seeds).
  - Non-hyperfinite bridges whose `E|_Y` has no treeing with short labels.
    Their cheap graphings are as uncontrolled as the target's witnesses.
  - Mixed traces.
  - P3 and D1 (deep labels).
**Profinite witnesses: exact finite-level fold density and a congruence
census (September 18, 2026, swarm-0917-w11-w11-fp-last1,
census-computation).** Artifact
`research/artifacts/fpbs-congruence-fold-census-2026-09-18.md`. Experiments
`experiments/fpbs-congruence-fold-census-2026-09-17/`.
- **Result.** [[fpbs-mal-profinite-fold-density-is-finite-percolation]] is
  ESTABLISHED, through its route.
  - For a profinite action `X = lim Q_n` of `L`,
    `sigma_b(X) = inf_n r(Q_n)/|Q_n|`, where `r` is the least 2-of-3
    percolating set of the finite triple hypergraph. No tree is needed, unlike
    Proposition F of w10.
  - `Q_j(X) <= sigma_b(X∘phi^j)` for every free `X`.
  - Every nonzero character tower and every regular dihedral tower
    (`a -> r`, `b -> s`) percolates with `O(1)` seeds, at every depth. So such
    witnesses have `Q_j = 0` for all `j`.
- **What it changes.**
  - The single-label part of W-prof is now a finite, computable invariant.
  - A class of floor witnesses is dead at every depth.
- **Census.** The upper bounds are certified by re-closing each seed set.
  - Sanov congruence towers, 3-, 5- and 7-adic and primes 5 to 29: plateau near
    .11, for example `sigma_b(3-adic) <= 1910/17496`.
  - Random Schreier graphs: .108 to .115.
  - Odometer and dihedral towers: `O(1/N)`.
  - Depths `j <= 8` at level 25: between .080 and .110, with no collapse
    (`census_depth2_out.txt`).
  - Mod `p`, the depth generators fall into the Borel subgroup for
    `p = 3, 5, 7, 11, 29, ...` (`borel_absorption_out.txt`). The density does
    not collapse there either (.096 to .167 on the levels computed).
- **Where it stops.**
  - The census gives only upper bounds on `sigma_b`, and `sigma_b` is itself
    only an upper bound for `Q_j`.
  - A lower bound on `Q_j(a_j)`, as w10 Corollary 2 needs, is untouched.
  - Surviving conjecture: `sigma_b(X) > 0` iff the profinite `X` is strongly
    ergodic.
**Chord-cell bootstrap: local absorption of long chords pays the seed floor
(September 18, 2026, swarm-0917-w12-w12-fp-last1, local-designs).** Script
`experiments/fpbs-chord-bootstrap-2026-09-17/bootstrap_injection.py`.
- **Result.** [[fpbs-mal-bootstrap-certified-chords-pay-seed-floor]]
  is ESTABLISHED through its route. Extend the 2-of-3 rule by one rule per
  chord instance: when all but one b-edge on its path is known, add the last
  one. Charge each such firing to its chord instance. Then the charged edges
  and the ignition seeds `A_0` have a plain 2-of-3 closure containing the
  whole bootstrap closure. So a conull bootstrap closure forces
  `μ(A_0) + mass(Φ) ≥ σ_b ≥ 1/80`. The bound is unweighted and uniform in
  label lengths, paths, sharing and number of labels.
- **Invariant, and the step where members die.** The injection from new
  b-edges to chord instances. Each instance fires at most once, at its first
  round with at most one unknown path edge. Every "sprinkle, then absorb long
  chords one at a time" refutation of this claim dies at that step, including
  heavily shared long chords (the shape of P2). This covers what the w7
  sprinkle-then-absorb kill left open for bounded-crossing steps, now for all
  lengths.
- **Obstruction to P1 through local closures.** The chord-cell closure is not
  exact. `Φ_0 = bab|_X ⊔ bbab|_X` generates (`bbab (bab)^{-1} = b`), both
  labels have b-length 2, and the bootstrap closure of `∅` is `∅`. So no
  finite-range bootstrap rule set can replace generation, as fold exactness
  does for b-seeds. P1 must bound circuits of several chords, where b-edges
  appear only as composites.
- **What survives.** A counterexample of mass `ε < σ_b` must have a
  non-conull bootstrap closure from every ignition set of measure
  `< σ_b − ε`. So it derives a non-null set of b-edges only through circuits
  of two or more chords, as in `Φ_0`. Next falsifiable step: a charging rule
  for
  two-chord circuits. Charge `h_2 h_1^{-1}` to the pair and bound how often
  one chord instance is reused across circuits.
**Full triples instead of slots: `σ_b ≥ 2/25` on `W_b` (September 18, 2026,
swarm-0917-w13-w13-fp-break, probability-random).** Artifact
`research/artifacts/fpbs-full-triple-fold-seed-floor-2026-09-17.md`.
Scripts in `experiments/fpbs-full-triple-floor-2026-09-17/`.
- **Result.** [[fpbs-bernoulli-fold-seeds-have-density-at-least-2-25]] is
  ESTABLISHED through its route. For every action of `F(a, b)` weakly
  contained in Bernoulli, `σ_b ≥ 2/25`. The optimum of the method is about
  `0.0819`. So `σ_b(Bernoulli) ∈ [2/25, 5/32]`, which replaces
  `[1/80, 5/32]`.
- **Invariant.** The number `F(I)` of full triples of an `n/2`-set in a
  random Schreier graph of `F_2`. An index `v` is a full triple of `I` when
  `v`, `σ_a v` and `σ_b v` all lie in `I`.
  - The sequential 2-of-3 closure from `S` passes through an `n/2`-set with
    `F(I) ≥ n/2 − |S|`, one firing index per step.
  - With high probability, no `n/2`-set has `21n/50` full triples. The
    first moment is `C(n,m) C(m,f)^3 / C(n,f)^2`, with exponent
    `J(1/2, 21/50) = −0.0079`.

  The w8 slot count splits each firing index into two independent slots and
  loses a factor of about 6.
- **Effect.** Every `1/80` in this cone improves to `2/25` by the same
  proofs:
  - the stage floor;
  - the single-double-coset `relC`;
  - the `b`-length-weighted floor, now `Σ |h| μ(D_h) ≥ 2/25`;
  - the finite-piece bridge floor and the bootstrap-certified chord floor,
    both on the live bus.

  Evidence: greedy contagious sets on random Schreier graphs with `n` up to
  `4·10^4` have density `≈ 0.116`, and `F(I)/n ≈ 0.385 < 0.42` at the
  crossing.
- **Where the method dies.** The sharp first moment of the same statistic
  caps at `≈ 0.0822`. The count sees only one double coset: a chord of
  `b`-length `r` unfolds into `r` seeds, and the count is blind to how those
  seeds are shared. So it says nothing about P2 (long, shared chords) or D1.
  This is a sharpening of the single-coset obstruction, not a decision.
**Spectral fold-seed floor; chord isoperimetry is what remains (September
18, 2026, swarm-0917-w13-w13-fp-last1, host-geometry).** Artifact
`research/artifacts/fpbs-spectral-fold-seed-floor-2026-09-18.md`. Scripts in
`experiments/fpbs-z3-overgroup-2026-09-17/`.
- **Result.** [[fpbs-strongly-ergodic-actions-have-fold-seed-floor]] is
  ESTABLISHED. For every non-atomic p.m.p. action of `L`,
  `sigma_b ≥ inf_{μ(I)=1/2} μ(I \ (a^{-1}I ∩ b^{-1}I)) ≥ (1 − rho_X)/4`.
  - Stop the closure rounds at measure 1/2. Each derived point uses up its own
    triple inside the crossing set, injectively, so the seeds pay for its
    `a,b`-boundary.
  - The Markov gap bounds that boundary from below.
  - On the Bernoulli class this gives `(2 − √3)/8 ≈ 0.0335` at every depth
    `X ∘ φ^j`, against the w8 constant `1/80`.
  - Every strongly ergodic action has `sigma_b > 0`, which is the open half of
    the w11 conjecture.
  - Through Theorem B, `relC_{≤ r} ≥ (2 − √3)/(8r)`.
- **Where it stops for this claim (artifact §4.4).** Lemma 1.1 needs a witness
  for each derived point *inside* the crossing set, with no witness shared.
  - A chord graphing derives `w ~ bw` through circuits of unbounded length.
  - Adding chord mass `δ` can raise the derived mass by more than any multiple
    of `δ` (the w12 example `bab ⊔ bbab`), so no such crossing set exists in
    general.
  - Theorem B's unfolding pays `|h|_{K,b}` seeds per chord to get around this,
    and that factor is the whole loss.
- **New decomposition.** On spectral-gap actions, the claim (D0, `r > 0`)
  follows from a *chord isoperimetry*. For a generating `Φ`, build a derivation
  in which each chord, counted once, is the unique witness for the points it
  derives, and stop it at a crossing set `I` with `μ(I) ∈ [1/3, 2/3]`. Then
  `μ(Φ) ≥ C^{-1} μ(I \ (a^{-1}I ∩ b^{-1}I)) ≥ (2/9)(1 − rho)/C`. The
  isoperimetry can fail on its own, and a failure would have to exhibit
  circuits whose derived mass per unit of chord mass is unbounded.
- **Dead (artifact §4.5).** Z/3 * Z/3 overgroup normalizer.
  `search_alpha.py` found no conjugate of the triangle rotation, over
  conjugators with at most 5 Nielsen moves, mapping `K` to a conjugate of `K`.
### swarm-0917-w13 (fp-follow): mod-p homological certificates for (D0) are Fox annihilators

- **Result.** New node
  `fpbs-mal-modp-promotion-certificates-are-fox-annihilators`, ESTABLISHED,
  with proof in `...-proof.md`. It gives three things.
  - An exact finite-level identity. For every field `F`, the `H_1(-;F)` lower
    bound on extra generating edges for `R_K v Phi = R_L` on a level `V` is
    `k_u(V) = dim {y : y u = 0}`, with `u = 1 - c - cb = dc/db`. This is
    checked by brute force on 900 pairs with 0 mismatches.
  - The witness floor `Q_0(X) >= limsup k_u(V_m)/|V_m|`.
  - Vanishing in characteristic `p` on `p`-towers, since `u` has
    augmentation `-1`.
- **Where the class dies.**
  - Any proof of (D0) by mod-`p` or rational first homology of the finite
    levels of a profinite witness equals the Sylvester rank deficit of `u`.
  - A positive such bound contradicts Jaikin-Zapirain's Conjecture 2.4 (1)–(2),
    which is open for non-amenable groups, over `F_p` for `F_2` at
    `u = 1 - x - y`.
  - Characteristic 0 is dead unconditionally (Linnell).
  - The census has random Schreier levels up to `n = 6400`, `SL_2(Z/3^k)`, and
    `PSL_2(F_q)` for `q <= 23`. No nested tower has `k_u/n` bounded away
    from 0.
- **What survives.**
  - Non-abelian certificates `d(N_m / <<K ∩ N_m>>^L)`.
  - (D1) deep-label arguments.

  The claim stays OPEN.
**Relative rank gradient: an exact finite form of (D0) (September 19, 2026,
swarm-0917-w14-w14-fp-break, finite-models).** New node
[[fpbs-profinite-relcost-equals-relative-rank-gradient]], ESTABLISHED.
Artifact `research/artifacts/fpbs-relative-rank-collapse-2026-09-18.md`.
Scripts in `experiments/fpbs-relative-rank-collapse-2026-09-17/`.
- **What was proved.** Fold the coset graph of `K = <a, bab^{-2}>` over a
  finite `L`-set `Q`. A chord of any length is then one vertex identification.
  - A set of chords generates `E_L` over `E_K` on a free cover iff the fold has
    `|Q|` vertices.
  - Hence `d(Q) = rk(Stab_L(q) : Stab_K(q))`, and both groups have rank
    `|Q| + 1`.
  - On free profinite actions, `relC = lim d(Q_m)/|Q_m|`. This is the relative
    Abert–Nikolov theorem.
  - With Abert–Weiss and weak-containment transfer,
    `Q_0 ≥ lim d(Q_m)/|Q_m|` for every free tower.
- **Consequence.** (D0) now follows from one finite-combinatorial input:
  relative rank linear in `|Q_m|` along a single free tower. Conversely,
  `fpbs-relative-fixed-price-free-pairs` forces `d(Q_m) = o(|Q_m|)` on every
  free tower.
- **Where the lower bound dies.** The rank count gives `0`, since both ranks
  are `n + 1`. Untwisted mod-`p` cokernels are small. Finite quotients bound
  only the profinite relative rank.
- **Numerics (upper bounds only).**
  - Greedy merges give `d/n ≈ 0.109–0.12` at `n ≤ 600`.
  - Random merges give `≈ 5/32`.
  - Odometers stay bounded.
  - No single chord ever suffices.
- **Status.** (D1) is untouched, and the claim stays OPEN.
**Independent chords of P2: union bound plus a uniform chain count
(September 19, 2026, swarm-0917-w14-w14-fp-last1, probability-random).**
Artifact `research/artifacts/fpbs-iid-chord-union-bound-2026-09-19.md`.
Scripts are in `experiments/fpbs-iid-chord-union-bound-2026-09-17/`.
- **Target.** Survivor P2, restricted to independent seeds. This is
  [[fpbs-mal-iid-chord-graphings-floor]]: `Theta(epsilon, p)`, where each
  point is active with probability `epsilon` and draws an arbitrary label
  `h ~ p`. The claim asks for a floor uniform in `p`, including heavy-tailed
  `b`-length, where the length-weighted floor `1/(80 m)` is empty.
- **Proved (Lemma 1, union bound).**
  `P[x ~ bx] <= sum_n epsilon^n sum_{D_1..D_n} prod q(D_i) N_n(D)`. Here
  `N_n` counts vertex-simple chains of classes from `K` to `Kb` with the
  prescribed relative positions. The proof splits each double coset into
  the disjoint sets `K g k^{-1}` (malnormality) and uses that distinct
  sources in a simple chain are independent. So `N_n <= rho^n` gives
  `epsilon_0 = 1/(6 rho)`, uniformly in `p`.
- **ESTABLISHED (Lemma 2).**
  [[fpbs-mal-two-step-relative-position-rigidity]]: for all classes `A`, `B`
  and double cosets `D`, `D'`, at most 12 classes `C` satisfy
  `D(A,C) = D` and `D(C,B) = D'`. The count is 9 exceptional plus 3 generic,
  obtained from projections of size at most 3 between hull translates and
  free stabilizer actions. It is uniform in the label length.
- **Open hole.** [[fpbs-mal-simple-chain-count-uniform]]:
  `N_n <= rho^n` uniformly. Route
  `fpbs-mal-iid-chord-graphings-floor-union-route` requires only that.
- **Evidence.** `N_3 <= 3` and `N_4 <= 5` in all scans. These cover short
  labels, random, folding and periodic labels up to length 16, and buried
  `K`-syllables of length 1 and 2. Walk counts, by contrast, blow up
  (1803 non-backtracking walks against 5 simple paths), so vertex-simplicity
  is essential.
- **Where it could fail.** Bridges that run along a third hull of the chain
  give about `|h|` attachment offsets. Iterating the projection argument
  then gives only a polynomial count `C^n prod (1 + |h_i|)^{O(1)}`, which is
  a moment condition, not a uniform floor. A family with `N_3` growing in
  `|h_2|` would kill this route but not the claim.
- **Scope.** Shared-seed factor-of-iid chords (the rest of P2) are not
  covered, because Lemma 1 needs independence of distinct points.
### swarm-0917-w14 (fp-follow): route to the counterexample node, and the D1 excursion retraction dies

- **Wiring.** New route `fpbs-mal-floor-gives-fixed-price-counterexample`
  targets `fpbs-fixed-price-counterexample-exists`. It requires this claim,
  `fpbs-mal-fixed-price-iff-bernoulli-finite-cost` and
  `fpbs-mal-odometer-product-actions-have-cost-two`. Both of those are
  ESTABLISHED. So this claim is now the only open premise of a complete route
  to the flagship's negation. Before this, no route connected them.
- **Setup for D1.** Write `M = L_j`. `M` is malnormal in `L`, because
  `φ^j(K)` is malnormal in `φ^j(L)` and malnormality is transitive. Let
  `S = S_{j+1}` be the orbit relation of `L_{j+1}`.
  - **Chain identity (remark).** `Q_j` with labels restricted to `L_i` equals
    `Q_{j-i}`. Transport along `φ^i`, and use Theorem M: restricted Bernoulli
    shifts are weakly equivalent to Bernoulli.
  - **Uniform statement (U).** There is `c > 0`, independent of `j`, with
    promotion cost using `L`-labels `>= c ×` promotion cost using `M`-labels.
    (U) together with D0 gives D1.
- **Attempt.** Retract an arbitrary `L`-labelled promoting graphing `Φ` onto
  `M`-labels.
  - Split `Φ = Φ_in ∪ Φ_out`. `Φ_in` has labels in `M`. The edges of
    `Φ_out` leave the `M`-orbit `Mx`.
  - Each excursion component of `S ∨ Φ_out` outside `Mx` returns to `Mx`.
    Each composite chord through it gives an edge of `E_M`. Let `T` be the
    relation these chords generate. Then `S ∨ Φ_in ∨ T ⊇ E_M`.
  - **Finite-contact lemma (proved).** An outside `S`-class `L_{j+1}·y` has
    at most one attachment point to `Mx` for each label `w ∉ M`. Proof: if
    `k g = w m` and `k' g = w m'` with `k, k' ∈ L_{j+1}`, then
    `k k'^{-1} ∈ M ∩ wMw^{-1} = 1`.
  - The hope was to charge `T` to the outside edges: each outside class would
    contribute at most `|labels|` chords.
- **Where it dies.**
  - A single excursion component can chain infinitely many outside
    `S`-classes through `Φ_out`. The finite-contact lemma bounds contacts per
    class and per label, not per component. So the attachment set `A(C)` of
    a component can be infinite.
  - Then `T` restricted to the attachment domain `D` is an infinite
    sub-relation of `E_M|_D`. Generating it can cost as much as
    `C(E_M|_D)`, which is about `1` by Gaboriau's induction formula.
  - Bounding that cost from below by `Φ_out`'s measure is (U) again. The
    retraction is circular with D0/(U), so this class dies here.
- **What survives.**
  - Retractions that control the number of outside classes per excursion
    component. A finite component bound would close (U) with
    `c = 1/(labels × bound)`.
  - Arguments that avoid retraction entirely, such as a profinite or
    relative-rank D1 statement along `fpbs-profinite-relcost-equals-relative-rank-gradient`.

  The claim stays OPEN.
### swarm-0917-w15 (fp-pull): (D0) is proved; word chords never beat vertex merges, and the Sanov 3-adic tower is the witness

- **Result 1.** [[fpbs-word-chords-are-dominated-by-merges]] is ESTABLISHED
  through its route.
  - Take a finite folded graph `Γ`, attach `k` arcs with any labels, and
    fold. The identification induced on `V(Γ)` is the fold-closure of at most
    `k − (E_Δ − V_Δ) ≤ k` pairs.
  - The proof is a potential `|P| + E_Δ − V_Δ`, which no fold increases.
  - The fold `Γ_Q^K` of the `K`-coset graph over a finite `Q` has three
    vertices over each point. Its merges are exactly 2-of-3 seeds.
  - So the least number of chords with arbitrary labels is `d(Q) = r(Q)`.
    `rho_vs_r.py` checks the merge half, `ρ = r`, on 48 of 48 random levels.
- **Result 2.** [[fpbs-profinite-relcost-equals-fold-seed-density]] is
  ESTABLISHED through its route.
  - For every essentially free profinite `X`, `relC(X) = σ_b(X)`. The route
    re-derives the chord folding criterion and the clopen approximation
    inline.
  - The Sanov 3-adic action of `L` on `SL_2(Z_3)` is free, has transitive
    levels, and is an expander tower (Selberg `(τ)`, Bourgain–Gamburd). So
    Theorem S gives `σ_b > 0` for it.
  - Abért–Weiss and Theorem M then give `Q_0 = relC(ρ) ≥ relC(Sanov_3) > 0`.
    This is (D0).
  - It refutes `fpbs-relative-fixed-price-free-pairs`, and the free-pair case
    of `fpbs-relative-fixed-price-fg-pairs`. Those nodes are left for their
    owners to update.
- **Invariant.** The fold potential `|P| + E_Δ − V_Δ`. Every chord, of any
  length and in any circuit, is charged to at most one vertex merge. This is
  global, so the local bootstrap obstruction `bab ⊔ bbab` of w12 does not
  apply.
- **Where this claim still stops: (D1).** At depth `j ≥ 1`, `Q_j` allows
  labels anywhere in `L`. The same potential gives the normal form
  `H = Γ_j / cl(m pairs)` plus a Δ-part of excess at most `k − m`. The
  target `t_j`-readings may pass through the Δ-part, and a single bridge can
  serve many base points. So `k ≥ m` no longer bounds a depth-`j` seed number.
- **Next step that can fail.** A rerouting inequality: move the
  `t_j`-readings through the Δ-part into `Γ_j / cl(P')` with
  `|P'| ≤ C(m + excess)`, where `C` does not depend on `j`.

  The claim stays OPEN, with (D0) settled and (D1) open.
**Non-abelian certificates: the pushout quotient is a triangle group, and on
random levels it is invisible to all finite quotients (September 19, 2026,
swarm-0917-w15-w15-fp-last1, group-rings).** Route
`research/fpbs-mal-pushout-fold-certificates-vanish-on-random-levels-proof.md`.
Scripts in `experiments/fpbs-pushout-fold-group-2026-09-17/`.
- **Result.** [[fpbs-mal-pushout-fold-certificates-vanish-on-random-levels]]
  is ESTABLISHED through its route.
  - *Theorem A.* If `K` is transitive on a level `V`, then
    `N / <<K ∩ N>>^N = P_V = <t_v | t_v = t_{vc} t_{vcb}>`. This is a
    one-vertex complex with `n` triangles, where each edge lies on 3
    triangles. Its relator is the 2-of-3 fold rule. The abelianization is the
    Fox element `u` of w13.
  - *Theorem B.* Every generating graph with `E` extra edges has
    `E >= log_|S| |Hom(P_V, S)|`, for every finite group `S`. So
    `Q_0(X) >= limsup log_|S| Z_S(V_m)/|V_m|` on free profinite witnesses.
    Taking `S = F_p` recovers `k_u`.
  - *Theorem C.* On uniformly random levels,
    `E |Hom(P_V, S)| <= (n+1)^(|S|^2 + 2|S|)`, by type counting and
    subadditivity of entropy. So each such certificate is `O(log n)` with
    probability `1 - 1/(n+1)`. This includes `S = F_p`, unconditionally.
- **What it kills.** The w13 survivor "non-abelian certificates
  `d(N_m / <<K ∩ N_m>>)`" is now `d(P_V)`. On random levels, which are the
  sofic models of `W_b`, every finite-quotient counting lower bound on it
  vanishes. A W-sof proof of D0 cannot go through normal generation that
  finite quotients of bounded size detect.
- **It is not vacuous.**
  - `P_V` is nontrivial, and sometimes infinite: `b_1 = 1` at `n = 12`.
  - When `H_1` is finite, `|H_1| = e^{theta n}` with `theta` in
    `[0.04, 0.26]`.
  - On an `A_4` Cayley level, `P_V` is perfect and maps onto `A_5`.
- **What survives.**
  - Counting certificates on structured (Cayley) towers, where `Z_S` grows:
    `Z_{C_2} = 2^13` on `PSL_2(7)`. This is a non-abelian Lück-approximation
    question.
  - The gap `d(N | K ∩ N) - d(P_V)` between relative rank and quotient rank.
  - `d(P_V)` detected by quotients of order `e^{Omega(n)}`, which Theorem C
    does not reach.
  - D1.
### swarm-0917-w15 (fp-follow): the Δ-part obstruction to (D1) is removed; (D1) is now two finite statements

- **Result (ESTABLISHED).**
  [[fpbs-mal-depth-promotion-equals-overfold-merge-number]] is proved
  through its route.
  - The folded `L_{j+1}`-graph `Γ_{j+1}(Q)` maps **onto** the folded
    `L_j`-graph `Γ_j(Q)`. The proof uses the fact that reduced `t_j` is a
    prefix of reduced `t_{j+1}`.
  - Hence any morphism `Γ_j(Q) → F(Φ)` fixing the reals factors as
    `g = f∘m` through the canonical map of `Γ_{j+1}(Q)`, by uniqueness of
    morphisms into folded graphs.
  - So the `t_j`-readings never enter the Δ-part. This answers the w15
    fp-pull stopping point.
  - The domination lemma then gives the exact count
    `d_j(Q) = deep_j(Q)`. This is the least number of same-fibre merges of
    `Γ_{j+1}(Q)` whose fold-closure contains `ker(Γ_{j+1} → Γ_j)`.
    Overfold merges, which lie outside the kernel, are allowed.
  - With `L_j`-labels the count is `law_j(Q) = r(Q^{(j)})`, where `Q^{(j)}`
    is `Q` twisted by `φ^j`.
  - The w15 clopen approximation runs with `t_j` in place of `b`. It gives
    `Q_j(X) = inf_m deep_j(Q_m)/|Q_m|` on every essentially free profinite
    `X` with transitive levels.
- **New decomposition.** Route
  `fpbs-mal-depth-floor-from-overfold-domination` targets this claim. Its
  two open premises can each fail:
  - (O) [[fpbs-mal-overfold-merges-never-help]]: `deep_j = law_j`, or
    just `deep_j ≥ c_1 law_j`;
  - (W) [[fpbs-mal-twisted-level-seed-density-uniform-witness]]: for some
    towers, `r(Q_m^{(j)})/|Q_m| ≥ c`, uniformly in `j`.

  (O) is the profinite form of (U) from the w14 D1 setup, with `c = 1`.
- **Evidence for (O).**
  - Exact search gives `deep_j = law_j` on 70 of 70 random levels
    (`j = 1, 2`; `|Γ_{j+1}| ≤ 100`).
  - Single-swap exchange at `j = 1` shows 0 failures in 288 tests. At
    `j = 2`, single swaps fail on some minimal non-minimum sets, so a proof
    must be global.
  - Greedy search over all 11, 87 and 559 overfold types never beat
    `law_j` at `j = 1, 2, 3`.
- **Evidence for (W).** Greedy `r(Q^{(j)})/n` on random `n = 120` levels
  stays at `0.117–0.125` for `j = 0..4`. These are upper bounds only.
- **Where it stops.** (O) has no proof. A generating-set analogue fails
  for general subgroup pairs, so a proof must use the rank-2 chain. (W)
  needs a spectral gap or seed density for `<a, t_j>` that is uniform in
  `j`. M. Hall induction loses the factor `[L : H_j]`.

  The claim stays OPEN.

**2026-09-20, swarm-0917-w22-w22-fp-break (belief breaker,
operator-algebras): OPEN; the approximate-odometer class of refutations is
killed.** Artifact:
`research/artifacts/fpbs-mal-bernoulli-height-defect-2026-09-20.md`.

- **Target of the attack.** The only known cheap free actions of
  `Gamma_mal` are the odometer products
  ([[fpbs-mal-odometer-product-actions-have-cost-two]]). Their seed set
  `{z mod N in {0,1,2}}` costs `3/N` and is built on an exactly
  `chi`-equivariant height. So a natural refutation of this floor is to
  build near-equivariant heights mod `N` inside `beta`. Then seed on them
  and control the 2-of-3 closure errors by the defect.
- **Result (ESTABLISHED,
  [[fpbs-mal-bernoulli-heights-have-uniform-defect]]).** Take any stage `n`,
  any countable `H_n`-set `Y` on which `a` or `b_n` has no fixed point, and
  any Borel `f : X -> Y`. Then
  `d_a(f) + d_{b_n}(f) >= (2 - sqrt 3)/(4 - sqrt 3) = 0.118`.
  In general the bound is `(2 - sqrt 3)(1 - sum p_y^2)`.
  - *Proof.* The graph vector `1[f(x) = y]` in `L^2(X) ⊗ l^2(Y)` has mass
    `1 - sum p_y^2` off `l^2(Y)`. That part is a multiple of
    `lambda_{F_2}`, by freeness of stages on the Bernoulli tensor basis and
    Fell absorption. Kesten's gap `4 - 2 sqrt 3` applies to it, and a
    concentration bound handles `p* > 1/2`.
- **Where the class dies.** At step 1, the existence of the height. The
  defect of any such height is at least `0.118`, uniformly in `N`, `n` and
  `Y`. The transport needs defect `o(1/N)`.
  - **Invariant:** the Kesten gap of the Koopman representation of a stage,
    twisted by `l^2(Y)`.
  - The qualitative exclusion of compact factors in item 5 of
    [[fpbs-mal-fixed-price-iff-bernoulli-finite-cost]] would still allow
    defects `eps_0(N) -> 0`. The uniformity is what kills the class.
  - It also covers congruence, dihedral, `Z`- and `Z^`-valued heights.
- **Not killed.**
  - Seed sets that are not functions of a height, including long-generator
    corrections of a height's defect region.
  - The lower-bound route through (O) and (W), which uses finite witnesses
    legitimately.
  - For a single generator the bound fails, by Rokhlin for `<a> ≅ Z`. So
    the obstruction really uses the non-amenability of each stage.
- **Remark (not established).** Weak-containment witnesses for
  `C(beta) < infinity` must be tempered. Tempered Gaussian actions
  `G(pi)`, with `pi ≼ lambda`, should all have cost `C(beta)`.
### swarm-0917-w22 (fp-pull, cohomology-index): the two sibling boundary kernels of the overgroup have finite cost

- **Result (ESTABLISHED).** `fpbs-mal-overgroup-is-free-by-cyclic`: the
  overgroup `M` is `F(u,v,w) ⋊_Θ <b>`, with
  `Θ: u ↦ v, v ↦ w, w ↦ v u^-1 v^2 w^-1`. Here `Gamma_mal = K ⋊ <b>` over
  `K = [M, M] ≅ F_∞`. The Alexander polygon is the triangle
  `(0,0), (2,0), (0,1)`, and the non-fibred lines are `(0,1)`, `(1,0)` and
  `(1,2)`, which is cited.
- **Result (ESTABLISHED).** `fpbs-mal-sibling-bns-kernels-have-finite-cost`:
  the other two boundary kernels `N_1 = ker (1,0)` and `N_2 = ker (1,2)` are
  increasing unions of 3-generated stages. Each step adds one generator that
  commensurates the stage, so the stage relative cost is `0` and the cost is
  at most `3` on every free action.
- **What dies.** Any floor proof that uses only:
  - the free-by-cyclic or BNS position of `Gamma_mal`;
  - Alexander or fibre-rank numerics;
  - the "`R_K` ∨ one normalising map" structure.

  All of these are shared by `N_1` and `N_2`, where the floor analogue is
  false.
- **Where it stops.** The only separating feature found is malnormality of
  `H_n < H_{n+1}`, which forbids the commensurated step. No floor is
  proved.

  The claim stays OPEN.

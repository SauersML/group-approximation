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

  The claim stays OPEN.

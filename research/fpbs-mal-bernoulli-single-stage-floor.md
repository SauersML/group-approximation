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

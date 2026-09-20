---
rg: 2
id: thompson-f-near-eigenvectors-carry-a-root-local-moore-tower
kind: claim
title: Near-eigenvectors of Thompson's F on pointed forests see a tower at the pointer - off mass 24 K^(n+2) sqrt(eta), the pointer tree or the tree 15 places to its right has at least 2 exp_(n+4)(0) leaves, so tower height grows like log(1/eta) in a window of two trees
distinct_from:
  thompson-f-near-eigenvectors-need-doubly-exponential-tree-sizes: that proves, by level-1 merge tests with explicit constants, a doubly exponential tree exp(exp(c eta^(-1/4))) somewhere within distance O(eta^(-1/4)) of the pointer; this proves a tower of height about log(1/eta) at one of two fixed slots (the pointer tree or T_(i+15)), by transferring Moore's weighted derivative machinery to l2, so for small eta it is stronger in both size and locality, and it makes the level-2 three-slot step of that node unnecessary; its explicit-constant items (merge tests, log-ratio turning-point kill) are not implied, since K here is effective but not computed.
  thompson-f-near-eigenvectors-have-fibonacci-tree-profiles: that is the level-0 Fibonacci profile within distance K; this is a tower at distance at most 15, with the same failure-mass shape in sqrt(eta).
  thompson-f-folner-function-exceeds-every-tower: that is Moore's global count, that a C^(-n)-Folner set has at least exp_n(0) elements, which says nothing about where mass sits; this is a mass statement for l2 vectors about two fixed addresses of the range tree, read off from the internal structure of Moore's proof (the right-spine doubling inside his Lemma proper_act plus a subtree-local form of his Lemma partial_growth).
  thompson-f-cnd-certificates-need-near-exponential-ball-growth: its route thompson-f-cnd-ball-growth-from-folner-tower extracts one Folner level set of a walk distribution by co-area and applies Moore's count to it; this never passes to level sets, works with the weighted measure f^2 directly, and bounds the mass of the bad set, which a level-set argument does not give.
  marginal-derivative-amplification-is-sharp-at-log-height: that abstracts the derivative step and bounds mu(h >= n) for any derivative datum with thin bad set; this uses the same bookkeeping for Moore's datum, adds the proper-action doubling at the last level and a subtree-local chain inequality, and translates the output into pointed forests, which is where the locality comes from.
  thompson-f-trees-carry-an-ackermann-derivative-hierarchy: that asks for stronger derivatives; any H_k with a subtree-local growth inequality would upgrade Theorem A here from towers to Ackermann-k by the same proof.
  thompson-f-one-sided-forest-windows-are-norm-lossless: that is the exact identity <f,Kf> = 4 - delta - energy on the one-sided forest model, used here as the setting; this is a structure theorem for near-optimal vectors on that model.
  thompson-f-is-amenable: that is the open root; this constrains every near-eigenvector quantitatively and decides nothing.
artifacts:
  - experiments/thompson-f-root-local-tower-2026-09-17/dictionary_check.py
  - experiments/thompson-f-root-local-tower-2026-09-17/dictionary_check.out
---

**ESTABLISHED** through `thompson-f-near-eigenvectors-root-local-moore-tower-proof`. That route
uses the published lemmas of J. T. Moore, arXiv:0905.1118v7 (Groups Geom. Dyn.), each quoted there,
plus a direct argument for everything else. The quantitative reading of Moore's lemmas and the dictionary
to pointed forests are new here. No priority is claimed for the Folner machinery.

**Setting.**
- Moore's conventions: `Γ = {x0^±1, x1^±1}`, and `f·g` means "f, then g".
- Each `f` in `F` has a reduced tree diagram `(L_f, R_f)`, with domain tree `L_f` and range tree `R_f`.
- For a tree `T` and a binary address `u`, `T/u = {s : u s ∈ T}`, and `|T/u|` is its number of leaves.
  This is 0 if a leaf of `T` is a proper prefix of `u`.
- `exp_0(0) = 0` and `exp_(k+1)(0) = 2^(exp_k(0))`.
- On `l2(F)` let `P = (1/4) Σ_γ ρ_γ`, where `ρ_γ F(s) = F(s·γ)`. For a unit vector `F ≥ 0`, set
  `η(F) = 1 − ⟨F, P F⟩`.
- The forest model is that of `thompson-f-one-sided-forest-windows-are-norm-lossless`.
  - `R` is the set of pointed forests `v = (T_0, T_1, ...; i)`.
  - `K` is the move operator.
  - For a unit `f ≥ 0` on `R`, `η(f) = 1 − ⟨f, K f⟩/4`, and `F` is amenable iff `inf η = 0`.

There is an absolute constant `K_0 ≥ 2`. It is effective, being the maximum of finitely many constants
in Moore's lemmas, but it is not computed here.

**Theorem A (l2, Moore coordinates).** Let `F ≥ 0` be a unit vector in `l2(F)` with `η = η(F)`. Let
`n ≥ 0` satisfy `12 K_0^(n+1) √η ≤ 1`. Then the set

`Y_n = {y ∈ F : |R_y/10| ≥ 2 exp_(n+4)(0) or |R_y/1^16 0| ≥ 2 exp_(n+4)(0)}`

has `F²`-mass at least `1 − 24 K_0^(n+2) √η`.

More precisely, let `∂` be Moore's tree derivative. Every `y` outside a set of mass
`24 K_0^(n+2) √η` has a nontrivial `S = ∂^n R_y` with one of two properties.
- The right-spine sizes increase: `2|S/1^j 0| < |S/1^(j+1) 0|` for `j < 16`. In this case
  `|R_y/1^16 0| ≥ 2 exp_(n+4)(0)`.
- The right-spine sizes decrease: the reverse inequalities hold for `j < 16`. In this case
  `|R_y/10| ≥ 2 exp_(n+4)(0)`.

**Corollary B (pointed forests).** Let `f ≥ 0` be a unit vector on `R` with `η = η(f)`. Let `n ≥ 0`
satisfy `12 K_0^(n+1) √η ≤ 1`. Then

`f²({v : |T_i| < 2 exp_(n+4)(0) and |T_(i+15)| < 2 exp_(n+4)(0)}) ≤ 24 K_0^(n+2) √η`.

- Take `n = ⌊log_(K_0)(1/(48 √η))⌋ − 2`. Then at least half of the mass of any vector with deficit
  `η` sits on forests where the pointer tree, or the tree 15 places to its right, has at least
  `exp_(n+4)(0)` leaves. Here `n = log(1/η)/(2 log K_0) − O(1)`.
- Only these two slots are involved. Nothing is claimed about the trees between them.

**Corollary C (cutoff kill with a two-slot window).** Suppose `f²`-almost every `v` has both
`|T_i| < N` and `|T_(i+15)| < N`. Then

`η ≥ (1/576) K_0^(−2 log* N − 4)`,

where `log* N` is the least `n` with `exp_n(0) ≥ N`.
- For comparison, the wave-19 cutoff is `c/(1 + log log N)^4`, over a window of `2 log_φ log_φ N + 9`
  trees.
- Any ansatz family that caps just these two trees at size `N` stays at `⟨f, Kf⟩/4 ≤ 1 − c K_0^(−2 log* N)`.
  This holds whatever the amplitudes and whatever the other trees look like.

**How it works (short).**
- **l2 to l1.** By Cauchy-Schwarz, `μ = F²` is a weighted `12√η`-Folner set in Moore's sense:
  `Σ_γ Σ_s |μ(s·γ) − μ(s)| ≤ 8√2 √η`.
- **Moore's chain, with mass kept.** Apply his three steps to `μ` itself instead of to a set:
  Folner->trees, then partial_marginalize `n` times, then removal of the marginal set `E**` of
  proper_act. Each step removes a marginal set, whose mass is at most a constant times the current
  Folner ratio, and pushes forward along a map that commutes with restriction to preimages. So the
  surviving mass is controlled pointwise in `y`.
- **Where the tower sits.** Outside `E**`, `S = ∂^n R_y` doubles along the 16 right-spine subtrees.
  This gives `|S/v| ≥ 2^15` at `v = 1^16 0` or at `v = 10`.
- **Local growth.** For a fixed address `v` and every `j`,
  `|∂^j R_y / v| ≥ 2^(|∂^(j+1) R_y / v| − 2) − 1`. The reason: the interior leaves of
  `∂^(j+1) R_y` below `v` carry doubling, pairwise disjoint subtrees of `∂^j R_y / v`.
  Inducting `n` times gives the tower at `v` itself.
- **Dictionary.** Let `φ : (0,1) → R` send the dyadic interval of `1^(k+1) 0` onto `[k, k+1]`, for `k ≥ 0`.
  - Conjugating by `φ` turns Moore's `x_0, x_1` into the forest generators `s_0, s_1`.
  - The pointed forest `v` becomes `y(v) = (φ^(−1) E(v) φ)^(−1)`, and its moves become right
    multiplications.
  - `R_(y(v))` is the reduced domain tree of `φ^(−1) E(v) φ`. It is dominated by an explicit diagram
    whose subtree at `1^(k+1) 0` is `T_(i+k)`.
  - Hence `|R_y/10| ≤ |T_i|` and `|R_y/1^16 0| ≤ |T_(i+15)|`. The induced Cayley graph is the move
    graph, so the two deficits `η` agree exactly.

**What changes.**
- **The near-eigenvector structure program (waves 17 to 19).** The level-by-level approach runs
  Fibonacci, then doubly exponential, then the proposed level 2 with its three-slot perturbation. It is
  superseded asymptotically.
  - The tower height here, about `log(1/η)`, is what that program hoped to reach after `log(1/η)`
    levels.
  - It arrives at a window of two fixed trees rather than `O(η^(−1/4))`.
  - The open level-2 step of `thompson-f-near-eigenvectors-need-doubly-exponential-tree-sizes` is
    therefore not needed for any size or locality conclusion. It would matter only for explicit
    constants.
- **Localisation is free.** Moore's theorem is stated, and imported into this graph, only as a count
  of the elements of a Folner set. Its proof in fact pins the growth to the right spine next to the
  root of the range tree, and in the forest model that spine is the pointer.
  - A near-eigenvector must put almost all its mass on forests whose pointer neighbourhood holds a
    tower-size tree.
  - An amplitude ansatz (product form, Markov size chains, renewal vectors) is dead as a route to
    `||P|| = 1` unless, at scale `η`, its law of `max(|T_i|, |T_(i+15)|)` has tower-type tails of
    height about `log(1/η)`. This holds whatever the ansatz does elsewhere.
- **Upgrade path.** The proof uses only three properties of Moore's derivative:
  - it has a thin bad set;
  - it satisfies a subtree-local growth inequality;
  - it doubles along the right spine at the last level.
  Any derivative from `thompson-f-trees-carry-an-ackermann-derivative-hierarchy` with the same
  subtree-local form would give Ackermann-size trees at the pointer by the same argument.

**Scope.**
- This is a constraint on near-eigenvectors. It is conditional on `η` being small and proves neither
  answer to `thompson-f-is-amenable`.
- The constant `K_0` is not computed. For moderate `η`, the explicit constants of the wave-19 node can
  be better.
- The global size statement alone ("some element of the reduced diagram is a tower") can also be
  reached from Moore's count through a co-area level set, but only for one level set and with no mass
  bound. The mass bound and the two-slot locality are the content here.
- Infinitely supported `f` are handled by truncation (Step 7 of the route).

**Computation.** `experiments/thompson-f-root-local-tower-2026-09-17/dictionary_check.py` uses the
standard library and exact rationals. Its output is in `dictionary_check.out`. It checks four things:
- (A) `φ x_k φ^(−1) = s_k` on 3000 points.
- (B) The explicit diagram of Step 6 represents `φ^(−1) E(v) φ` on 400 random pointed forests, both
  before and after caret reduction.
- (C) `|L_g / 1^(k+1) 0| ≤ |T_(i+k)|` on 2054 (state, k) pairs. The shapes are equal on all 705 pairs
  with `T_(i+k)` nontrivial.
- (D) A merge is right composition with `x_1`, and a pointer step is right composition with `x_0`.

Proof route: `thompson-f-near-eigenvectors-root-local-moore-tower-proof`.

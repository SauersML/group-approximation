# Swarm attack: rokhlin-maximality-ascends-amenable-normal-extensions

Date: 2026-09-16. Agent: swarm-rokhlin-maximality-ascends-ame. Hole worked: the target itself.

## 1. Setup

`N ◁ W` amenable, `Q = W/N` Rokhlin-maximal at `q`. By Seward's Theorem 1.10
(`seward-per-group-rokhlin-entropy-of-bernoulli-shifts`, item 1), for countably infinite `Q` this says
`min(k log q, h_sup(Q)) = k log q` for every `k`, that is INF(`Q`). So the hypothesis is INF(`Q`) and the
conclusion is INF(`W`), independent of `q`.

Outcome: a reduction, together with a record of the approaches that die. No proof of the target and no
counterexample.

## 2. What was proved

Notation (Seward): `h_sup(G)` is the supremum of the finite Rokhlin entropies of free ergodic p.m.p. actions of
`G`. INF(`G`) means `h_sup(G) = ∞`. POS(`G`) means some free ergodic p.m.p. action of `G` has positive Rokhlin
entropy.

### 2.1 Proposition (products with a torsion-rich amenable factor)

Let `G` be countably infinite. Let `P` be countable and amenable, with finite subgroups of unbounded order; for
example `P = ⊕_{n≥1} Z/nZ`. Then

    h_sup(P × G) ∈ {0, ∞},   and   h_sup(P × G) = ∞  iff  INF(G).

Consequently POS(`P × G`) ⟺ INF(`P × G`) ⟺ INF(`G`).

*Proof.*
- **Zero side.** If `h_sup(G) < ∞`, Seward's Theorem 1.11 (import item 3) gives `h_sup(P × G) = 0`. This uses
  only the torsion hypothesis on `P`.
- **Infinite side.** Suppose INF(`G`) and fix `q ≥ 2`. For every `k`, import item 1 with `L = A^k` uniform gives
  `h^Rok_G((A^k)^G) = min(k log q, ∞) = k log q`. So `G` is Rokhlin-maximal at `q` in the sense of Theorem A.
  - Put `H = {1} × G`, which is infinite. Its right cosets are `H(p,g) = {p} × G`, so `H\(P × G)` is `P`, and
    `s = (p_s, g_s)` acts by `p ↦ p p_s`.
  - Given finite `S ⊆ P × G` and `δ > 0`, amenability of `P` gives a finite nonempty `F ⊆ P` with
    `|F p_s \ F| ≤ δ|F|` for all `s ∈ S`. Right Følner sets exist by inverting left ones.
  - Then `Ω' = {{p} × G : p ∈ F}` satisfies `|Ω' s \ Ω'| ≤ δ|Ω'|`, so `H` is co-amenable in the Følner sense.
  - Theorem A (`rokhlin-maximality-ascends-co-amenable-subgroups`) makes `P × G` Rokhlin-maximal at `q`.
    Import item 1 for the countably infinite group `P × G` gives `min(k log q, h_sup(P × G)) = k log q` for every
    `k`, so `h_sup(P × G) = ∞`. This uses only amenability of `P`.
- **POS.** `positive-rokhlin-entropy-action-gives-positive-supremum` (1 ⟺ 4) gives POS(`P × G`) ⟺
  `h_sup(P × G) > 0`. By the dichotomy that is `h_sup(P × G) = ∞`, which is INF(`G`). ∎

No step is new mathematics: the proposition is Seward's Theorem 1.11 plus Theorem A. What is new is putting them
together. Seward's (∀`G` POS) ⟹ (∀`G` INF) argument uses only the zero side. The infinite side identifies
*which* side of the dichotomy `P × G` lies on, one group at a time.

It differs from `rokhlin-supremum-dichotomy-with-centralized-self-copies`, whose dichotomy needs `Γ ⊇ Γ × Γ`;
here `G` is arbitrary. In particular it gives, for every single countably infinite `G`:

    INF(G)  ⟺  POS(P × G).

### 2.2 Corollary (reduction of the target)

Let `𝒞` be the class of countable groups `W` with an amenable normal subgroup `N` such that INF(`W/N`). The class
is closed under `W ↦ P × W`: `P × N ◁ P × W` is amenable and `(P × W)/(P × N) ≅ W/N`. The analogous classes with
abelian, locally finite or elementary amenable kernels are also closed, since `P = ⊕ Z/nZ` is locally finite
abelian.

**Claim.** The target holds iff every `W ∈ 𝒞` has POS.

- (⟹) Let `W ∈ 𝒞`. INF(`W/N`) implies `W/N` is Rokhlin-maximal at `q`, so the target makes `W` maximal at `q`.
  `W` is infinite, so import item 1 gives INF(`W`), and INF ⟹ POS.
- (⟸) Let `N ◁ W` be amenable with `W/N` maximal at `q`.
  - If `W/N` is finite, `W` is amenable. If `W` is infinite, it is sofic and hence maximal (import item 4). If
    `W` is finite, the time-zero partition is optimal by counting.
  - If `W/N` is infinite, import item 1 gives INF(`W/N`), so `P × W ∈ 𝒞` has POS by hypothesis.
    Proposition 2.1 with `G = W` gives INF(`W`), and import item 1 makes `W` maximal at `q`.

The same argument gives: ascent across locally finite kernels ⟺ POS for every locally-finite-by-INF group. That
implies the finite-kernel case (`finite-kernel-ascent-from-amenable-kernel-ascent`, Kaloujnine–Krasner shape).
One instance: the Kun–Thom wreath `W_KT` is Rokhlin-maximal iff POS(`P × W_KT`).

**Honest assessment.** The new hole is *equivalent* to the target, not strictly weaker. Its advantage is shape
only. A proof needs only **one** free ergodic action of an amenable-by-INF group with positive Rokhlin entropy,
of any kind: not a Bernoulli shift, not a lower bound of the right size. A counterexample must be total collapse.
A failure of the target at `W` produces `P × W ∈ 𝒞` with `h_sup = 0`. By `generators-dense-iff-zero-rokhlin-entropy`,
generating partitions are then dense in its free actions. So every counterexample upgrades to a total-collapse
counterexample, an amenable-by-INF group with zero Rokhlin supremum. A disproof may therefore aim at collapse
directly.

## 3. Approaches and where each dies

Throughout, `α` is a generating partition of `A^W` with `H(α) < log q`. The aim is a contradiction, or a POS
action of `P × W`. These are sketches recorded to save the next attacker time. None is a proof of anything
beyond its stated failure point.

1. **`N`-entropy set function along `Q`.**
   - For finite `F ⊆ Q` with a lift `F~`, put `φ(F) = h_N(σ-alg_N(∨_{f ∈ F~} fα))`. This is Kolmogorov–Sinai
     entropy, available since `N` is amenable.
   - Subadditivity and `N`-invariance give `φ(F) ≤ |F| H(α)`.
   - Recovering the Bernoulli coordinates on `N F~` needs translates over a ball `B_r F`. So one gets
     `φ(B_R) ≥ |B_(R−r)| log q`, hence `H(α) ≥ log q · |B_(R−r)| / |B_R|`.
   - **Dies:** the recovery radius `r = r(ε)` is unbounded as the error `ε → 0`, and for nonamenable `Q` the
     ratio `|B_(R−r)|/|B_R|` stays bounded away from 1. This is the boundary count of the co-amenable attempt
     with `H = N`, seen from the kernel side.
2. **Block codes along Følner sets of `N`.**
   - Code the coordinates in `N`-blocks `S y` with `S ⊆ N` Følner.
   - **Dies:** the block family is not `W`-stationary, because conjugation by `w` sends `S` to `w S w^-1`.
     Making it stationary is exactly the coherent-window condition, which forces a conjugation-invariant mean
     (CIM, `coherent-kernel-folner-windows-force-conjugation-invariant-mean`). The CIM fails on the Kun–Thom wreath.
3. **Cocycle `Q`-systems.**
   - Fix a section `Q → W` with cocycle `c(q, q') ∈ N`. A free `W`-action becomes a `Q`-"system" with
     `N`-fibres twisted by `c`, and `A^W` over the `N`-invariant σ-algebra is a relative Bernoulli factor over `Q`.
   - **Dies twice:**
     - recovery of the fibre coordinates needs windows coherent under `c`, which is the CIM again;
     - even with windows, the lower bound needs relative maximality over `Q`, i.e. Seward's direct-product
       conjecture for a non-weakly-minimal `Y` (`seward-direct-product-relative-rokhlin-entropy-conjecture`),
       plus a lift cocycle that need not exist.
4. **Skew products `X_β`.** Given a cocycle `β : Q × Y → N` into a free `Q`-system `Y`, the skew product
   `Y × (N-Bernoulli)` is a free `W`-action. **Dies:** there is no lower bound on its Rokhlin entropy.
   Positivity would again need a relative count along `Q` with `N`-fibres.
5. **Central infinite kernels.**
   - Here a CIM exists, since conjugation is trivial on `N`, so windows are coherent.
   - **Dies:** after averaging along `N`, the remaining count is over `Q` with coefficients in the twisted
     section action. That is the extension-class obstruction of the finite-kernel case
     (`research/artifacts/rokhlin-finite-kernel-ascent-equivalence-2026-09-13.md`, Section 5), which is open.
6. **Sofic `Q` with window fibres.** Use sofic models for `Q` and Følner windows of `N` as fibres over each
   model point. **Dies:** gluing the fibres consistently along model edges needs coherent windows, which gives the
   CIM. A consistent gluing would also amount to finite models of `W`, which the Kun–Thom wreath does not have
   (`kun-thom-nonsofic-wreath`).
7. **Finite quotients of `N`.**
   - Replace `N` by `W`-invariant finite-index subgroups `M` and pass to `W/M`, a finite-kernel extension of `Q`.
   - **Dies:** a deficit witness over `W` folds on a sofic-invisible element
     (`sofic-radical-localizes-bernoulli-deficit-witnesses`). Finite quotients see only what the sofic radical
     leaves.
   - For `W`-residually finite kernels, local embeddings reduce the question to finite kernels, which is the
     open `rokhlin-maximality-ascends-finite-normal-extensions`. So nothing is gained.
8. **Pull-back of the quotient Bernoulli shift.** **Dies:** factors fixed by the infinite subgroup `N` have zero
   outer entropy (`infinite-subgroup-invariant-information-has-zero-outer-entropy`). The same kills product
   actions `X_P × X_W` of `P × W` as a route to POS. Each factor is fixed by an infinite subgroup, so
   `h_(P×W)(X_P × X_W) = h(X_P × X_W | B(X_W))`, and no lower bound follows.
9. **Relative entropy over `Y = q^Q`.**
   - Bound `h_W(A^W)` below by `h_W(A^W × Y | Y)` and try Seward's weak-containment equality.
   - **Dies:** it is circular. Weak containment of `Y` in all free `W`-actions reduces the relative entropy back to
     `h_W(A^W)`, the quantity sought.
10. **Finite subgroups `T ≤ P`.**
    - To get POS(`P × W`) from `W × T`, note restriction gives `h_(W×T)(X) ≥ h_W(X)/|T|` only.
    - **Dies:** the bound decays as `|T| → ∞`, and `P` is not a finite join of its finite subgroups. This is the
      mechanism of Seward's Theorem 6.7 run in reverse, and it only produces collapse.
11. **Invariant random subgroups (Kun–Thom lamps).**
    - Let `M_ω ≤ N` be the common kernel of `m` i.i.d. uniform random functionals on `N = ⊕_X Z/2`.
      - Its law is conjugation-invariant: `W` permutes the coordinates of a functional, and `N` fixes it.
      - So `M_ω` is an invariant random subgroup of `W` with `N/M_ω` of order at most `2^m`.
      - It converges to `δ_1` in the Chabauty topology, since a fixed nonzero lamp lies in `M_ω` with
        probability `2^-m`.
      - `M_ω` is not normal in `W`, so `W/M_ω` is a random coset space with finite fibres over `W/N`, not a group.
    - The idea is to transfer maximality from these finite-fibre coset spaces to the limit.
    - **Dies:** even at fixed `m`, the needed statement is a random finite-fibre ascent over `Q`, which is no easier
      than the finite-kernel case. The `N`-translates of a generator depend on the random functional at each
      coset, so there is no finite join.
    - The closedness result that would let the limit pass (attributed to Bowen–Chapman) was **not verified**:
      the fetch failed.
12. **Regular wreath `Z/2 wr Q` as a model case.**
    - Here the complement `Q` is **not** co-amenable when `Q` is nonamenable, so Theorem A does not apply.
    - *Proof:* a `W`-invariant mean `m` on `N = ⊕_Q Z/2` has `m({0}) = 0`, since it is translation-invariant and `N`
      is infinite. Then `μ(E) = m(n ↦ |supp(n) ∩ E| / |supp(n)|)` is a `Q`-invariant mean on `Q`.
    - So Theorem A covers only split extensions whose complement is co-amenable. That class is already in the
      target's Attempts.

**Summary of the failure pattern.** Every mechanism either
- counts along `Q` and pays a nonamenable boundary (1, 9, 10), or
- counts along `N` and needs coherent windows, which gives the CIM (2, 3, 5, 6), or
- uses finite approximations that see only the sofic radical (7, 11), or
- uses quotient information with zero outer entropy (4, 8).

Section 2 shows a proof may use **any** free action of `P × W`. So the missing tool is a positive lower bound for one
action of an amenable-by-INF group, and none of 1–12 supplies it.

## 4. Literature

**Gate attempts on 2026-09-16.**
- `export.arxiv.org/api/query` failed every time: connection reset, `CONNECT tunnel failed, response 502`, proxy
  `ws_closed_mid_exchange`, and HTTP 429 through WebFetch at about 03:35 UTC.
- `arxiv.org/abs` pages failed the same way.
- The shared WebSearch budget of the session was exhausted.
- I did not change proxy or TLS settings. So **no 2024–2026 paper was read in this attack**, and the gate is
  incomplete.

**Sources used, all through nodes already in the graph and not re-fetched:**
- B. Seward, *Krieger's finite generator theorem for actions of countable groups II*, arXiv:1501.03367v4.
  - Theorems 1.10, 1.11 and 1.12 and Corollary 4.1, as quoted verbatim in
    `seward-per-group-rokhlin-entropy-of-bernoulli-shifts`.
  - Corollary 7.7, via `positive-rokhlin-entropy-action-gives-positive-supremum`.
  - Section 1 ends with "(∀G POS)⇒(∀G INF)", proved through `P × G`. The per-group identification
    INF(`G`) ⟺ POS(`P × G`) of Section 2.1 needs Theorem A, which is not in that paper. I found no statement of
    it in the graph's sources, but the gate above is incomplete, so no novelty is claimed.
- B. Seward, *Weak containment and Rokhlin entropy*, arXiv:1602.06680v2, via
  `seward-direct-product-relative-rokhlin-entropy-conjecture`.
- A. Alpeev and B. Seward, *Krieger's finite generator theorem for actions of countable groups III*,
  arXiv:1705.09707, via `infinite-subgroup-invariant-information-has-zero-outer-entropy`.
- Theorem A is the graph's own result (`rokhlin-maximality-ascends-co-amenable-subgroups`, artifact
  `research/artifacts/rokhlin-co-amenable-ascent-and-thompson-v-2026-09-12.md`).
- "Amenable groups are sofic" is standard (Gromov; Weiss, *Sofic groups and dynamical systems*, 2000). It is used
  only in the trivial finite-quotient case, and the reference was not re-fetched here.

**Seen but not read (unverified).**
- arXiv:2511.06586, Bowen–Chapman, *Surjunctivity does not characterize cosoficity of invariant random subgroups*.
  - The title is confirmed from repo text (`research/sofic-groups-are-surjunctive-citation.md`).
  - Any IRS closedness statement usable in Section 3, item 11, is **unverified**.
- arXiv:2607.11549 is recorded by a sibling swarm note as a search snippet about amenable groups. Not relevant here.
- arXiv:2607.20735, 2608.02025 and 2604.19174 appeared in an earlier partial listing, but their abstracts could not be
  fetched. Nothing is claimed about their content.

**Target's own earlier search.** The target's Attempts record arXiv:1501.03367, 1602.06680, 1705.09707,
1804.05270 and 1805.08279 as containing no mechanism for joint counting along `N` and `W/N`.

## 5. Graph files written

- `research/rokhlin-supremum-of-torsion-products-is-zero-or-infinite.md`: the claim of Section 2.1.
- `research/rokhlin-supremum-torsion-products-proof.md`: the route proving it from three established nodes.
- `research/amenable-by-maximal-groups-have-positive-rokhlin-entropy.md`: the new open hole, POS for amenable-by-INF
  groups.
- `research/amenable-kernel-ascent-from-positive-entropy-on-products.md`: the route from the hole, the claim and the
  Seward import to the target. It is the (⟸) direction of Section 2.2.

The reverse implication (target ⟹ hole) is recorded in the hole's body, not as a route.

## Referee (2026-09-16)

**What was checked.**
- All four graph files and this note were read in full, together with the nodes they use:
  `seward-per-group-rokhlin-entropy-of-bernoulli-shifts`, `rokhlin-maximality-ascends-co-amenable-subgroups`
  (with Sections 0–2 of its artifact), `positive-rokhlin-entropy-action-gives-positive-supremum`,
  `infinite-subgroup-invariant-information-has-zero-outer-entropy`, `finite-kernel-ascent-from-amenable-kernel-ascent`,
  `rokhlin-supremum-dichotomy-with-centralized-self-copies` and the target.
- **Theorem A hypotheses.** They match the application. The artifact's Følner form uses right cosets `Hg` with the
  action `(Hg)s = Hgs` and `H` infinite. For `H = 1 × G`, the right coset of `(p, g)` is `{p} × G`, and `s` acts by
  `p ↦ p p_s`. Inverting a left Følner set `E` for `{p_s^-1}` gives `F = E^-1` with
  `|F p_s \ F| = |p_s^-1 E \ E| ≤ δ|E|`, which I recomputed. I also reread the Theorem A proof (Steps 1–7) and found
  no use of normality, finite generation or amenability of `G`. Its lower bound uses Abért–Weiss and Seward's
  weak-containment equality for the Bernoulli complement, which applies here.
- **Zero side.** Item 3 of the import (Seward, Theorem 1.11, quoted verbatim in the graph) is used exactly as stated.
- **Item 3 cycle.**
  - POS ⟹ `h_sup > 0`: this is Corollary 7.7 via the graph node.
  - The dichotomy then gives INF(`G`), and INF(`G`) gives INF(`P × G`).
  - INF ⟹ RBS uses items 1 and 2. For item 2, `h_sup = ∞` supplies a positive-entropy action.
  - RBS ⟹ POS holds because the Bernoulli 2-shift over an infinite group is free and mixing.
  - The cycle is correct.
- **The reduction route.** Case 2 is correct:
  - `P × N` is amenable and normal in `P × W`, with quotient `≅ W/N`;
  - `W` is infinite;
  - item 3 of the new claim with `G = W` gives INF(`W`), and item 1 gives maximality.
  - The locally finite remark is also correct: an extension of a locally finite group by a locally finite group is
    locally finite, so `P × N` is locally finite.
- **Equivalence.** The hole is honestly labelled as equivalent to the target: target ⟹ INF(`W`) ⟹ POS(`W`).
- **Item 12 of Section 3.** It is correct. The supports give a `Q`-invariant mean from a translation- and
  conjugation-invariant mean on `⊕_Q Z/2`.
- **Duplicates.** `bin/cairn search --similar` on both new claims found no duplicate. The per-group statement
  INF(`G`) ⟺ POS(`P × G`) is not in the graph. The self-copy dichotomy only covers groups containing their own
  square.
- **Literature spot-check.**
  - `arxiv.org/abs/1501.03367` and `arxiv.org/abs/1602.06680` were fetched on 2026-09-16, and the titles and
    authors are confirmed. Neither abstract states the per-group product identification.
  - The full text of 1501.03367 could not be parsed (no working PDF text extractor), and WebSearch was exhausted.
    So the novelty gate stays incomplete, and the nodes claim no novelty.

**Changes made.**
1. `amenable-kernel-ascent-from-positive-entropy-on-products`, Case 1 with `W` finite. The counting argument
   holds only for the plain infimum over generating partitions. I added the case of Seward's convention, which
   conditions on the invariant σ-algebra. There the hypothesis fails for every finite quotient: the time-zero
   partition is correlated with the invariant "constant configuration" events. So the implication is vacuous
   and the case is covered under both conventions.
2. `amenable-by-maximal-groups-have-positive-rokhlin-entropy`, Attempts. "Kills product actions" was too strong.
   It now says that zero outer entropy reduces product actions to entropy relative to a factor, and that no lower
   bound follows.

**Verdict.** The claim `rokhlin-supremum-of-torsion-products-is-zero-or-infinite` is sound as a composition of
established nodes. The reduction route is valid, and its new hole is honestly marked as a reformulation equivalent
to the target. It lands with the two small fixes above.

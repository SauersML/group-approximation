# Gottschalk beyond soficity: linear sofic, weakly sofic, and uniform quantitative surjunctivity

Lane `gk3-approx-surjunctive`, 2026-09-14. Directive: extend surjunctivity past sofic groups to the next
approximation classes, or land the barrier, and name the exact gap. The gap map
`research/artifacts/approx-class-surjunctivity-gap-map-2026-09-14.md` assembles the reduction and the
barrier from nodes already on main. This file adds the one new theorem (Section 3).

## 0. Verdict

- **No class beyond soficity is proved surjunctive.** These stay OPEN:
  - `linear-sofic-groups-are-surjunctive`;
  - `metric-ultraproducts-of-finite-groups-are-surjunctive`, the weakly sofic content;
  - `surjunctive-groups-are-uniformly-quantitatively-surjunctive`.
- **Landed:** `uqs-groups-are-closed-under-amenable-extensions`, with route
  `uqs-amenable-extension-closure-proof`. UQS passes to extensions with amenable quotient, with an explicit
  constant. Towers of such extensions over a UQS group are therefore UQS and surjunctive. The calibration
  makes every amenable group UQS. It adds no new surjunctive host: no nonsofic group is known to be UQS.
- **Exact gaps:** Section 4.

## 1. Literature pinned on main (not re-read by this lane)

- **Gromov--Weiss**, sofic groups are surjunctive: `sofic-groups-are-surjunctive-citation`. The attribution
  there was checked against the Bowen--Chapman abstract.
- **Arzhantseva--Păunescu** Theorem 7.4 and Proposition 2.8 (arXiv:1212.6780v1), verbatim in
  `linear-sofic-group-algebra-stably-finite-citation`: an `F`-linear sofic group has a stably finite group
  algebra over `F`. Their Question 8.5 (is some nonsofic group linear sofic?) is cited in
  `linear-sofic-groups-are-surjunctive`.
- **Glebsky--Rivera** Definition 4.1 and Theorem 4.3 (arXiv:0709.0026v2), verbatim in
  `glebsky-rivera-w-sofic-criterion-citation`.
- **Not pinned:** Capraro--Lupini's monograph and Elek--Szabó's original papers. This lane ran no
  literature search certifying that no surjunctivity theorem for a nonsofic linear sofic or weakly sofic
  group exists.

## 2. Where each class stops

### 2.1 Linear sofic groups

- **Reduction.** By `linear-sofic-surjunctivity-is-a-rank-implication-per-datum`, the claim over `F_p` is a
  rank implication per strict datum. The recorded route needs
  `prime-field-left-inverse-pairs-are-stably-formalizable`, which is open.
- **The suggested linearization, and why it fails.** Take `A = F_p`. The local functions on `A^G` form
  `L(G) = F_p[X_g : g in G] / (X_g^p - X_g)`.
  - Its monomials with finite support are a permutation basis. So `L(G)` is a permutation
    `F_p[G]`-module with finite stabilizers (a stabilizer of a finite support `S` lies in `S S^-1`) and
    infinitely many orbits.
  - For a strict pair `sigma tau = id`, the pullback `tau*` is `F_p[G]`-linear with `tau* sigma* = id`. So
    `tau*` is onto. The indicator of a missing pattern is killed by `tau*`, so `tau*` is not injective.
  - This is a one-sided inverse on a module of **infinite** rank. `tau*` raises radius: it maps functions of
    radius `s` to radius `s + R`, and preserves no finitely generated submodule. So stable finiteness of
    `F_p[G]`, which controls only finite-rank matrices, gives nothing.
  - This is the finite-dimensional filtration remark of `amenable-extension-surjunctivity-transfer-2026-09-12.md`
    (Section 1): the obstruction lives in a multiplicative ideal, while filtrations of finite rank are additive.
- **Counting in the rank metric.** `site-pullbacks-are-discontinuous-in-the-rank-metric`: nonlinear local
  rules have no rank-metric evaluation. Counting reaches only near-monomial tuples
  (`gromov-weiss-is-the-monomial-case-of-the-rank-implication`).

### 2.2 Weakly sofic groups and metric ultraproducts

- **Reduction.** `strict-reverse-words-lie-in-bounded-width-profinite-closures`. It needs one width bound `n`
  per strict datum, valid in every finite group.
- **The count consumes an `H`-set, not the length.** `hamming-transports-of-weak-sofic-models-are-soficity`:
  uniform Hamming transports of weakly sofic models exist iff the group is sofic. The loss is total. For a
  nonsofic weakly sofic group, every family of finite actions of the models has the decoder identity fail at
  all but a vanishing fraction of points on some finite set. So the Gromov--Weiss count certifies membership
  only in the sofic reflection kernel.
- **Finite surjunctivity gives no uniform width.** In each finite image a reverse word is a product of
  conjugates of forward relators, but with conjugacy width growing with the image.

### 2.3 Uniformly quantitatively surjunctive groups

- **Established.** `amenable-extensions-of-uqs-groups-are-surjunctive`, and heredity to subgroups and uniform
  directed unions (Proposition 3.1 of `amenable-extension-surjunctivity-transfer-2026-09-12.md`).
- **New here.** Closure under extensions with amenable quotient (Section 3).
- **Where it stops.** No nonsofic group is known to be UQS or AQS. The peeled nonsofic witnesses carry no
  deficit (Section 4.6 of `quantitative-surjunctivity-residue-2026-09-12.md`). Simple Kazhdan payoff hosts have
  no infinite amenable quotient.

## 3. UQS is closed under amenable extensions

### 3.1 Statement

**Definition.** `N` is UQS if for every finite `B` and `w >= 1` there is `delta_N(B,w) > 0` such that no
injective automaton maps `(B^n x D^j)^N` into `(Y_1 x ... x Y_n) x (D^(j'))^N` when `(j' - j) log|D| < delta_N n`
and each `Y_i <= B^N` is a subshift missing some pattern on at most `w` sites.

**Theorem 3.1.** Let `N <| G` with `Q = G/N` amenable, and let `N` be UQS. Then `G` is UQS with

```text
delta_G(B, w) = min_(1 <= u <= w) delta_N(B^u, w) / (4 w^3).
```

### 3.2 Proof

Fix representatives `s_q` (`s_e = e`), write `s_q g = n_(q,g) s_(q gbar)` and `x_q(n) = x(n s_q)`. Fix `B`, `w`,
and put `delta = delta_G(B,w)`. Suppose `Phi` is injective from `(B^n x D^j)^G` into
`(Y_1 x ... x Y_n) x (D^(j'))^G`, with memory `M` containing `1`, `(j' - j) log|D| < delta n`, and `Y_i` missing
`r_i` on `W_i`, `|W_i| <= w`.

1. **Left inverse.** `Phi` is a homeomorphism onto its closed image and commutes with the shift. Its inverse is a
   continuous equivariant map on a subshift. By uniform continuity it has a finite memory, and extending its
   local rule arbitrarily to all patterns gives an automaton `sigma` with memory `S` and `sigma Phi = id`.
2. **Følner set.** Put `Kbar = Mbar ∪ Sbar ∪ union_i Wbar_i`. Choose `eps <= 1/(2w)` with
   `eps |Sbar| (n log|B| + j log|D|) <= delta n`, and a finite `F <= Q` with `|F k \ F| <= eps |F|` for all
   `k in Kbar` (right Følner sets exist since `Q` is amenable; if `Q` is finite take `F = Q`). Put:
   - `F^+ = F Mbar`, which contains `F`;
   - `F^- = {q in F : q Sbar <= F}`, with `|F \ F^-| <= |Sbar| eps |F|`;
   - `F'_i = {q in F : q Wbar_i <= F}`, with `|F \ F'_i| <= w eps |F| <= |F|/2`.
3. **Transplant.** `Phi(x)_q(n) = mu((x_(q mbar)(n n_(q,m)))_m)`, by Lemma 2.1 of the transfer artifact. So the
   rows of `Phi(x)` in `F` depend only on the rows of `x` in `F^+`, through an automaton over `N`.
   - `Psi(x) = (Phi(x)|_F, x|_(F^+ \ F^-))` is an automaton over `N` on `((B^n x D^j)^(F^+))^N`.
   - `sigma` recovers `x_q` for `q in F^-` from the rows `q Sbar <= F` of `Phi(x)`. So `Psi` is injective.
4. **Tiles.** For each `i` take a maximal `T_i <= F'_i` with the sets `q Wbar_i` pairwise disjoint.
   - Every `q in F'_i` lies in some `q_k Wbar_i Wbar_i^-1`. So `|T_i| >= |F'_i| / w^2 >= |F| / (2w^2)`.
   - For `q in T_i`, `n s_q w = n n_(q,w) s_(q wbar)`. So track `i` on the rows `q Wbar_i`, read as a configuration
     over `N` with alphabet `B^(Wbar_i)`, avoids the partial pattern with value `r_i(w)` at coordinate
     `(wbar, n n_(q,w))`, for every `n`.
   - `w -> (wbar, n_(q,w))` is injective, so the pattern is consistent. Its window `{n_(q,w)}` has at most `w`
     sites. The tile subshift is closed, `N`-invariant and proper, and it misses a full pattern extending
     `r_i` on at most `w` sites.
   - Tiles of different tracks use different coordinates.
5. **One alphabet.** The sizes `u_i = |Wbar_i|` lie in `{1,...,w}`. So some `u` carries
   `n' >= n |F| / (2w^3)` tiles. Put `B' = B^u`, identified with each `B^(Wbar_i)` of size `u`.
   - **Source.** Regroup `n' u` of the `n |F^+|` source `B`-coordinates into `n'` tracks over `B'`. `E_s`
     collects the rest, so `log|E_s| = (n|F^+| - n'u) log|B| + j|F^+| log|D|`.
   - **Target.** `n'` tile tracks, each in its proper subshift. `E_t` collects the rest, so
     `log|E_t| = (n|F| - n'u) log|B| + j'|F| log|D| + |F^+ \ F^-| (n log|B| + j log|D|)`.
   - Since `F^- <= F <= F^+`,

     ```text
     log|E_t| - log|E_s| = (j' - j)|F| log|D| + |F \ F^-| (n log|B| + j log|D|)
                          < delta n |F| + delta n |F|  =  2 delta n |F|  <=  delta_N(B', w) n'.
     ```

     The last inequality uses `delta <= delta_N(B^u,w) / (4w^3)` and `n' >= n|F| / (2w^3)`.
6. **Normal form.** Let `c = delta_N(B', w) n' - (log|E_t| - log|E_s|) > 0`.
   - Take `K` independent copies of `Psi`. Choose an injective map `E_t^K -> E^(J')`, where
     `J' = ceil(K log|E_t| / log|E|)` and `E = E_s` if `|E_s| >= 2`, else `E = B'`.
   - Take `J = K` if `E = E_s`, and `J = 0` otherwise.
   - The result is an injective automaton from `(B'^(K n') x E^J)^N` into
     `(product of K n' tile subshifts) x (E^(J'))^N`, with margin
     `(J' - J) log|E| <= K (log|E_t| - log|E_s|) + log|E|`.
   - For `K > log|E| / c` this is below `delta_N(B', w) K n'`, contradicting UQS of `N`. QED

### 3.3 Calibration

- **The trivial group is UQS** with `delta(C, w) = log(|C| / (|C| - 1))`. Over one point, an injection
  `C^n x D^J -> (Y_1 x ... x Y_n) x D^(J')` with every `|Y_i| <= |C| - 1` forces
  `(J' - J) log|D| >= n log(|C| / (|C| - 1))`.
- **Every amenable group is UQS**, by Theorem 3.1 with `N = 1`, with
  `delta(B, w) = -log(1 - |B|^(-w)) / (4w^3)`. This is within a factor `O(w)` of the sofic counting constant
  recorded in `surjunctive-groups-are-quantitatively-surjunctive`.
- **Products.** `N x Q` is UQS for UQS `N` and amenable `Q`.

### 3.4 Remarks

- **AQS does not propagate by this device.** The transplanted margin `(j' - j)|F| log|D|` grows with `|F|`. AQS
  constrains only bounded margins, except for two-ended quotients, which is already Theorem B part 2 of the
  transfer artifact.
- **No new host.** A nonsofic UQS kernel would make every group in its amenable-extension towers UQS and
  surjunctive. None is known.
- **Known witnesses already covered.** `G x W` and `G x D`, for surjunctive `G` and Kun--Thom wreaths `W` or
  doubles `D`, are surjunctive by `products-with-lef-permanence-closure-factors-are-surjunctive`. The payoff
  would be non-split amenable extensions of a nonsofic UQS kernel.
- **Not independently re-derived.**

## 4. Exact gaps

Going strictly beyond sofic groups needs one of the following. Every counting mechanism on record stops at the
sofic reflection kernel (gap map, Section 3).

1. `prime-field-left-inverse-pairs-are-stably-formalizable` with nontrivial memory, giving `N_lin(F_p)`. A proof
   must bound the radius growth of `tau*` on the infinite-rank module `L(G)` (Section 2.1).
2. A uniform bounded-width closure bound, `strict-reverse-words-lie-in-bounded-width-profinite-closures`, giving
   `N_ws`.
3. UQS for some nonsofic surjunctive group, e.g. a Kun--Thom wreath. It would have to carry a per-track deficit
   through marked-site peeling. By Theorem 3.1 it would then propagate along amenable extensions.

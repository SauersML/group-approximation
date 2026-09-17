# Height-graded germ models for Bernoulli deficit witnesses

Agent a-gs-kazhdan-rokhlin, swarm-0917, 2026-09-17. Target hole
`bernoulli-rokhlin-maximal-on-fg-simple-kazhdan-groups`, family symbolic-dynamics, role transplanter.

**Summary.**
- Section 1 proves a counting lemma: the Gromov--Weiss count behind
  `sofic-radical-localizes-bernoulli-deficit-witnesses` needs no permutations. Arbitrary self-maps of a
  finite set work, provided most points see a correct chart of the pattern.
- Section 2 uses that freedom to build models of a witness pattern that are not group
  approximations: shrinking colorings sorted by height. It proves Theorem A.
  - Hypothesis: the pattern carries a nonnegative integer height potential whose zero-height
    letters generate a finite subgroup.
  - Conclusion: `Phi >= log q` on every group, with no soficity assumption anywhere.
- Section 3 places Theorem A among the existing filters.
- Section 4 records the amenable-core extension (Theorem B), which is OPEN.
- Section 5 records the exact step where every germ-type model dies: a nonamenable core.

Notation follows `bernoulli-rokhlin-deficit-has-a-finitary-witness`:
- `G` is a countable group, `|A| = q >= 2`, and the configuration is `(k, E, F, psi)`, with `psi`
  taking values in a finite set `R`.
- `x` is iid uniform on `A^k` over `G`, `y_f = psi((x(fe))_(e in E))`, and
  `Phi = (1/k)[H(psi(x|_E)) + H(x(1) | y_F)]`.
- `Q = {1} ∪ E ∪ FE ⊂ G`, the points of the pattern.

## 1. Counting on functional models

**Lemma 1 (functional count).** Let `X` be a finite set with maps `T_f : X -> X` (`f in F`) and
`S_e : X -> X` (`e in E`). The maps are arbitrary: not injective, not group actions, and with no
relations among them. For `w in X`, the *chart* at `w` is the relation `chi_w ⊂ Q × X` containing:
- `(1, w)`;
- `(e, S_e w)` for `e in E`;
- `(fe, S_e T_f w)` for `f in F` and `e in E`.

Call `w` *good* if `chi_w` is the graph of an injective function `Q -> X`. That means two formal
expressions give the same point exactly when they name the same element of `G`. Let `beta` be the
fraction of points that are not good. Then

    log q <= Phi + beta (log|R|/k + log q).

*Proof.* Let `x` be iid uniform on `A^k` over `X`, and put `c(w) = psi((x(S_e w))_(e in E))`. So `c` is a
function of `x`, and

    k|X| log q = H(x) <= H(c) + H(x | c) <= sum_w H(c(w)) + sum_w H(x(w) | (c(T_f w))_(f in F)).

The steps are: `H(x) = H(c) + H(x|c)` because `c` is a function of `x`; then subadditivity; then the
chain rule and dropping conditioning.

Take a good `w`. The sites `S_e w` are distinct, so `c(w)` has the law of `psi(x|_E)`. The variables
`x(w)` and `c(T_f w) = psi((x(S_e T_f w))_e)` are the same functions of iid values at the points
`chi_w(q)`. Those points are distinct, and they coincide exactly as the elements of `Q` do in `G`. So
`(x(w), (c(T_f w))_f)` has the law of `(x(1), y_F)`, and the two local terms of a good `w` sum to
`k Phi`.

At a bad `w`, bound the terms by `log|R|` and `k log q`. Dividing by `k|X|` gives the claim. ∎

**Corollary 1.** Suppose for every `beta > 0` there is a finite set with maps as above and at most a
`beta`-fraction of bad points. Then `Phi >= log q`.

This generalizes Step 3 of Theorem 1 in
`research/artifacts/bernoulli-deficit-witness-localization-2026-09-12.md`. The (F',delta)-permutation
models used there are the special case in which the maps are permutations coming from an
almost-action of `<E ∪ F>`.

**What the maps are forced to do.** Suppose `fe = 1` for some `f in F` and `e in E` (a *read pair*).
At good points `S_e T_f w = w`. A self-map of a finite set that has a left inverse on a
`(1-beta)`-fraction of points is injective on that fraction, hence it is a bijection off an
`O(beta)`-fraction. So read letters act by near-bijections, while letters in no read pair can be
many-to-one. The germ models below use exactly this freedom.

## 2. Theorem A: finite-core height potentials

**Definition.** A *height potential* for the pattern is a pair of functions `a : F -> Z_(>=0)` and
`b : E -> Z_(>=0)` such that the rules

    ht(1) = 0,   ht(e) = b(e),   ht(fe) = a(f) + b(e)

define a function `ht : Q -> Z_(>=0)`. That is, whenever two of these expressions name the same element
of `G`, they give the same value.

The *zero letters* are `Z = a^-1(0) ∪ b^-1(0) ⊂ G`, and the *core* is `K_Z = <Z> <= G`.

In particular:
- a read pair `fe = 1` forces `a(f) = b(e) = 0`, so read letters are zero letters;
- `e = f e'` forces `b(e) = a(f) + b(e')`.

The zero potential is always a height potential, and its core is `<E ∪ F>`.

**Theorem A.** If a configuration admits a height potential with finite core, then `Phi >= log q`,
for every countable group `G`.

*Proof.*

*Setup.*
- Let `K = <E ∪ F>` with word length `|·|` for the generating set `E ∪ F`.
- Put `D = max_(kappa in K_Z) |kappa|` and `lambda = 1 + D`.
- Put `R_r = K_Z · B(r)` for integers `r >= 0`, where `B(r)` is the ball of radius `r` in `K`.
- Put `L = lambda · max_Q ht`.

Two facts hold:
- (i) `z R_r = R_r` for `z in Z`, since `z K_Z = K_Z`.
- (ii) `f R_(r - lambda a(f)) ⊂ R_r` when `a(f) >= 1` and `r >= lambda a(f)`, and likewise for `e` with
  `b(e) >= 1`. Indeed `|f kappa g| <= 1 + D + (r - lambda) <= r` for `kappa in K_Z` and `|g| <= r - lambda`.

Together, for every letter `u` with height `t in {a(u), b(u)}`:

    u R_(r - lambda t) ⊂ R_r.

*The model.* Fix integers `N >= 2` and `M >= 2`. Let `X` be the disjoint union of a junk point `*`
and the levels `X_r = N^(R_r) × [M]^r` for `0 <= r <= L`. For a point `w = (r, c, j)` and a group
element `g`, define the germ at `g` with drop `d` as follows:
- If `r >= d` and `g R_(r-d) ⊂ R_r`, it is `germ_(g,d)(w) = (r - d, c(g ·)|_(R_(r-d)), j|_(first r-d coordinates))`.
- Otherwise it is `*`.

Put `T_f = germ_(f, lambda a(f))`, `S_e = germ_(e, lambda b(e))`, and send `*` to `*`.

*Exact coincidences.* At every level `r >= L`, restriction and truncation compose, so

    S_e T_f (r, c, j) = (r - lambda ht(fe), c(fe ·)|_(R_(r - lambda ht(fe))), j|_(r - lambda ht(fe))).

This depends only on the element `fe` and on `ht(fe)`, and `ht` is a function on `Q`. So products that
are equal in `G` give the same point. A read pair gives `(r, c, j) = w`, and `e = fe'` gives
`S_e w = S_(e') T_f w`. The only level used is `L`, so every point of `X_L` has a well-defined chart
function `chi_w(q) = germ_(q, lambda ht(q))(w)`.

*Injectivity.*
- If `ht(q) != ht(q')`, the images lie in different levels.
- If `ht(q) = ht(q')` and `q != q'`, the germs have first coordinates `c(q)` and `c(q')` at the site
  `1 in R_(L - lambda ht(q))`. These are two distinct sites of `R_L`. For uniform `c` they agree with
  probability `1/N`.

So at most a `|Q|^2/N` fraction of `X_L` is bad.

*Levels.* `|X_r| = N^(|R_r|) M^r` is nondecreasing in `|R_r|` and gains a factor `M` per level. So
`(|X_0| + ... + |X_(L-1)| + 1)/|X| <= 1/(M-1) + 1/M <= 3/M`.

*Conclusion.* The bad fraction satisfies `beta <= 3/M + |Q|^2/N`, which tends to `0` as `M, N -> infinity`.
Corollary 1 gives `Phi >= log q`. ∎

**Remarks.**
1. **Rational heights.** Real nonnegative heights with a given zero set can be replaced by integer
   heights with the same zero set. The consistency conditions are linear with integer coefficients,
   and rational points are dense in the relative interior of each face of the solution cone. So
   Theorem A holds for real potentials.
2. **Uniformity.** The models use no approximation of `G`, `K` or the canonical host. Their maps are
   restriction maps, many-to-one exactly on the positive letters.
3. **Sanity check.** The script `experiments/germ-models-2026-09-17/check_germ_model.py` builds the
   model literally over `Z/2 * Z` with `E = F = {1, z, s}`. That pattern has read degree `m = 2`, core
   `{1, z}`, and heights `a(s) = b(s) = 1`. The script checks the identity
   `S_e T_f = germ(fe)` on every sample, and the chart-injective fraction is at least the union bound.

## 3. What Theorem A adds

**Filter.** Let `(k, E, F, psi)` be a deficit witness over any group. Then every height potential of
its pattern has an infinite core. Equivalently, the zero letters of every consistent nonnegative
grading generate an infinite subgroup.

The read bound (`bernoulli-witness-information-is-bounded-by-code-reads`) gives `m >= 2`, and read
letters are zero letters. Since at most one read pair is `(1, 1)`, the core contains a nontrivial
element `z = f = e^-1`.

**Not subsumed by the landed filters.**
- *Sofic radical* (`sofic-radical-localizes-bernoulli-deficit-witnesses`). On a nonsofic simple host
  it only asks `K` to be nonsofic. Theorem A applies whatever `K` is.
- *Difference subgroup* (`bernoulli-deficit-windows-need-a-non-maximal-difference-subgroup`). It asks
  `<E E^-1>` to be infinite and non-maximal. Theorem A allows positive letters in `E` that generate
  anything.
  - Example: `E = {1, z, s_1, s_2}` and `F = {1, z, t}` with `z^2 = 1`, zero letters `{1, z}`, and
    heights `b(s_i) = a(t) = 1`.
  - Consistency only asks that no element of `{1, z}` (height 0) equals an element of
    `{s_i, z s_i, t, t z}` (height 1) or of `{t s_i}` (height 2).
  - Coincidences inside one height class are unrestricted. So `s_1, s_2, t` may generate any group,
    and `<E E^-1>` may be nonsofic.
- *Read bound.* The read bound is automatic here, since `m >= 2`.

**Canonical hosts.** The canonical host of a height-graded pattern maps onto `Z` through `ht`, and its
defining relators `fe = f'e'` have the vertical/horizontal square form. It is not claimed that these
hosts are always sofic. If they were, Theorem A would follow from the sofic radical theorem applied
to the canonical host. Theorem A needs no such input.

**Limitation (honest).** In a torsion-free group every nontrivial read letter has infinite order. So
the finite-core hypothesis never holds for a pattern with `m >= 2` inside a torsion-free subgroup.
Theorem A constrains only witnesses whose core meets torsion. The amenable version (Section 4) would
remove this restriction.

## 4. Theorem B (OPEN): amenable core

**Statement.** If a configuration admits a height potential whose core `K_Z` is amenable, then
`Phi >= log q`.

**Proposed route.**
- *Setup.* Replace the `K_Z`-invariant regions, which cannot be finite when `K_Z` is infinite, by
  anchored frames. Take a rule, a factor of the iid coloring, that tiles each `K_Z`-coset `pK_Z` meeting
  the relevant region by `(eps, Følner)` tiles.
  - A point of a level is a triple: a tile shape `S`, a position `s in S`, and a coloring of a fixed
    region around the anchor.
  - Zero letters change the position inside the tile.
  - Positive letters drop a level and re-anchor at the tile of the translated position. The level
    drop gives room to recompute that tile.
- *Consistency repair.* A tile is accepted only if every one of its points computes the same tile;
  otherwise the point is a singleton tile.
- *Splitting.* Split the alphabet `A' = A'' × A'''` into a rule component and a separation component.
- *Counting.*
  - Mass transport identifies the uniform count on objects with the Palm measure of the iid tiling.
  - The bad fraction is then bounded by the density of tile boundaries, plus the rule's error
    density, plus the separation collisions of Section 2.

**Missing import (the reason this stays OPEN).**
- *Tiling input.* A finitary form of exact or `eps`-Følner tilings as factors of iid on free p.m.p.
  actions of amenable groups. Sources: Ornstein--Weiss quasi-tilings, or
  Conley--Jackson--Kerr--Marks--Seward--Tucker-Drob, *Følner tilings for actions of amenable groups*,
  Math. Ann. 2018. The finitary form needs block factors of finite radius with small error density.
- *Graph status.* No graph node imports either result verbatim (`bin/cairn search` for Følner tilings
  and quasi-tilings, 2026-09-17).
- *Unverified step.* The tile of a translated position must be computable inside the shrunken region
  after a positive move, for every path of the pattern and uniformly in the level. This has not been
  checked in writing.

## 5. Where germ models die: a nonamenable core

This is the step at which every model of Section 2 type fails. It is an obstruction to the method, not
a proved theorem about `Phi`.

- **Levels as a G-set.** Generalize the levels to any finite index set `Lev`. Level `l` carries a
  finite region `R_l ⊂ K`, and each letter `u` acts by restriction `c -> c(u ·)|_(R_(l u))` into a
  level `l u`, with `u R_(l u) ⊂ R_l`.
- **Return pairs force invariance.** For a read pair `z z^-1 = 1`, Lemma 1 needs the return map to be
  the identity on most points. By Section 1 the restriction must then be a near-bijection
  `N^(R_l) -> N^(R_(l z))`, so `|R_(l z)| = |R_l|`, and hence `z R_(l z) = R_l` on most of the
  measure.
- **Core cocycle.** So along core moves the regions form a cocycle: `R_(l kappa) = kappa^-1 R_l` for
  `kappa in K_Z`, up to an `O(beta)` share of the level measure.
- **Reiter condition.** Level measures proportional to `N^(|R_l|)` weight the levels. Pushing the
  normalized counting measures of the `R_l` forward along the cocycle gives probability measures on
  `K_Z` that are `O(beta)`-almost invariant under each core generator. That is Reiter's condition, so
  `K_Z` is amenable once `beta -> 0` is forced.
- **Alternatives fail.**
  - Absolute Følner frames need amenability of all of `K`.
  - Base-point frames break the canonical representation under mixed coincidences such as
    `z e = f z'`, where a zero letter and a positive letter produce the same point.

**Obstruction statement (method level).**
- *Invariant:* the core `K_Z` of zero-height letters, over all height potentials of the pattern.
- *Where it dies:* at the region-cocycle step, which forces a Reiter measure on `K_Z`.
- *Consequence:* a deficit witness can escape every germ-type count only if every height potential has
  a nonamenable core. The ungraded potential has core `<E ∪ F>`, so the witness group is itself
  nonamenable (already known).
- *Open:* whether a witness exists at all. The first genuinely new constraint would be Theorem B: some
  read letter generates, with the other zero letters, a nonamenable subgroup for every grading.

## 6. Decomposition of the target

A lower bound on a nonsofic simple Kazhdan host through germ models splits into three steps, each of
which can fail separately:
1. **(Established, Theorem A.)** Finite-core potentials give `Phi >= log q`.
2. **(OPEN, Theorem B.)** Amenable-core potentials give `Phi >= log q`. It needs a finitary Følner
   tiling import.
3. **(OPEN, dead for this method.)** Patterns every one of whose potentials has a nonamenable core. Germ
   models cannot certify them (Section 5). They are the remaining candidates for a deficit, and no
   landed method reaches them.

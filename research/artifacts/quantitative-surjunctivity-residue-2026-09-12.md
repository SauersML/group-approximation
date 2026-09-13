# Quantitative surjunctivity: what invariant configurations settle, and the residue that is left

Lane w5-quant-surj, 2026-09-12. Target: `surjunctive-groups-are-quantitatively-surjunctive` (QS), from
`research/artifacts/product-fibre-garden-of-eden-filter-2026-09-12.md` (the fibre artifact).

**Summary.**
- **Section 1.** Restricting to configurations invariant under a normal subgroup settles every
  Garden of Eden pattern that extends to such a configuration. Over `G x K` this makes the single-fibre
  theorem (`strict-product-automata-have-no-single-fibre-garden-of-eden`) true with no hypothesis on `G`.
- **Section 2.** The same restriction gives QS constants. A subshift missing a configuration invariant
  under a normal `N` inherits the constant of `G/N`. So QS needs proof only for proper subshifts that
  contain every configuration invariant under a normal subgroup with sofic quotient. For groups with no
  nontrivial sofic quotient, these are the subshifts containing all constant configurations.
- **Section 3.** The case `j' <= j` of QS is equivalent to surjunctivity, so QS adds exactly linear growth of the
  margin in `n`. In Theorem Q that margin pays for the sofic error rate.
- **Section 4.** Routes that die: compactness, amplification, recoding the output, the clause axiomatization,
  counting on amenable Schreier graphs, and peeling split extensions.
- **Section 5.** `G x F` for finite `F` and `G x Z` are surjunctive exactly when `G` is, so neither is equivalent
  to QS unless the target holds. The candidate "QS iff `G x K` is surjunctive for every sofic `K`" is open in the
  converse direction.

The target stays OPEN. Nothing here proves or refutes it.

## 0. Conventions

- **Automata.** An automaton over a group `Γ` is `tau(x)(g) = mu((x(g m))_(m in M))` for a finite memory `M`.
  It commutes with left translation `(h.x)(g) = x(h^-1 g)`.
- **Invariant configurations.** For `H <= Γ`, `Fix_H` is the set of configurations with `h.x = x` for all
  `h in H`, that is, constant on each right coset `Hg`. For a subshift `Y`, `Per_H(Y) = Y cap Fix_H`.
- **Extension.** A pattern `p` on a finite `E <= Γ` *extends to `Fix_H`* when `p(e) = p(e')` whenever
  `He = He'`. Then some configuration in `Fix_H` restricts to `p` on `E`.
- **QS.** As in the target node. A *QS constant* for a proper subshift `Y <= B^G` is a `delta > 0` such that
  no injective automaton maps `(B^n x D^j)^G` into `Y^n x (D^(j'))^G` when `(j' - j) log|D| < delta n`.

## 1. Invariant configurations over products

**Input (Theorem A(4) of `subgroup-fixed-configuration-transfer-2026-09-12.md`, node
`injective-automata-restrict-to-schreier-graph-automata`).** If `H` is normal in `Γ`, `Γ/H` is
surjunctive and `tau` is injective over `Γ`, then `Fix_H` lies in the image of `tau`.

**Proposition 1.1.** Let `G`, `K` be groups, `N` a normal subgroup of `G`, and `tau` an injective automaton on
`A^(G x K)` with image `X`. If `(G/N) x K` is surjunctive, then `X` contains every configuration `x` with
`x(ng, k) = x(g, k)` for all `n in N`. In particular:
- **(a)** If `K` is surjunctive, `X` contains every configuration that does not depend on the `G`-coordinate.
  So every pattern `p` on a finite `E <= G x K` with `p(g,k) = p(g',k)` whenever both sites lie in `E` is
  realized.
- **(b)** If `K` is surjunctive, every pattern on a single fibre `{g} x F` is realized, whatever `G` is.
- **(c)** If `K` and `G/N` are sofic, every pattern that extends to `Fix_(N x 1)` is realized.

**Proof.**
1. `N x 1` is normal in `G x K` with quotient `(G/N) x K`. Theorem A(4) gives the statement.
2. **Directly.** `Fix_(N x 1)` is translation invariant because `N x 1` is normal, so `tau` maps it into
   itself. Write `x(g,k) = y(gN, k)`. Then `tau(x)(g,k) = mu((y(g g_m N, k k_m))_m)`, an automaton `tau'` over
   `(G/N) x K` with memory `{(g_m N, k_m)}`. It is injective, being a restriction of `tau`, so it is onto, and
   `Fix_(N x 1)` lies in `X`.
3. **(a)** is `N = G`. **(b)** A pattern on `{g} x F` extends to the configuration equal to `p(g,k)` on all of
   `G x {k}` for `k in F`. **(c)** A product of two sofic groups is sofic, hence surjunctive. QED.

**Consequence for the single-fibre theorem.**
- `strict-product-automata-have-no-single-fibre-garden-of-eden` assumes `G` surjunctive and `K` sofic. Its
  conclusion is (b), which needs nothing of `G` and only surjunctivity of `K`. Symmetrically, patterns on
  `G_0 x {k}` are realized whenever `G` is surjunctive, with no hypothesis on `K`.
- So the sofic transplant of Sections 1–2 of the fibre artifact proves a statement whose hypotheses are
  superfluous. The argument is correct (verifier PASS, `w3-vf-positive` Section 16.2), but the filter carries
  no information about `G`. It is not partial progress on `products-with-a-sofic-factor-are-surjunctive`.

**The sharpened filter.** Let `tau` be a strict automaton over `G x K` with `K` sofic, and `p` a Garden of Eden
pattern on `E`. For every normal `N` of `G` with `G/N` sofic, some two sites `(g,k)`, `(g',k)` of `E` have
`g' g^-1 in N` and `p(g,k) != p(g',k)`. With `N = G` the two sites share a `K`-coordinate. The single-fibre
theorem said only that some two sites have different `G`-coordinates.

**Where Theorem Q starts.** In Theorem Q of the fibre artifact, `Y <= (A^(E_K))^G` is the subshift avoiding
`p` at every `g`.
- `Y` misses a point of `Fix_N` iff `p` extends to `Fix_(N x 1)`.
  - **If.** Given an extension `x`, the configuration `w(g)(k) = x(g,k)` for `k in E_K` lies in `Fix_N` and
    shows `p` at `g = 1`.
  - **Only if.** If `w` in `Fix_N` shows `p` at `g`, translate by `g^-1` (normality keeps `w` in `Fix_N`) and
    set `x(g',k) = w(g')(k)` on `G x E_K`, constant elsewhere.
- By (c), such `p` is realized, so it is not a Garden of Eden pattern. So Theorem Q only ever meets subshifts
  `Y` containing `Fix_N` for every normal `N` with sofic quotient. Section 2 shows those are exactly the
  subshifts where the QS constant is not already known.

## 2. Quotient deficits

**Proposition 2.1.** Let `N` be normal in `G`, `B` finite, and `Y <= B^G` a subshift. Let `Y_N <= B^(G/N)` be the
subshift with `Y cap Fix_N = {x : x(g) = y(gN), y in Y_N}`. Suppose `Fix_N` is not contained in `Y`, so that
`Y_N` is proper. Then every QS constant of `Y_N` over `G/N` is a QS constant of `Y` over `G`.

**Proof.**
1. Let `Phi` be an injective automaton over `G` from `(B^n x D^j)^G` into `Y^n x (D^(j'))^G`.
2. `Phi` commutes with translations, so it maps `Fix_N` of the source into `Fix_N` of the target. The latter is
   `Per_N(Y)^n x Fix_N((D^(j'))^G)`.
3. `Y cap Fix_N` is closed and `G`-invariant, and `G` acts on `Fix_N = B^(G/N)` through `G/N`, so `Y_N` is a
   subshift over `G/N`.
4. As in Proposition 1.1, the restriction is an injective automaton over `G/N` from `(B^n x D^j)^(G/N)` into
   `Y_N^n x (D^(j'))^(G/N)`. A QS constant of `Y_N` excludes it once `(j' - j) log|D| < delta n`. QED.

**Corollary 2.2 (constant configurations, every group).** Let `c_Y` be the number of constant configurations
in `Y`. If `c_Y < |B|`, then `log(|B| / c_Y)` is a QS constant for `Y`, and no injective automaton exists at all
when `c_Y = 0`.

**Proof.** Take `N = G` and count directly. The source has `|B|^n |D|^j` constant configurations and the
target has `c_Y^n |D|^(j')`. An injective equivariant map sends constants injectively to constants, so
`|B|^n |D|^j <= c_Y^n |D|^(j')`, that is, `(j' - j) log|D| >= n log(|B| / c_Y)`. QED.

**Corollary 2.3 (periodic points).** Let `H <= G` have finite index `m`, not necessarily normal. If
`|Per_H(Y)| < |B|^m`, then `log(|B|^m / |Per_H(Y)|) / m` is a QS constant for `Y`.

**Proof.** `Phi` commutes with translation by `H`, so it maps `Fix_H` into `Fix_H`. The source has
`(|B|^n |D|^j)^m` such configurations, and the target has `|Per_H(Y)|^n |D|^(j' m)`. Compare. QED.

**Corollary 2.4 (residually finite groups, by periodic points).** Let `G` be residually finite, and let `Y`
miss a pattern `r` on a finite `W <= G`. Then `-log(1 - |B|^(-|W|)) / |W|^2` is a QS constant for `Y`.

**Proof.**
1. Choose a normal `H` of finite index `m` such that `W` maps injectively to `G/H`. Read as `y in B^(G/H)`, every
   point of `Per_H(Y)` avoids the image of `r` on every window `gW` in `G/H`, since `y` showing it at `gW` makes
   the periodic configuration show `r` at `g`.
2. Each point lies in at most `|W|` windows, so each window meets at most `|W|^2` windows, itself included.
   Greedy selection gives at least `m / |W|^2` disjoint windows.
3. The constraints on disjoint windows are independent, so
   `|Per_H(Y)| <= |B|^m (1 - |B|^(-|W|))^(m / |W|^2)`.
4. Corollary 2.3 finishes. QED.

This is the sofic constant of the fibre artifact, up to `|W|^2 + 1` in place of `|W|^2`, proved with no sofic
models.

**Corollary 2.5 (the residue).** Let `Nsof(G)` be the set of normal subgroups `N` with `G/N` sofic. Then `G` is QS
iff every proper subshift `Y <= B^G` that contains `Fix_N` for every `N in Nsof(G)` has a QS constant.

**Proof.** If a proper `Y` misses a point of `Fix_N` with `G/N` sofic, Proposition 2.1 and the sofic count
(Section 3 of the fibre artifact, verified as prose in `w3-vf-positive` Section 16.3) give a constant. The
converse is the definition. QED.

**Import-free form.** Proposition 2.1 alone gives Corollary 2.5 with `Nsof(G)` replaced by the normal subgroups
`N` with `G/N` QS. The sofic count enters only to show that sofic quotients qualify.

**What the residue is.**
- **Sofic `G`.** `1 in Nsof(G)` and `Fix_1 = B^G`, so the residue is empty.
- **No nontrivial sofic quotient.** `Nsof(G) = {G}`, and the residue is the proper subshifts containing all
  `|B|` constant configurations. This covers finitely generated simple nonsofic groups, the hosts to which
  `gottschalk-reduces-to-fg-simple-kazhdan-groups` reduces the conjecture.
- **Everything else.** Restriction and fixed-point counting give no constant on the residue. The deficit
  there must come from the nonsofic part of `G`.

## 3. Zero margin

**Proposition 3.1.** For every group `G`, surjunctivity is equivalent to the case `j' <= j` of QS. That is, for
all `B`, proper `Y <= B^G`, `D`, `n >= 1` and `j >= j' >= 0`, no injective automaton maps `(B^n x D^j)^G` into
`Y^n x (D^(j'))^G`.

**Proof.**
- **The case gives surjunctivity.** If `tau` on `B^G` is injective and not onto, its image `Y` is a proper
  subshift, and `tau` is a map of the excluded kind with `n = 1` and `j = j' = 0`.
- **Surjunctivity gives the case.** Let `Phi` be such a map. Follow it by an injective symbol map
  `D^(j') -> D^j` on the last track. The composite is an injective automaton on `(B^n x D^j)^G` whose first
  track lies in `Y`, so it is not onto. QED.

**Remarks.**
- **One pattern suffices.** Every proper `Y` lies in the subshift `Y_r` avoiding one pattern `r` that `Y` misses,
  and a constant for `Y_r` is one for `Y`.
- **What QS adds.** For `|D| >= 2`, Proposition 3.1 forces `(j' - j) log|D| >= log 2` for every map of this shape.
  That margin is bounded below independently of `n`. QS asks for a margin growing linearly in `n`.

**Where the margin comes from in Theorem Q.**
- The fibre device over `G x K` stores the input on the `epsilon |V|` bad points of a sofic model `V` of `K`.
  That stored input is the extra full-shift track, against a number of copies of `Y` proportional to `|V|`.
- When `K` has exact finite models there are no bad points and `j' = j`. Proposition 3.1 then closes the
  argument, which is the content of `products-with-lef-permanence-closure-factors-are-surjunctive`.
- So QS is needed exactly to absorb the sofic error rate. Since `epsilon` can be taken as small as wanted, any
  positive `delta_Y` suffices.

## 4. Routes that die

### 4.1 Compactness and ultraproducts

Suppose `G` is surjunctive and `Y` has no QS constant. Then there are injective automata `Phi_i` from
`(B^(n_i) x D_i^(j_i))^G` into `Y^(n_i) x (D_i^(j'_i))^G` with margins `m_i = (j'_i - j_i) log|D_i|` and
`m_i / n_i -> 0`.
- **`n_i -> infinity`.** By Proposition 3.1 each `m_i >= log 2`. If `n_i` stayed bounded along a subsequence,
  `m_i / n_i` would stay bounded below.
- **No limit automaton.** The alphabets grow without bound, so a limit is not an automaton over a finite
  alphabet.
- **The limit statement is true.** A limit with infinitely many tracks has the form of an injective equivariant
  map `(B^N)^G -> Y^N`. Such maps exist over every group.
  - Take `B = {0, 1, 2}` and `Y = {0,1}^G`, a proper subshift.
  - Encode each symbol of `B` as two bits and send track `i` to tracks `2i` and `2i + 1`.
  - The map is injective, equivariant and coordinatewise.
- **Where it stops.** No contradiction can come from the limit, so any proof must keep `n` finite and
  quantitative.

### 4.2 Amplification

- **Products.** The `m`-fold product of `Phi` has parameters `(m n, m j, m j')` and the same ratio.
- **Composition.** A second map of the same shape, from `(B^n x D^(j'))^G` into `Y^n x (D^(j''))^G`, restricts to
  the image of `Phi`. The composite keeps `n` and adds the margins.
- **Where it stops.** Neither operation turns a small positive ratio into a nonpositive margin, which is all that
  surjunctivity forbids.

### 4.3 Recoding the output

The tempting contradiction follows `Phi` by an injective automaton `Psi`, defined on a subshift containing the
image of `Phi`, into a full shift `C^G` with `|C| < |B|^n |D|^j`.
- **No such `Psi` exists, over any group.** `Phi` maps the `|B|^n |D|^j` constant configurations of the source
  injectively to constant configurations. `Psi` must map those injectively to the `|C|` constant configurations
  of `C^G`.
- **Where it stops.** The deficit cannot be converted into a smaller alphabet. A proof has to count invariant
  configurations, as in Section 2, or use finite models. Over `Z` this is the periodic-point condition of
  Krieger's embedding theorem.

### 4.4 Logic

- **Certificates.**
  - An injective automaton has a left inverse automaton.
  - The condition "every `Y`-track of the image avoids `r`" is a finite condition on the local rule.
  - So a failure of QS for `Y_r` at ratio below `delta` is certified by a finite piece of the multiplication
    table of `G`, two local rules on a ball, the identity `sigma Phi = id` on that ball, and the avoidance of `r`.
- **Clauses.** Surjunctivity forbids the certificates of ratio `<= 0` (Proposition 3.1), a set of rectangle
  clauses. QS for `Y_r` says that for some `delta` all certificates of ratio below `delta` are forbidden, and the
  set of clauses depends on the unknown `delta`.
- **Where it stops.** A derivation would have to turn a certificate of small positive ratio into one of ratio
  `<= 0` on a larger ball, which is the recoding of Section 4.3. Compactness over the clauses gives
  certificates of vanishing ratio on growing balls, which is Section 4.1.

### 4.5 Counting on amenable Schreier graphs

Section 2 counts configurations invariant under normal subgroups. Theorem A applies to every subgroup `H`.
`Phi` restricts to an injective graph automaton on the Schreier graph `S` of `H`, with a left inverse (Theorem
A(2)).
- **The count.** Let `S` have Følner sets `F_k`.
  - The input on the interior of `F_k` is determined by the output on `F_k`.
  - An output track avoids the image of `r` on every window `vW` at which `W` maps injectively.
  - If those vertices have density at least `c_W > 0` in the `F_k`, the argument of Corollary 2.4 gives the
    constant `-c_W log(1 - |B|^(-|W|)) / |W|^2` for `Y_r`.
- **It reaches only sofic groups.**
  - Take `W = {1, s}` with `s != 1`. Positive density of `W`-injective vertices says that `s` moves a fraction
    at least `c_W` of the vertices of `F_k`.
  - Restricting the action to `F_k` and patching the boundary gives almost-actions of `G` whose fixed-point
    fractions stay below `1 - c_W + o(1)`.
  - Tensor powers push these fractions to `0`. So `G` is sofic, where the constant is already known.
- **Where it stops.** For a nonsofic `G`, every amenable Schreier graph has density `0` for some `W`, and the
  count gives nothing.

### 4.6 Peeling split extensions

Theorem 0 of `research/artifacts/finitary-split-extension-surjunctivity-2026-09-11.md` proves `W = N ⋊ G`
surjunctive from `G` by peeling strata. Carrying a QS constant from `G` to `W` through that proof meets three
obstacles.
- **Equivariance.** The transplants `tau_U` over `G`, with alphabet `B^(Q_U)` and cocycle `c^U_m(g)`, commute
  only with the stabilizer `G_U`. QS of `G` concerns maps commuting with all of `G`.
- **The constraint is not carried.**
  - The induction proves bijectivity of stages `rho_U`, built from `tau_U` and inverses of earlier stages.
  - It applies surjunctivity of `G_U` on a region that is a finite union of right cosets of `G_U`.
  - The condition that output tracks lie in the transplanted `Y` holds for `tau_S`, not for these composites,
    so no stage sees a proper subshift.
- **Scale.** Even for one stage, `n` copies of `Y` over `W` become `n` copies of a subshift over the base with
  alphabet `B^(Q_U)`, and the margin is multiplied by `|Q_U|`. QS of the base gives some constant for each
  subshift, with no lower bound in terms of `|Q_U|`.

This matches the note on `surjunctive-groups-are-uniformly-quantitatively-surjunctive`: marked-site peeling
separates finite quotients stratum by stratum and carries no deficit.

## 5. The equivalences asked about

**Proposition 5.1.**
1. For finite `F`, `G x F` is surjunctive iff `G` is.
2. If `G` is surjunctive, so is `G x Z`.

So neither "`G x F` surjunctive for all finite `F`" nor "`G x Z` surjunctive" is equivalent to QS, unless every
surjunctive group is QS, which is the target.

**Proof.**
1. An automaton over `G x F` on `A^(G x F)` is an automaton over `G` on `(A^F)^G`, with memory the projection
   of the old one. Conversely `G` is a subgroup of `G x F`, and surjunctivity passes to subgroups by induction of
   automata.
2. `Z` is LEF, and `products-with-lef-permanence-closure-factors-are-surjunctive` puts every LEF group in
   `{K : G x K surjunctive}`.
3. Both properties are equivalent to surjunctivity, and QS implies surjunctivity. So an equivalence of either
   with QS says that every surjunctive group is QS. QED.

**The candidate "QS iff `G x K` is surjunctive for every sofic `K`".**
- **Forward.** This is Theorem Q.
- **Converse.** It needs a construction from maps over `G` with small positive margin to strict automata over
  `G x K`, the reverse of the fibre device. None is known. Its `K` could not lie in the LEF permanence closure,
  since those products are surjunctive for every surjunctive `G`.
- **Relation to the target.**
  - If the target holds, so does the equivalence: `G x K` surjunctive makes the subgroup `G` surjunctive, hence QS.
  - If the equivalence holds, the target is equivalent to `products-with-a-sofic-factor-are-surjunctive`.

**No refutation.** A counterexample to the target needs a surjunctive nonsofic group and a proper subshift in
its residue with no constant. Section 4 gives no mechanism producing maps of vanishing ratio over any group, so
no candidate is at hand.

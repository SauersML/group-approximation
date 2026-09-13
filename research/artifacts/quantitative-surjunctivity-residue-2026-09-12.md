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
- **Sections 3–5** (landed separately): zero margin, routes that die, and the equivalences asked about.

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

**What the residue is.**
- **Sofic `G`.** `1 in Nsof(G)` and `Fix_1 = B^G`, so the residue is empty.
- **No nontrivial sofic quotient.** `Nsof(G) = {G}`, and the residue is the proper subshifts containing all
  `|B|` constant configurations. This covers finitely generated simple nonsofic groups, the hosts to which
  `gottschalk-reduces-to-fg-simple-kazhdan-groups` reduces the conjecture.
- **Everything else.** Restriction and fixed-point counting give no constant on the residue. The deficit
  there must come from the nonsofic part of `G`.

# Kari-type block decompositions and regrouping for stable formalizability

Lane `gk-fz-kari` (family F), 2026-09-12. Supports:
- `reversible-automata-over-integers-are-block-permutation-words` (Section 3, open, imported);
- `reversible-binary-automata-over-integers-virtually-formalizable` (Section 3, open);
- the route `kari-words-give-virtual-formalizability-over-integers`.

The live family targets are:
- `injective-binary-automata-are-stably-formalizable` (identity tracks);
- `injective-automata-over-fg-groups-are-virtually-formalizable` (regrouping along a finite-index subgroup of the finitely generated memory group, with payoff route `virtual-formalizability-reduces-surjunctivity-to-kaplansky`).

The unstabilized form is refuted (`binary-left-inverse-pairs-need-not-be-formalizable`).

This artifact asks what block and partition decompositions contribute. The general marker-flip
case and the regrouping payoff were landed by gk-fz-decompose while this lane drafted; Sections 1–2
re-derive them independently and cite those nodes, and no duplicate node is landed.

## 1. Bookkeeping: formal identities under composition, memory, tracks and regrouping

Throughout, `k = F_p` with `p` prime. A pair `(tau, sigma)` with polynomial representatives `mu`,
`nu` is formal when the substituted composite `nu o mu` is the coordinate vector of `X_(e,.)` as
polynomials, without using `x^p = x`.

- **Composition.** Formal pairs compose: `(tau2 tau1, sigma1 sigma2)` is formal, by associativity of
  substitution. This is recorded on `structurally-reversible-automata-are-formalizable`.
- **Memory.** Enlarging a memory adds unused variables and changes no polynomial identity.
- **Identity tracks.** If `(tau, sigma)` is formal with representatives `mu`, `nu`, then
  `(tau x id_m, sigma x id_m)` is formal with representatives `(mu, Y)` and `(nu, Y)`.
- **Regrouping.** Let `H` have finite index with right transversal `C`. The map
  `x -> ((x(hc))_(c in C))_(h in H)` is an `H`-equivariant bijection `(k^n)^G -> (k^(n|C|))^H` and
  renames variables bijectively. So a `G`-equivariant formal pair stays formal over `H`. The converse
  fails: an `H`-equivariant representative need not be the translate of one polynomial over `G`.
  Compare `subset-stable-marker-flips-are-virtually-formalizable` with
  `binary-left-inverse-pairs-need-not-be-formalizable`.

## 2. Independent re-derivations of landed sibling results

**2.1 Payoff after regrouping** (`virtual-formalizability-reduces-surjunctivity-to-kaplansky`).
Suppose `H` has finite index and the regrouped pair is formal over `H` at alphabet `k^N`.
- `M_N(k[H])` is a unital subring of `M_N(k[G])`, hence directly finite.
- `formal-polynomial-strict-pairs-need-unstable-linearization` over `H` makes the regrouped automaton
  bijective.
- Regrouping is a bijection of configuration spaces, so the automaton is bijective over `G`.

This agrees with the landed route, which first localizes to the finitely generated memory subgroup.

**2.2 Marker flips** (`subset-stable-marker-flips-are-virtually-formalizable`). Let `H` be normal of
finite index and avoid the marker window `S`. For `g = hc` and `s in S`, `gs` lies in `Hc` iff `csc^(-1)`
lies in `H`, iff `s` lies in `H`, by normality. So the flip of the class `Hc` reads only other classes:
over `H` it is a track shear. Flipping class by class gives `tau` when flips never change markers.
Same argument as the landed node.

**2.3 Partitioned words over `G` itself, no regrouping.** A finite composition of the following maps
is a formal two-sided pair with the reversed composition, `G`-equivariantly:
- sitewise permutations of `F_p^n`, when `n >= 2` or `p <= 3`
  (`sitewise-pairs-over-prime-fields-are-stably-formalizable`, Theorem 4.1 part 1;
  `tame-maps-induce-every-permutation-of-prime-field-cubes`);
- linear automata with a linear two-sided inverse, for instance translating single tracks by fixed
  group elements;
- track shears, reading coordinates other than the one written
  (`structurally-reversible-automata-are-formalizable`).

This is a corollary of the landed nodes, so no separate claim is landed. Classical partitioned
(Margolus-type) automata, translating some tracks and then applying a sitewise permutation, are in
this class over `G` itself. The one-track rigidity of
`formalizable-binary-pairs-over-biorderable-groups-are-affine` is the case `n = 1`.

**2.4 What decompositions cannot do.** A formal two-sided pair represents a bijection. So no word of
formally invertible pieces represents `tau x id` for a strict `tau`, and for strict automata a formal
left-inverse pair needs a formally non-invertible layer. This agrees with
`formalizable-left-inverse-iff-clean-shear-dilation` and with gk-free-neg's Attempts entry on
`injective-binary-automata-are-stably-formalizable`: any realization of `tau x id` is formally dirty
at `y = 0`.

## 3. Over the integers: Kari-type decompositions

*Trust note.* Kari, "Representation of reversible cellular automata with block permutations",
Math. Systems Theory 29 (1996), states that every reversible one-dimensional automaton is, after
grouping cells into blocks, a translation composed with block permutations along two partitions into
intervals that are translates of each other. I did not read the source verbatim here. No established
node uses it; it is the open claim `reversible-automata-over-integers-are-block-permutation-words`.

**Partial derivation: the partition lemma.** Take neighbourhoods `{0,1}` and `{−1,0}`. Let
`F(x)_i = f(x_i, x_(i+1))` be bijective with inverse `G(y)_i = g(y_(i−1), y_i)`. Put `rho(a) = f(a, .)`
and `lambda(b) = f(., b)` in `A^A`, `L = lambda(A)`, `R = rho(A)`.
- **(F1)** `f(a, b) = h(rho(a), lambda(b))` for a well-defined `h : R x L -> A`. If `rho(a) = rho(a')`
  and `lambda(b) = lambda(b')`, then
  `f(a, b) = f(a', b) = lambda(b)(a') = lambda(b')(a') = f(a', b')`.
- **(F2)** `a -> (lambda(a), rho(a))` is injective, since `a = g(f(c, a), f(a, d)) = g(lambda(a)(c), rho(a)(d))`
  for any `c`, `d`.
- **Missing:** the counting step `|A| = |L| |R|`, which makes both maps bijective. Granting it,
  `F = h o (translate the L-coordinate one cell) o (lambda, rho)` is a partitioned word (Section 2.3)
  on the alphabet `L x R`.

*Granting the import.* Group along `mZ`, refining so both partitions are unions of blocks:
- the aligned block permutation is sitewise on blocks of at least two bits (a one-bit sitewise
  permutation is affine anyway);
- the offset block permutation is conjugate to an aligned one by a regrouped translation, which is
  linear with a linear inverse;
- the final translation is linear too.

Section 2.3 over the group `mZ` then makes every reversible binary automaton over `Z` formalizable
after regrouping (route `kari-words-give-virtual-formalizability-over-integers`). This is the
bijective special case, over `Z`, of `injective-automata-over-fg-groups-are-virtually-formalizable`.
It is a calibration only, since `Z` is amenable.

*Why grouping enters.* F1, F2 and Section 2.3 are `G`-equivariant. But reducing a general radius to the
neighbourhoods `{0,1}` / `{−1,0}` groups cells into blocks, that is, passes to `mZ`. With identity tracks
and `Z`-equivariant representatives no radius reduction is known. That is the one-ancilla test on
`injective-binary-automata-are-stably-formalizable`.

## 4. Z^2, other groups, and hosts without finite quotients

- **`Z^d` and residually finite memory groups.** Block methods reach marker flips (Section 2.2) and
  partitioned words along finite-index subgroups. I did not settle whether every reversible automaton
  over `Z^2` is a block-permutation word. Higher-dimensional representation results (Durand-Lose) were
  not read here, and no node uses them.
- **Memory groups with no proper finite-index subgroup** (`R^x`, `V`, finitely generated simple
  Kazhdan hosts). Regrouping is unavailable, so block and partition methods reach exactly the
  `G`-equivariant partitioned words. All of them are bijective (Section 2.4).
- **Consequence for the stable target.** On the hosts where the Kaplansky payoff matters,
  decompositions add nothing for strict automata. What is needed there is a representative of
  `tau x id` with a formal left inverse that is not two-sided, which no decomposition supplies.

## 5. Status

- **Landed here:** the open import `reversible-automata-over-integers-are-block-permutation-words`,
  the open calibration `reversible-binary-automata-over-integers-virtually-formalizable`, and the route
  between them.
- **Re-derived, not duplicated:** the sibling nodes of Sections 2.1–2.3.
- **Open:** the counting step of the partition lemma, the `Z^2` block question, and the stable target
  for strict automata on hosts without finite quotients.

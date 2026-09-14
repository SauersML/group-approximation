# gk3-binary-descent-2: universal binary descent, round 2 (2026-09-14)

Target: `some-nonsurjunctive-group-gives-a-binary-one` (OPEN). If some group carries an injective,
non-surjective cellular automaton (a *strict* automaton) over some finite alphabet, then some group carries
one over two symbols. With `every-group-is-binary-surjunctive` this is Gottschalk's conjecture
(`gottschalk-via-universal-binary-descent`).

State at the start: `passive-fixing-injective-automata-are-surjective` and
`ec-groups-share-the-nonsurjunctive-alphabet-sizes` (both ESTABLISHED, 0a2fdc1cc), and the fiber analysis
over `G × F` in `research/artifacts/gk3-alphabet-descent-2026-09-14.md`, Section 4.

**Verdict.** The target stays OPEN. Landed:
- `modular-matrix-failures-descend-to-scalars-over-g-times-p` (ESTABLISHED): binary descent holds for every
  strict automaton that is linear over a field of characteristic two, with host `G × P`, `|P|` odd.
- `binary-shifts-over-odd-fibers-split-off-the-augmentation-shift` (ESTABLISHED): over odd fibers the two
  constant fibers collapse to one reserved symbol, the zero vector of `R_q = F_2[x]/(Φ_q)`, and a
  `ζ`-homogeneous strict automaton on `R_q^G` suffices.

Nothing is independently reviewed.

## 1. Notation

- `NS(G)`: the alphabet sizes `n >= 2` at which `G` carries a strict automaton; `NS_all = ∪_G NS(G)`.
- An automaton is a continuous `G`-equivariant self-map of `A^G`; by Curtis–Hedlund–Lyndon it has a finite
  memory and a local rule.

## 2. Compression criterion (recorded here only)

**Lemma.** Let `κ: A^G → B^G` be injective, continuous and `G`-equivariant, with `|A| > |B| >= 1`. Then every
size `c` with `|B| <= c <= |A|` and `c >= 2` lies in `NS(G)`.

*Proof.* Identify `B ⊆ C ⊆ A` with `|C| = c`, and let `ι: C^G → A^G` and `j: B^G → C^G` be the symbol
inclusions. `Φ = j ∘ κ ∘ ι` is an injective automaton on `C^G`.
- If `c > |B|`, its image lies in `B^G ⊊ C^G`.
- If `c = |B|`, its image is `κ(B^G)`. This is a proper subset of `κ(A^G) ⊆ B^G`, because `κ` is injective
  and `B^G ⊊ A^G`. ∎

**Consequence.** `2 ∈ NS_all` as soon as some group has an injective automaton from a full shift on at
least three symbols into the binary full shift. The measurable form of such a compression is
`measurable-alphabet-compression-over-leavitt-units` (OPEN). The route
`alphabet-conjugacy-invariance-from-gottschalk` is the special case of a conjugacy.

This is a sufficient condition, stronger than the target, so it is not landed as a route.

## 3. Linear witnesses descend: `modular-matrix-failures-descend-to-scalars-over-g-times-p`

**Statement.** `M_n(F_p[G])` is not directly finite for some `n` iff `F_p[G × P]` is not directly finite for
some finite `P` with `p ∤ |P|`. Take `P = (C_q)^r ⋊ C_r` with primes `q, r != p` and `r >= n`.

**Idea.**
- The monomial representation of `P` (diagonal `q`-th roots of unity, cyclic permutation) spans `M_r(F)`
  over `F_p`, with `F = F_p(ζ)`.
- By Maschke, `M_r(F)` is a ring direct factor of `F_p[P]`, so `M_r(F[G])` is a direct factor of
  `F_p[G × P]`.
- A one-sided inverse in `M_n(F_p[G])` becomes one in `M_r(F[G])` by padding and scalar extension, hence one
  in `F_p[G × P]`.
- The converse restricts scalars along the Wedderburn factors of `F_p[P]`.

**Automaton form.** Through `linear-strict-pairs-are-transposes-of-post-surjective-automata`: `G` has an
`F_p`-linear strict automaton over some `F_p^n` iff some `G × P` (`p ∤ |P|`) has an `F_p`-linear strict
automaton over `F_p`. For `p = 2` the latter is binary.

**What it settles for the target.**
- **Linear witnesses.** Every strict automaton that is linear over a field of characteristic two gives a
  binary strict automaton over `G × P`.
- **Homomorphic witnesses.** With `homomorphic-solvable-alphabet-ca-reduce-to-stable-finiteness`, a strict
  automaton over a finite 2-group alphabet `K` that is a group homomorphism fails stable finiteness of
  `F_2[G]`, and so descends to two symbols over some `G × P`.
- **The linear gates.** For these witnesses the host is preserved up to a finite direct factor, which the
  universal tester `kaplansky-direct-stable-finiteness-one-universal-group` does not give.

**Calibration** (local, exact; script `research/artifacts/gk3-binary-descent-2-2026-09-14-calib.py`).
- `p = 2`, `q = r = 3`, `F = F_4`: `|ρ(P)| = 81`, and the `F_2`-span of `ρ(P)` has dimension 18 =
  `dim_(F_2) M_3(F_4)`.
- Negative control `ζ -> 1`: the image is the 3 permutation matrices, which span dimension 3. The surjectivity
  step uses `ζ != 1`.

## 4. Odd fibers: `binary-shifts-over-odd-fibers-split-off-the-augmentation-shift`

**Statement.** For `|P|` odd, `{0,1}^(G×P) ≅ {0,1}^G × I_P^G` equivariantly, by fiber parity plus augmentation
part. A `P`-equivariant strict automaton on `I_P^G` gives a binary strict automaton over `G × P`. The only
fixed symbol of `I_P` is `0`. For `P = C_q`, `I_P = R_q = F_2[x]/(Φ_q)` with the generator acting by
`ζ = [x]`, so equivariance is `f(ζu) = ζ f(u)`.

**What changes against the Section 4 analysis of gk3-alphabet-descent.**
- There the fiber alphabet `{0,1}^P` has two fixed symbols `0^P`, `1^P` and `N = (2^q - 2)/q` free orbits.
- Here the parity factor `{0,1}^G` may be left untouched (`β = id`). The designer faces one reserved symbol,
  `0 ∈ R_q`, and `(2^(q-1) - 1)/q` free orbits.
- The reserved symbol now has additive meaning: `R_q^G` is an `F_2`-vector space and ζ-homogeneous rules
  include every `R_q`-linear rule.
- The passive barrier still applies with passive set `{0}`: a strict `θ` must write nonzero at some `0`-site
  or `0` at some nonzero site.

**Calibration** (same script). For `G = C_2`, `P = C_3`: `Θ` is a bijection on all 64 configurations, lands
in the augmentation module, and intertwines all 6 translations. `I_(C_3)` has the single fixed vector `0`.

## 5. Phase-borrowing between relays (direction 1 of the previous artifact)

Setting as in gk3-alphabet-descent Section 4.3: a strict pair `(μ, ν)` over `[k]` realized with memories
`M` and `S`, symbols carried by free orbits of `{0,1}^P`, `|P| = q` prime.

- **Phases are spent.** An equivariant rule assigns to each output fiber a phase that is a fixed offset of
  the phase of one input fiber (normalize on the first non-constant input). In the Section 4.3 design every
  output site `g` is relay 1 for exactly one demanded cell `g s_1^(-1)`, whose phase it transports. So no
  output phase is free.
- **Relative-phase tags must be coboundaries.** Suppose relay `s_j` of the demanded cell `d` stored a tag as
  the phase of `d s_j` relative to `d s_1`. Writing `π` for the output phases, the constraints are
  `π(d s_j) - π(d s_1) = tag_j(d)` for all `d` and `j`.
  - These determine `π` along the Cayley graph of `⟨S⟩`. They are consistent only if the tags sum to zero
    around every cycle, i.e. `tag` is a coboundary, which arbitrary tag data is not.
  - Relative phases therefore add at most one `Z/q`-value per output site, which is the output's own phase,
    already spent above.
- **Count.** Per site, the capacity is `(orbit, phase)` on both sides, and the Section 4.3 shortfall
  `k(N - k + 3) > N` in orbit indices is unchanged.

This is an analysis of the relay design, not a theorem about `G × P`.

## 6. Overgroups with outer action (direction 2)

Let `L = G ⋊ P` with `P` acting on `G` by automorphisms `α`. The fibers `{g} × P` are still the blocks of
`L`-translation, and `(1,u)` sends the fiber over `g` to the fiber over `α_u(g)`, translating within it.
- The split of Section 4 applies verbatim: `{0,1}^L ≅ {0,1}^G × I_P^G`, with `P` acting on sites by `α` and
  on `I_P` symbolwise.
- The symbolwise action on each fiber is still left translation on `{0,1}^P`, so the orbit structure of the
  fiber alphabet and the fixed symbol `0` are unchanged.
- An outer action moves sites, but equivariance and the passive barrier are sitewise, so the counts of
  Section 5 are not improved. No gain.

## 7. Group change beyond finite index (direction 3)

- By `ec-groups-share-the-nonsurjunctive-alphabet-sizes` the target is: for one existentially closed `K`,
  `NS(K) != ∅ ⇒ 2 ∈ NS(K)`. By `surjunctivity-is-axiomatized-by-rectangle-clauses`, strict data at a fixed
  size is a finite table plus rules, so the target is a purely combinatorial transformation of finite strict
  data at size `k` into finite strict data at size 2, in some realizable table. No such transformation was
  found.
- **Compression.** By Section 2 it would suffice to build, over some group, an injective automaton from a
  larger full shift into `{0,1}^L`. Over sofic groups no such map exists, since it would give strictness
  there. So any construction must use the given strict pair as a black box and exploit its room: the image
  of `τ` misses a finite pattern.
- **Stamping a missing pattern.** The natural attempt stamps the missing pattern `w` of `τ` to mark
  reserved sites. It overwrites exactly the `τ`-values the decoder `ν` needs at the stamped window, so it
  fails on injectivity. One missing pattern per window stores one bit of marking, and the overwritten
  window needs `|W| log k` bits.

## 8. Exact gap

`some-nonsurjunctive-group-gives-a-binary-one` stays OPEN.
- **Proved cases.** Strict witnesses that are linear over a field of characteristic two, and homomorphic
  witnesses over 2-group alphabets.
- **Sufficient condition.** A `ζ`-homogeneous strict automaton on `R_q^G` over some group `G`, for some odd
  prime `q`. Equivalently, `P`-equivariant strictness on the augmentation shift.
  - It must write on `0`-sites or produce `0` at nonzero sites (passive barrier).
  - For `q = 3` it is a strict automaton on `F_4^G` commuting with multiplication by a primitive cube root of
    unity.
- **Not covered.**
  - Nonlinear witnesses, in particular any strict automaton over an alphabet whose size has an odd prime
    factor and no linear structure over `F_2`.
  - Even for `F_p`-linear witnesses with `p` odd, the descent lands at size `p`, not 2.
- **Next tests.**
  1. Can a `ζ`-homogeneous automaton on `R_3^G = F_4^G` absorb the `0`-symbol by an `F_4`-linear correction
     term supported on `0`-sites? Linear corrections are automatically homogeneous.
  2. Does `homomorphic-solvable-alphabet-ca-reduce-to-stable-finiteness` extend to rules that are
     homomorphisms on a sub-alphabet and `ζ`-homogeneous elsewhere?

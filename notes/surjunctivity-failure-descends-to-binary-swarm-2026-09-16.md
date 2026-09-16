# Binary descent of surjunctivity failure: swarm attack, 2026-09-16

Target: `surjunctivity-failure-descends-to-binary-alphabet` (OPEN). Agent
`swarm-surjunctivity-failure-descends`. Hole worked: the target itself (locked).

## 0. Setup and conventions

- `K` a group, `A` a finite alphabet, `(h.x)(g) = x(h^{-1} g)`. An automaton is a continuous
  `K`-equivariant self-map of `A^K`; `Phi(x)(g) = f( (x(gn))_{n in N} )` for a finite memory `N`.
- Strict = injective and not surjective. `NS(K)` = sizes `n >= 2` carrying a strict automaton.
- Recorded facts used: `NS(H) ⊆ NS(K)` for `H <= K`; `NS(K)` closed under multiples
  (`strict-rule-pairs-pass-to-product-alphabets`); `full-shifts-with-different-alphabets-are-not-conjugate`
  (ESTABLISHED), which contains: if `|A| > |B|` there is no equivariant injection `A^K -> B^K`,
  continuous or not (constants argument).

Outcome: no resolution. One correction to recorded attempts (Section 1), a replacement criterion and
where it dies (Section 2), and several dead ends located precisely (Sections 3-6). No research node
was added: the candidate barrier I proved (Section 5) is already landed.

## 1. Correction: every coding/compression criterion recorded for this target is vacuous

**Fact.** Let `|A| >= 3`. There is no `K`-equivariant injection `e: A^K -> {0,1}^K`, for any group `K`.

*Proof.* A configuration fixed by all of `K` is constant: if `g.x = x` then
`x(g) = (g.x)(g) = x(g^{-1}g) = x(1)`. So `Fix_K(A^K)` has `|A|` points and
`Fix_K({0,1}^K)` has 2. If `h.x = x` for all `h`, then `h.e(x) = e(h.x) = e(x)`, so `e` maps
`Fix_K(A^K)` injectively into `Fix_K({0,1}^K)`, forcing `|A| <= 2`. ∎

This is the landed `full-shifts-with-different-alphabets-are-not-conjugate`, stated for injections.

**Consequences for recorded attempts.**
1. Target, Attempts bullet "Reformulation and the marker obstruction (w3-alphabet)". It says descent
   is *equivalent* to an equivariant continuous injection `e: A^K -> {0,1}^K` with a retraction and
   clopen image. By the Fact no such `e` exists when `|A| >= 3`, and for `|A| = 2` it is trivial. So:
   - the sufficient condition never applies;
   - "equivalent" is false: for every surjunctive `K` (for instance `K = Z`) descent holds vacuously,
     while no coding exists;
   - the marker discussion is moot. Block coding over a finite `H` fails at the constants whether or
     not an equivariant marking of `K/H` exists, so the obstruction is not about markers.
2. `research/artifacts/gk3-binary-descent-2-2026-09-14.md`, Section 2 (compression lemma) and Section 7
   ("Compression"). The hypothesis "an injective continuous equivariant `κ: A^G -> B^G` with
   `|A| > |B|`" is never satisfied, for any group. The lemma is vacuously true and the suggested
   construction cannot exist over any group, sofic or not. The reason given there ("over sofic groups
   no such map exists, since it would give strictness there") is correct but not the operative one.
3. Also subsumed: the clopen-image requirement. Over infinite `K` a full shift has no nonempty proper
   clopen invariant subset. (If `U` and its complement are nonempty clopen invariant, pick cylinders
   `[p] ⊆ U` on window `F` and `[q] ⊆ U^c` on window `F'`; since `{g : gF' ∩ F != ∅} = F F'^{-1}` is
   finite, choose `g` with `gF'` disjoint from `F`; a configuration with `p` on `F` and the translate of
   `q` on `gF'` lies in `U ∩ g.[q] ⊆ U ∩ U^c`.) So a clopen equivariant image would be everything,
   i.e. a conjugacy, which the landed claim excludes directly.

**What this means for designs.** Any intertwining `kappa o tau = Phi o kappa` with `kappa: A^K -> {0,1}^K`
has `kappa` non-injective on the constants, and strictness does not pass forward through a
non-injective intertwiner. The direction in which strictness does transfer is the reverse one
(Section 2). I appended a short correction bullet to the target's Attempts (no deletion).

## 2. Replacement criterion: lifting through a factor map, and where it dies

**Criterion (elementary).** Let `r: {0,1}^K -> A^K` be continuous, surjective and equivariant, `tau` a
strict automaton on `A^K`, and `Phi` an injective automaton on `{0,1}^K` with `r o Phi = tau o r`. Then
`Phi` is strict.
*Proof.* If `Phi` were surjective, `tau o r = r o Phi` would be surjective, so `tau` would be. ∎

**Existence of factor maps.** For `K` containing a free subgroup `F = <a,b>` of rank 2 put
`r(x)(g) = (x(g)+x(ga), x(g)+x(gb))` (mod 2), a sliding block code with memory `{1,a,b}`
(Ornstein–Weiss example; reference not fetched, properties verified here).
- Equivariant and continuous: `r(h.x)(g) = x(h^{-1}g)+x(h^{-1}ga) = r(x)(h^{-1}g)`.
- Kernel: `r(x) = 0` iff `x(g) = x(ga) = x(gb)` for all `g`, iff `x` is constant on each left coset `gF`.
- Surjective: `{0,1}^K = prod_{cosets} {0,1}^{gF}`, and on one coset with base point `g` define
  `x(g) = 0`, then extend along reduced words by `x(ha) = x(h)+y_1(h)`, `x(hb) = x(h)+y_2(h)`,
  `x(ha^{-1}) = x(h)+y_1(ha^{-1})`, `x(hb^{-1}) = x(h)+y_2(hb^{-1})`; the Cayley graph of `F` is a tree,
  so this is consistent.

So `4 ∈ NS(K)` descends to `2 ∈ NS(K)` whenever some strict `tau` on four symbols has an injective
lift through `r`. The question is which `tau` lift.

**Proposition A (lifts over `K = F`).** For `K = F` the kernel is `{0, 1}` (the two constants).
1. Every injective lift `Phi` commutes with the flip `x -> x+1`.
2. Conversely every flip-commuting automaton `Phi` on `{0,1}^F` induces an automaton `tau` on
   `({0,1}^2)^F` with `r o Phi = tau o r`, and `Phi` is strict iff `tau` is strict.

*Proof.* (1) `r(Phi(x+1)) = tau(r(x)) = r(Phi(x))`, so `Phi(x+1) - Phi(x) ∈ {0,1}`, and injectivity
excludes `0`. (2) `tau(r x) := r(Phi x)` is well defined since `Phi(x+1) = Phi(x)+1` has the same image;
`r` is a closed continuous surjection of compact Hausdorff spaces, hence a quotient map, so `tau` is
continuous, and it is equivariant. If `Phi` is injective and `tau(rx) = tau(rx')`, then
`Phi x' ∈ {Phi x, Phi x + 1} = {Phi x, Phi(x+1)}`, so `x' ∈ {x, x+1}` and `rx = rx'`. If `tau` is
surjective, any `w` has `r w = tau(r x) = r(Phi x)` for some `x`, so `w ∈ {Phi x, Phi(x+1)}`.
Conversely, `Phi` surjective gives `tau o r = r o Phi` surjective, so `tau` is surjective; and if `tau` is
injective and `Phi x = Phi x'`, then `rx = rx'`, so `x' ∈ {x, x+1}`, and `x' = x+1` is excluded because
`Phi(x+1) = Phi x + 1 != Phi x`. ∎

So over `F_2` itself, descent through this factor is exactly the existence of a strict flip-commuting
binary automaton: a stronger conclusion than the target. (Both sides are empty, `F_2` being sofic.)
For `K ⊋ F` the kernel is the group of coset-constant functions, uncountable when `[K:F]` is
infinite; injective lifts must satisfy `Phi(x+c) - Phi(x) ∈ ker r ∖ {0}` for every nonzero
coset-constant `c`.

**Proposition B (the coordinate swap has no lift by any automaton).** Let `K ⊇ F = <a,b>` free and
`tau(y)(g) = (y_2(g), y_1(g))`. No automaton `Phi` on `{0,1}^K` satisfies `r o Phi = tau o r`.

*Proof.* The equations are `Phi x(g) + Phi x(ga) = x(g)+x(gb)` and `Phi x(g) + Phi x(gb) = x(g)+x(ga)`.
With `z = Phi x + x`: `z(g)+z(ga) = x(ga)+x(gb) = z(g)+z(gb)`, so `z(h) = z(hc)` for all `h`, where
`c = a^{-1}b` has infinite order. `z` is an automaton image, `z(g) = f'((x(gn))_{n in N'})` with
`1 ∈ N'`. Choose `k` with `c^k N' ∩ N' = ∅` (possible, since `c^k ∈ N'N'^{-1}` for finitely many `k`).
For patterns `p, p'` on `N'` take `x` equal to `p` on `N'` and to `p'` on `c^k N'` (translated). Then
`f'(p) = z(1) = z(c^k) = f'(p')`, so `f'` is constant `ε` and `Phi x = x + ε`. The first equation then
reads `x(ga) = x(gb)` for all `x`, false. ∎

**Where it dies.** Lifting is a cohomological problem: `Phi(x)(1) = f(x)` must be a *local* potential
with `f(x) + f(a^{-1}.x) = c_1(x)`, `f(x) + f(b^{-1}.x) = c_2(x)` for `c = (tau o r)(x)(1)`
(up to the convention for the shift). No mechanism was found that produces local potentials for an
arbitrary strict `tau`, and Proposition B shows that lifting fails even for bijective automata of
radius zero. I did not find a way to modify a given strict `tau` (by composing with products,
conjugating by automorphisms of the four-symbol shift, or passing to `tau × id`) that guarantees a
lift. The criterion is recorded here only, as a sufficient condition stronger than the target.

## 3. Decompositions (elementary, recorded for orientation)

1. **Target ⟸ group-level ascent to a power of two ∧ binary-power descent.** If `n ∈ NS(K)` implies
   `2^j ∈ NS(K)` for some `j`, and `2^j ∈ NS(K)` implies `2 ∈ NS(K)`, the target holds for `K`.
   Group-level ascent at `K` would follow from the group-level consequence of
   `strict-rule-pairs-ascend-to-larger-alphabets` (OPEN in the landed graph). Referee note: on 2026-09-16 a
   refutation of that table-level claim by a composite-size table pair was in flight from another agent, not
   yet landed; the group-level ascent question would stay open in any case.
2. **Binary-power descent ⟸ square-root descent at `2^{2^k}`.** From `2^j ∈ NS(K)`, product closure
   gives `2^{2^k} ∈ NS(K)` for `2^k >= j`; halving the exponent `k` times reaches `2`. The base step is
   `4 ∈ NS(K) ⇒ 2 ∈ NS(K)`, i.e. a strict automaton on `({0,1}^2)^K` gives one on `{0,1}^K`.
3. **Restriction goes the wrong way.** If `[K:H] = j` then `n ∈ NS(K) ⇒ n^j ∈ NS(H)` (a `K`-automaton on
   `A^K ≅ (A^j)^H` is an `H`-automaton). For finite `F`, `2 ∈ NS(K × F) ⇒ 2^{|F|} ∈ NS(K)`. Both raise
   the alphabet, so neither helps the groupwise target.
4. **Quotient restriction constrains product-host designs.** For `N ⊴ L` and an `L`-automaton `Psi` on
   `C^L`, the `N`-fixed configurations are those constant on cosets `gN`, `Fix_N ≅ C^{L/N}`, and `Psi`
   maps `Fix_N` into itself (it commutes with `N`-translations). The restriction is a continuous
   `L/N`-equivariant map, hence an `L/N`-automaton, injective if `Psi` is. So a strict binary automaton
   over `K × C_q` restricts to an injective binary automaton over `K` on the constant-fibre subsystem;
   a design over `K × C_q` either already gives `2 ∈ NS(K)` or is bijective on constant fibres.

## 4. Phase transport over `K × C_q`: coincides with a recorded sufficient condition

- Binary configurations over `K × C_q` are maps `K -> W = {0,1}^{C_q}`, with `C_q` rotating every fibre at
  once. For `q` an odd prime, `W` has two constant words and `(2^q - 2)/q = 2 N_q` free rotation orbits, where
  `N_q = (2^{q-1}-1)/q`.
- On the subshift where every fibre is non-constant, a free word is an orbit label and a phase, and
  `Psi(o, φ) = (tau(o), φ)` is strict and commutes with the rotation, for any strict `tau` on
  `2N_q` labels. For odd `n` and a prime `q > n` with `q ≡ 1 mod ord_n(2)`, `n | N_q`, so `n ∈ NS(K)`
  reaches `2N_q ∈ NS(K)` by product closure. (For even `n` only `v_2(n) = 1` fits, since `N_q` is odd.)
- Rotation-equivariance forces a constant output on windows whose fibres are all constant (the output
  must be a rotation-fixed word), and by `injective-automata-fixing-passive-sites-are-surjective`
  (consequence "Binary codings over G × F") a design that leaves constant fibres in place is surjective
  once injective. By Section 3.4 the constant-fibre subsystem must carry a bijective binary automaton
  unless `2 ∈ NS(K)` already.
- **Where it dies.** Extending `Psi` to configurations with constant fibres. Output phases at sites
  whose input fibre is constant can only be relative to a free neighbour, and a free site sent to a
  constant fibre loses its phase, which must be stored elsewhere. I found no injective extension. This
  is the recorded sufficient condition "a `ζ`-homogeneous strict automaton on `R_q^G`" of
  `research/artifacts/gk3-binary-descent-2-2026-09-14.md`, Section 8, and it targets the universal form
  `some-nonsurjunctive-group-gives-a-binary-one`, not the groupwise target (the host changes to
  `K × C_q`).

## 5. Passive barrier strengthening: proved, but already landed

I proved: if `P ⊆ C` is nonempty and `Phi` is an injective automaton on `C^K` with
`x(g) ∈ P ⇒ Phi(x)(g) = x(g)` (no condition at active sites), then `Phi` is surjective. Pieces
`Y(E, ω) = {x : x = ω off E}` with `E` finite and `ω` passive off `E` have `|C|^{|E|}` elements, are
`Phi`-invariant (off `E` the sites carry passive symbols and are unchanged), so `Phi` bijects each;
their union is dense and the image is closed. This kills erasure designs (relays reading `∗` output
`∗`), which `passive-fixing-injective-automata-are-surjective` lists as not covered.
**Duplicate check:** this is exactly `injective-automata-fixing-passive-sites-are-surjective`
(ESTABLISHED through `passive-site-fixing-surjectivity-via-local-passivity`). No node added.

## 6. Other dead ends

- **Bicyclic monoid.** With `B = <p, q | pq = 1>` and `rho(m) = mq`, `rho` is surjective and not
  injective (`q^{i}` and `q^{i+1}p` both map to `q^{i+1}`), so `x -> x o rho` is strict over every
  alphabet including two. Monoids give no alphabet separation, and no content for groups.
- **Rectangle-clause view.** By `surjunctivity-is-axiomatized-by-rectangle-clauses`, a uniform descent
  would transform strict data `D` over `A` into strict binary data `D'` whose memories are words in the
  memories of `D`. Forward coincidences of `D'` can be derived equationally from those of `D`. The
  reverse side needs each derived coincidence outside `T'_r` to force an original coincidence outside
  `T_r` modulo the forward relations. No transformation meeting both was found. The fixed-table
  obstruction (`equal-label-table-is-strict-at-three-symbols-not-two`) shows that the memories must grow.
- **Stamping a missing pattern of `tau`** (gk3-binary-descent-2, Section 7): not reattempted.
- **Linear witnesses at the groupwise level.** A strict `F_2`-linear automaton on `(F_2^m)^K` gives no
  binary automaton on `K` itself by any recorded argument. The recorded linear descent lands at
  `K × P` (`modular-matrix-failures-descend-to-scalars-over-g-times-p`), so even the linear case of the
  groupwise target stays open.

## 7. Literature gate (checked 2026-09-16)

No primary source resolving alphabet reduction to two symbols for surjunctivity was found.
- arXiv:1912.00541 (Cannizzo): withdrawn (withdrawal dated 4 Dec 2019); no usable content.
- arXiv:2403.05998 (X. K. Phung, 9 Mar 2024) and arXiv:2503.23435 (Phung, v2 14 Mar 2026): no alphabet
  reduction found.
- T. Ceccherini-Silberstein, M. Coornaert, X. K. Phung, Groups Geom. Dyn. 19 (2025) 495–503,
  DOI 10.4171/GGD/885 (arXiv:2310.09451): fetched. Title "First-order model theory and Kaplansky's stable finiteness conjecture for surjunctive
  groups": it proves by model theory that group rings of surjunctive groups are stably finite, and contains
  no alphabet reduction. Its citation of the Ceccherini-Silberstein–Coornaert book
  (2nd ed., 2023) was not checked (book paywalled): unverified.
- arXiv:2606.17757 (Ceccherini-Silberstein, Coornaert, Salo, 16 Jun 2026) and arXiv:2603.18183 (Phung,
  18 Mar 2026): no alphabet reduction.
- arXiv export API listing for "surjunctive" (35 entries) and for "Myhill AND amenability" (9 entries):
  titles and abstracts scanned, none on alphabet reduction.
- arXiv:1605.09133 (L. Bartholdi, D. Kielak; v1 30 May 2016, v2 7 Jun 2016): uses alphabets `K^2` and
  `K^Y` over fields. No reduction to two symbols.
- A search-engine summary asserting that the question is open and equivalent to the case
  `A = {0,1}` could not be traced to a primary source: **unverified**, not relied on.
- Not checked: arXiv:2511.06586, arXiv:2002.05352 (404 at fetch), arXiv:2111.13607, arXiv:2405.18287.
- Ornstein–Weiss factor example (1987): not fetched; every property used in Section 2 is proved there.

## 8. What remains open

- The target, in full. No strictness-transferring mechanism from `|A| >= 3` symbols to two symbols over
  the same group is known. Codings are impossible (Section 1), product hosts change the group
  (Sections 3-4), and factor lifts need local potentials that no argument supplies (Section 2).
- Most concrete next question: for `K ⊋ F_2` with the coset-constant kernel, can a given strict
  four-symbol automaton be modified, keeping strictness, so that it acquires an injective lift through
  the Ornstein–Weiss factor?

## Referee (2026-09-16)

**Checked.**
- Section 1. The Fact (constants are the `K`-fixed points; an equivariant injection maps them injectively)
  is correct over every group, finite or infinite, and is the landed
  `full-shifts-with-different-alphabets-are-not-conjugate` restricted to injections. I read the "Reformulation"
  bullet of the target and its source, `research/artifacts/alphabet-ascent-and-binary-descent-2026-09-12.md`,
  Section 3, and the compression lemma of `research/artifacts/gk3-binary-descent-2-2026-09-14.md`, Sections 2
  and 7. Both need an equivariant injection `A^K -> {0,1}^K` (resp. `A^G -> B^G` with `|A| > |B|`), so both
  are vacuous as the solver says. "Equivalent" in the target bullet is indeed an overstatement: the source
  artifact gives only the sufficient direction. The measurable compression claim
  `measurable-alphabet-compression-over-leavitt-units` is not affected (constants are null). The
  no-proper-clopen-invariant-set argument over infinite `K` is correct (`{g : gF' ∩ F != ∅} = F F'^{-1}`).
- Section 2. Verified the criterion, equivariance and kernel of the Ornstein–Weiss map, surjectivity by the
  tree extension, Proposition A (both directions; I spelled out the converse for injectivity, which uses flip
  commutation, not only the intertwining equation), and Proposition B (the invariance `z(h) = z(h a^{-1} b)`,
  the choice of `k` with `c^k N' ∩ N' = ∅`, constancy of the local rule, and the contradiction).
- Section 3. Restriction to finite-index subgroups needs a right transversal `K = ⊔ H t` for the left shift;
  with it the identification `A^K ≅ (A^j)^H` is `H`-equivariant. The quotient restriction in 3.4 is correct
  (`N` normal, so `N`-fixed configurations are constant on cosets and form an `L/N`-full shift).
- Section 4. Arithmetic rechecked (`n = 3, q = 5`: `N_5 = 3`; `n = 5, q = 13`: `N_13 = 315`; `n = 7, q = 13`).
  The identification with the `ζ`-homogeneous condition of gk3 Section 8 is loose ("same obstacle": the free
  fibres are the nonzero vectors of `R_q` plus the augmentation bit, and the unresolved part is the zero
  symbol), but nothing depends on it.
- Section 5: the barrier is exactly the landed `injective-automata-fixing-passive-sites-are-surjective`; no
  node was added, correctly. Section 6 bicyclic example rechecked in normal forms `q^i p^j`.
- Literature spot-checks, fetched 2026-09-16: arXiv:1912.00541 (Cannizzo, withdrawn 4 Dec 2019, Lemma 5.3 gap);
  arXiv:2310.09451 and ems.press DOI 10.4171/GGD/885 (GGD 19 (2025), no. 2, 495–503); arXiv:2403.05998;
  arXiv:2503.23435 (v1 30 Mar 2025, v2 14 Mar 2026); arXiv:2603.18183; arXiv:2606.17757 (a Z-SFT paper). All
  exist with the stated authors and dates. I could not run further web searches (search budget exhausted),
  so the "no primary source on alphabet reduction" gate rests on the solver's scan.

**Changed.** Section 3.1 now records that `strict-rule-pairs-ascend-to-larger-alphabets` is OPEN in the landed
graph with a refutation in flight; Section 4 says `q` odd prime (for `q = 2`, `N_q` is not an integer);
Proposition A(2) converse spelled out; the GGD paper's content described accurately.

**Verdict.** Sound. No new node; the target stays OPEN. The appended correction bullet on the target is a
genuine correction of a recorded attempt and adds text only. Landed with small fixes.

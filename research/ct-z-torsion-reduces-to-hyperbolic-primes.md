---
rg: 2
id: ct-z-torsion-reduces-to-hyperbolic-primes
kind: claim
title: "Torsion in CT(Z) reduces to the hyperbolic primes: isometric primes collapse to a finite set without changing the order; if 2 is the only hyperbolic prime, finitely generated subgroups embed in Thompson's V and torsion is decidable; compression and non-trivial periodic germs are semi-decidable certificates of infinite order, but each alone is incomplete, and Conway's amusical permutation acts on Z_2 × Z_3 as the full 3-shift"
requires:
  - ct-z-rational-base-machines-carry-a-potential
  - ct-z-monomial-elements-have-decidable-torsion
  - ct-z-residue-partition-certificates-live-on-s-adic-coordinates
  - ct-z-finite-cycle-problems-are-undecidable
---

**ESTABLISHED** (lane proof, not reviewed). Elementary, apart from the cited solvability of torsion
in `V`. No priority is claimed.
- The torsion problem of `CT(Z)` stays **OPEN**. This node proves decidability on a larger class
  and isolates what a full proof needs: Conjecture 7.

## Setting

- For `g ∈ CT(Z)`, let `S` be the primes dividing its moduli.
- **Hyperbolic and isometric primes.** A prime `p ∈ S` is *hyperbolic* for `g` if some piece slope
  has `v_p ≠ 0`, and *isometric* otherwise. `H(g)` is the set of hyperbolic primes and
  `I(g) = S ∖ H(g)`. For a finitely generated subgroup, take unions over the generators.
- `ĝ` acts on `Ẑ_S` as in `ct-z-residue-partition-certificates-live-on-s-adic-coordinates`.

## Statement

**Theorem 1 (isometric quotient).**
- **The factor.** Let `M_I = ∏_{p∈I} p^{k_p}`, with `k_p = v_p` of the lcm of the moduli. Then
  `ĝ` factors onto a homeomorphism `g^♭` of `Ẑ_H × Z/M_I`, and `g` has the same order as `g^♭`.
- **No hyperbolic primes.** If `H(g) = ∅`, every slope is `1` and `g` has finite order.
- **Subgroups.** For a finitely generated `G ≤ CT(Z)`, `g ↦ g^♭` is an injective homomorphism into
  the homeomorphisms of `Ẑ_{H(G)} × Z/M_I`.

**Theorem 2 (only 2 hyperbolic).** If `H(G) = {2}` for a finitely generated `G ≤ CT(Z)`, which
means every slope is a power of 2 while the moduli may have odd factors, then `G` embeds in the
Higman–Thompson group `V_{2,M_I} ≅ V`. So `G` has solvable torsion problem.
- This contains Theorem 2 of `ct-z-monomial-elements-have-decidable-torsion`, where all moduli are
  powers of 2.
- Any embedding of `2V`, or of any group with unsolvable torsion problem, into `CT(Z)` therefore
  needs an odd hyperbolic prime.

**Lemma 3 (two certificates of infinite order; both Σ₁).**
- **(a) Compression.** A clopen `W` and `k ≥ 1` with `ĝ^k(W) ⊊ W`.
- **(b) Hyperbolic periodic germ.** A periodic point of `g^♭` whose germ of `(g^♭)^n` has slope
  `≠ 1`.

Either one implies that `g` has infinite order, and each can be searched for effectively.

**Proposition 4 (Conway's amusical permutation is a full shift).** Let
`α = (2n ↦ 3n, 4n+1 ↦ 3n+1, 4n−1 ↦ 3n−1)`. It lies in `CT(Z)`, being piecewise canonical from
`{0(2), 1(4), 3(4)}` to `{0(3), 1(3), 2(3)}`. Its extension `α̂` to `Z_2 × Z_3` is topologically
conjugate to the full shift on three symbols. So elements with two hyperbolic primes can carry every
subshift on three symbols as a closed invariant set, including infinite minimal ones. There is no
`V`-type structure theorem in that range.

**Proposition 5 (neither certificate is complete alone).**
1. **`g_1 = ψ_{0(3)} · τ_{1(3),2(9)}`** has infinite order and `H = {2, 3}`. No periodic point of
   `ĝ_1` on `Ẑ_{2,3}` has a germ of slope `≠ 1`: over the `Z_2` fixed points of `ψ`, the `Z_3` fibre
   maps have no periodic points. So (b) fails, but (a) holds.
2. **`F_M` for a periodic but not uniformly periodic 2-RCM `M`** has infinite order. Such `M` exist,
   because periodicity is undecidable and uniform periodicity is decidable (Kari–Ollinger Thms 3, 4).
   It admits no compression, so (a) fails.

**Theorem 6 (monomial elements).** Torsion is decidable on `Mon`
(`ct-z-monomial-elements-have-decidable-torsion`, via Kari–Ollinger Thm 4).

**Conjecture 7 (certificate completeness).** Every `g ∈ CT(Z)` of infinite order admits (a) or (b).
If it holds, run the search for `N` with `g^N = 1` in parallel with the search for (a) or (b). That
decides torsion in `CT(Z)`, and then `2V ⊄ CT(Z)` by Theorem 1 of
`ct-z-torsion-problem-and-the-brin-thompson-transplant`.

## Proofs

**Theorem 1.**
- **The factor exists.** For `p ∈ I`, every slope is a `p`-unit, and each piece depends on `x_p` only
  mod `p^{k_p}`. The map `x_p ↦ s + q(x_p − r)` is well defined mod `p^{k_p}`, so the projection
  `Ẑ_S → Ẑ_H × ∏_{p∈I} Z/p^{k_p}` is equivariant. For a finitely generated `G`, take `k_p` over the
  generators; composites stay well defined.
- **Same order when `H ≠ ∅`.** If `(g^♭)^N = 1`, each piece of `ĝ^N` is a rational affine map fixing
  an open set of some `Z_p` with `p ∈ H`. So it is the identity, and `ĝ^N = 1`. The same argument
  gives injectivity.
- **The case `H = ∅`.**
  - A positive `S`-unit with `v_p = 0` for all `p ∈ S` is `1`, so every piece is a translation
    `r(m) → s(m)`.
  - Let `L` be the lcm of the moduli. Then `g` permutes `Z/L` by some `π`, and for `N = ord(π)` the
    power `g^N` translates each class `c(L)`, `0 ≤ c < L`, by a multiple of `L`.
  - Elements of `CT(Z)` satisfy `n ≥ 0 ⇔ g(n) ≥ 0`. This holds for class transpositions and so for
    their products. Such a translation must therefore be `0`, so `g^N = 1`. The same argument gives
    injectivity. ∎

**Theorem 2.**
- **A Higman–Thompson element.** With `H = {2}`, each piece of `g^♭` maps a cone
  `(r + 2^aZ_2) × {j}` onto a cone `(s + 2^bZ_2) × {j′}`, by the prefix replacement
  `x ↦ s + 2^{b−a}(x − r)`. So `g^♭` lies in `V_{2,M_I}`, which acts on `M_I` copies of the Cantor set.
- **To `V`.** `V_{2,r} ≅ V` effectively (Higman), and `V` has solvable torsion problem (Belk–Bleak §1,
  citing Belk–Matucci). Theorem 1 transfers the answer back to `g`. ∎

**Lemma 3.**
- **(a) implies infinite order.** `ĝ^k(W) ⊊ W` gives `ĝ^{jk}(W) ⊊ W` for all `j ≥ 1`, so no power
  of `ĝ` is the identity.
- **(b) implies infinite order.** If `g^N = 1`, the germ of `(g^♭)^{nN}` at the point is the identity.
  Its slope is `U^N` for a positive rational `U ≠ 1`, a contradiction.
- **Semi-decidability.**
  - For (a): images of finite unions of boxes are computable, so enumerate pairs `(W, k)`.
  - For (b): on each piece of `(g^♭)^n` with slope `U ≠ 1`, the only candidate is the rational point
    `B/(1 − U)`. Test whether it lies in the piece's box, and whether a fixed residue exists in the
    finite factor. ∎

**Proposition 4.**
- **Membership.** `α` is piecewise canonical, so it lies in `CT(Z)` by
  `piecewise-canonical-permutations-are-transposition-products`.
- **Forward itineraries.** The domain pieces are determined by `x_2 mod 4`. Their `Z_2` maps
  (`3x/2`, `(3x+1)/4`, `(3x−1)/4`) send `2Z_2`, `1 + 4Z_2` and `3 + 4Z_2` onto all of `Z_2`,
  expanding by 2, 4 and 4. So forward itineraries determine `x_2`, and every sequence in
  `{A,B,C}^N` occurs.
- **Backward itineraries.** The image classes `0(3)`, `1(3)`, `2(3)` are determined by `x_3`, and
  `α̂^{-1}` maps each of `3Z_3`, `1 + 3Z_3`, `2 + 3Z_3` onto `Z_3`, expanding by 3. So backward
  itineraries determine `x_3`, and every sequence occurs.
- **Conclusion.** The itinerary map `Z_2 × Z_3 → {A,B,C}^Z` is a homeomorphism that conjugates `α̂` to
  the shift. ∎

**Proposition 5.**
1. **`g_1`.**
   - The factors have disjoint supports: `ψ_{0(3)} ∈ CT(Z)` by item 3 of
     `ct-z-north-south-element-has-no-finite-cycles`. Slopes `4, 1/4` and `3, 1/3` give `H = {2,3}`.
   - **Outside `0(3)`**, `ĝ_1^2 = 1`, so periodic germs there are trivial.
   - **On `0(3)`**, `ĝ_1` is conjugate by `x ↦ 3x` to `ψ̂` on `Z_2 × Z_3`. The `Z_2` periodic points
     of `ψ` are only `−2/3` and `−1/3`. Over them the fibre maps `u ↦ 4u + 2` and `u ↦ (u − 1)/4` have
     all their iterates' fixed points at `−2/3` and `−1/3`, which are not in `Z_3`.
   - **Compression.** `W = 6(12)` has `ĝ_1(W) = 30(48) ⊊ W`.
2. **`F_M`.**
   - `M` is complete, so every code is a configuration code and every integer orbit of `F_M` is
     finite. Periods are unbounded, so the order is infinite.
   - If `ĝ^k(W) ⊆ W` for a clopen `W`, each integer `w ∈ W` has period `j`, and
     `w = g^k(g^{k(j−1)}w)` with `g^{k(j−1)}w ∈ W`. So `W ∩ Z = g^k(W ∩ Z)`, and by density
     `ĝ^k(W) = W`. ∎

## What this says

- **Where the question now sits.** The open core is elements with an odd hyperbolic prime,
  necessarily through non-monomial pieces. There, hyperbolic dynamics can be a full shift
  (Proposition 4), and the two known certificates each miss some infinite-order element
  (Proposition 5).
- **What a proof of Conjecture 7 must supply.** A structure theorem for elements with no compression
  and trivial periodic germs, showing that every point is periodic with bounded period. The two
  inputs we have:
  - the conservation law of `ct-z-rational-base-machines-carry-a-potential`, which removes storage;
  - the finiteness of non-interior fixed points in piecewise-affine hosts (lane bh-free-57,
    15698b400).
- **The monomial case fits.** Non-uniformly periodic `F_M` has unbounded periods. By compactness,
  those orbits accumulate at a configuration with an infinite counter. We expect (b) at such a
  boundary point, since a trivial germ there would force bounded periods nearby. This is not
  proved here; Kari–Ollinger Thm 4 already settles `Mon`.

## Lesson for general BH

**Isometric directions can be collapsed; only the hyperbolic ones compute.**
- A coordinate where every slope is a unit carries only finite information, so it collapses to a
  finite set without changing the order (Theorem 1).
- With one hyperbolic prime, the host is Thompson's `V` in disguise (Theorem 2).
- With two, even one element (Conway's amusical permutation) is a full shift.
- **For BH host design.** Count the hyperbolic directions of the pieces, not the primes in the
  moduli. Uniform computation needs at least two, and the finite-information parts of an
  arithmetic host are free.

# Gromov density-model random groups at density in (1/3, 1/2): hyperbolic, Kazhdan, aspherical, b_2 >= 1

Verification for the `hyperbolic-sofic` lane, done by `lit-groups` on 2026-09-12.
All statements were read from PDF text extracted with ghostscript on MSI.

## Hyperbolicity and asphericity below density 1/2

**Source.** Y. Ollivier, *Sharp phase transition theorems for hyperbolicity of
random groups*, GAFA 14 (2004), arXiv:math/0301187v3 (latest arXiv version).

- **Theorem 1** (attributed to Gromov). Fix a density `d` between 0 and 1.
  Choose a length `ℓ` and pick at random a set `R` of `(2m−1)^{dℓ}` uniformly
  chosen cyclically reduced words of length `ℓ` in `a_1^{±1}, …, a_m^{±1}`.
  - If `d < 1/2`, the probability that `<a_1,…,a_m | R>` defines an infinite
    hyperbolic group tends to 1 as `ℓ → ∞`.
  - If `d > 1/2`, the group is w.o.p. `{e}` or `Z/2Z`.
  - The paper states that a complete proof is included in Section 2.
- **Asphericity, in that proof.** The isoperimetric inequality
  `|∂D| > αℓ|D|` holds for every reduced van Kampen diagram, not only minimal
  ones, so there is no reduced spherical diagram. The text: "Second, we prove
  that the presentation is aspherical. With our conventions on van Kampen
  diagrams, our asphericity implies asphericity of the Cayley complex and thus
  cohomological dimension at most 2 (indeed, thanks to the marking of each face
  by a starting point and a relator number, two faces are reducible in a
  diagram only if they really are the same face in the Cayley complex, so that
  diagram reduction is a homotopy in the Cayley complex)." It then concludes
  torsion-freeness.
- Small-cancellation companion paper, not needed here: Ollivier,
  arXiv:math/0409226 (IJAC 2007), Theorem 1 restates hyperbolicity for
  `d < 1/2`. Its introduction lists "Property T for d > 1/3 [Zuk03]".

## Property (T) above density 1/3

**Source 1.** M. Kotowski and M. Kotowski, *Random groups and property (T):
Żuk's theorem revisited*, arXiv:1106.2242v2 (latest version, May 2012).

- **Theorem B.** "For density d > 1/3, a random group in the Gromov model
  G(n,l,d) has property (T) with overwhelming probability."
- **Definition 2.1.** `R` consists of `(2n−1)^{ld}` relators "chosen uniformly
  and independently from the set of relators of length l", which may repeat.
  Relators are cyclically reduced by the paper's standing convention.
  Overwhelming probability means the limit as `l → ∞` with `n` fixed.
- The proof ("Proof of Theorem B", Section 3) passes through the triangular
  model `M+(m, d)` (Theorem 3.14) and a finite-index comparison (Lemma 3.15).
- **Scope caveat.** The authors say: "Actually we have covered only the case of
  l divisible by 3". They sketch the other lengths by allowing all relators of
  length `≤ l`. Imported here only for `l ≡ 0 mod 3`.

**Source 2** (independent proof). C. Druțu and J. M. Mackay, *Random groups,
random graphs and eigenvalues of p-Laplacians*, arXiv:1607.04130v3.

- The introduction says: "We do find a new proof of property (T) for any fixed
  k ≥ 2 and d > 1/3, which moreover applies at d = 1/3 as well (see Theorem
  12.6 for a precise statement)".
- **Theorem 12.6** is stated in the binomial model `B(k,l,ρ)`, for
  `ρ(l) ≥ C l (2k−1)^{l/3}/(2k−1)^l`. Corollary 12.7 transfers it to the
  density model through Proposition 10.2. The construction again uses relator
  lengths that are multiples of 3.
- **Theorem 1.10** gives the stronger `FL^p` property for `k ≥ 10·2^p` at
  `d > 1/3`.

## Consequence: b_2 >= 1

Fix `m >= 2` and `d ∈ (1/3, 1/2)`, and let `ℓ → ∞` through multiples of 3.

1. **Model transfer.** Ollivier's model draws a uniform set, Kotowski–Kotowski
   a uniform multiset. At `d < 1/2` a repeated relator has probability
   `≤ (2m−1)^{2dℓ}/#{cyclically reduced words} → 0` (birthday bound), and the
   group does not change when duplicates are removed. So each w.o.p. event
   transfers between the two models.
2. **Both properties at once.** W.o.p. `G` is infinite hyperbolic, the
   presentation is aspherical (so the presentation 2-complex `X` is a finite
   `K(G,1)`), and `G` has property (T).
3. **Euler characteristic.** `χ(X) = 1 − m + |R| = 1 − b_1(G) + b_2(G)`, with
   rational Betti numbers of `G` equal to those of `X`. Property (T) gives
   `b_1(G) = 0`. So `b_2(G) = |R| − m = ⌊(2m−1)^{dℓ}⌋ − m ≥ 1` as soon as
   `ℓ ≥ 6`.

**Not explicit.** This is existence with high probability. No specific
presentation is certified, and the Kotowski–Kotowski import is limited to
lengths divisible by 3.

---
rg: 2
id: orderable-quotient-stackings-inject-the-kernel
kind: claim
title: A relator whose letters survive in orderable quotients, with a reduced image that is not a proper power, keeps both free factors, including the kernels of the quotient maps
distinct_from:
  lo-syllable-relators-keep-free-factors: that needs the syllable subgroups themselves to be left-orderable, so every letter has infinite order and the syllable subgroups are torsion-free; this needs only homomorphisms from the syllable subgroups to orderable groups under which the letters survive, so the syllable subgroups may contain torsion or non-hyperlinear subgroups. That claim is the case where p and q are the identity.
  normal-generators-of-free-products-have-non-lo-syllables: that pushes a normal generator forward to a quotient pair and applies the orderable case there, which only detects elements that survive in the quotient; this pulls the action on the line back and injects the whole factor, including the kernel of the quotient map, which the push-forward never sees.
  left-orderable-free-products-have-normal-rank-above-one: that is Chen--Lodha Theorem B for orderable factors; this is their spectral gap run with a non-faithful action pulled back from an orderable quotient of the syllable subgroups.
  klyachko-kl-holds-when-all-coefficients-have-infinite-order: that allows exponent sum ±1 only and needs infinite order; this allows every exponent sum, including 0, and needs survival in an orderable quotient, which is stronger than infinite order.
  klyachko-multivariable-equation-with-nonpower-content-solvable: that needs the whole group torsion-free and the variable content not a proper power; this needs no torsion-freeness but needs the reduced image over an orderable quotient not to be a proper power.
---

**Status: proposed ESTABLISHED** by `orderable-quotient-stackings-proof`. It is
a literature derivation: Chen–Lodha's two input theorems are imported and not
reproved, and the new step is the pull-back. Not independently reviewed.

**Terminology.** For a group `H`, the *orderable radical* `R(H)` is the
intersection of the kernels of all homomorphisms from `H` to right-orderable
groups. `H/R(H)` embeds in a product of right-orderable groups, which is
right-orderable under a lexicographic order on a well-ordered index set, so
`R(H)` is the smallest normal subgroup with right-orderable quotient. It contains
every element of finite order.

**Statement.** Let `A`, `B` be arbitrary groups and `G = A * B`. Let
`w = a_1 b_1 ... a_n b_n` be cyclically reduced, `n >= 1`, `a_i ∈ A∖{1}`,
`b_i ∈ B∖{1}`, with syllable subgroups `A' = <a_1,...,a_n>` and
`B' = <b_1,...,b_n>`. Suppose there are homomorphisms `p: A' -> Q_A`,
`q: B' -> Q_B` to right-orderable groups such that

- (L) `p(a_i) ≠ 1` and `q(b_i) ≠ 1` for every `i`, and
- (P) `w̄ = p(a_1) q(b_1) ... p(a_n) q(b_n)` is not a proper power in `Q_A * Q_B`.

Then:
1. **Spectral gap.** Every boundary-incompressible `w`-admissible surface `S` in
   `G` satisfies `−χ^−(S) >= deg(S)`.
2. **Injectivity.** `A -> G/<<w>>` and `B -> G/<<w>>` are injective. This
   includes the kernels `ker p` and `ker q`, whose elements are invisible to the
   action on the line.
3. **Powers.** The same injectivity holds for `<<w^k>>`, `k >= 1`, since
   `<<w^k>> ⊆ <<w>>`.

The best choice is `p: A' -> A'/R(A')`, `q: B' -> B'/R(B')`. Any other choice
factors through it, and a proper power stays a proper power under a homomorphism
that keeps the letters nontrivial. So (L) and (P) hold for some pair iff they
hold for the radical quotients.

**Sharpness of the method.** A *relative stacking* of `w` in `A' * B'`
(Chen–Lodha Definition `def: relative stacking`: an action on `R`, not
necessarily faithful, with a stable trajectory) exists iff (L) and (P) hold for
some pair `(p, q)`. So this statement is exactly the reach of the Chen–Lodha
spectral-gap method for a fixed relator. It cannot say anything about a relator
that has a letter in `R(A')` or `R(B')`, or whose radical image is a proper
power. See Step 5 of the proof.

**Kervaire–Laudenbach and Levin form** (`B = <t>`, `q = id`). Let `G` be any
group and `w = a_1 t^(k_1) ... a_n t^(k_n)` cyclically reduced (`a_i ≠ 1`,
`k_i ≠ 0`, `n >= 1`). If every `a_i` lies outside `R(A')`, and the image of `w`
in `(A'/R(A')) * <t>` is not a proper power, then `G -> (G * <t>)/<<w>>` is
injective, at every exponent sum including `0`. The step from `A'` to `G` is
the pushout `(G * <t>)/<<w>> = G *_(A') (A' * <t>)/<<w>>`. The screen that this
gives for violations of `kervaire-laudenbach-nonsingular-conjecture` is
`kl-violations-need-a-sign-change-coefficient-in-the-lo-radical`.

**Classes it reaches that no known theorem covers.** Take `G = K × Z` with `K`
arbitrary, `Z = <s>`, and coefficients `a_i = (k_i, s^(c_i))` with every
`c_i ≠ 0` and `∏ s^(c_i) t^(k_i)` not a proper power in `F(s, t)`. Then
`p: A' -> Z` works, and `G` injects at every exponent sum. The coefficient
subgroup contains `A' ∩ K`, which may have torsion and need not be hyperlinear
(`K` might be a free Burnside group, whose hyperlinearity is open).

The following theorems do not cover it:
- **Pestov / Nitsche–Thom:** they need `K` hyperlinear.
- **Klyachko:** he needs exponent sum ±1.
- **Brodskii–Howie–Short, Krstić, Chen–Lodha's own theorem:** `A'` has torsion.
- **Klyachko–Mikheenko** (GR kernel, locally indicable quotient): they need the
  kernel `K` to be GR.

**Calibration.**
- **Free products with coprime torsion.** Over `Z/2 * Z/3` the word
  `a t b t^(-1)` kills `a`. Both letters have finite order and lie in the
  radical, so (L) fails and nothing is claimed.
- **Over `Z × Z/2 = <s> × <c>`.** For `w = (sc) t s^(-1) t^(-1)`, (L) and (P)
  hold, and the conclusion agrees with the HNN extension conjugating `s^(-1)` to
  `(sc)^(-1)` (both of infinite order), which contains `G`.
- **Words `a t^k` with `a` of finite order.** The radical image is `t^k`, a
  proper power, so nothing is claimed. The conclusion is true there for other
  reasons (amalgamate `<a>` into a cyclic group).

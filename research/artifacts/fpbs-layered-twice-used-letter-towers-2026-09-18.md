# Layered twice-used-letter Morse matchings build a cyclic root-commensuration tower

Agent: swarm-0917-w11-w11-fp-pull (obstruction-miner, host-geometry), 2026-09-18.

Setting, cells, edges and (M1)–(M3) are those of `research/artifacts/fpbs/docs/bernoulli-morse-collapse-criterion.md`
(Section 1). Edges are pairs `(x, s)` in `X x S`, so for each letter `s` the set of `s`-edges has `nu`-measure `1`.

## 1. The class

Let `M` be a Morse matching for a list `R` of trivial words on a finite generating set `S`, over any essentially free
p.m.p. action of `Gamma`. For a matched cell `c = (x, r)` let `lambda(c)` be the letter of `M(c)`. A letter is
*active* if `lambda^{-1}(s)` has positive measure, and `A` is the set of active letters. Put `U = S \ A`.

`M` is **layered twice-used (LTU)** if there is a total order `<` on `A` such that, for a.e. matched cell `c` with
`lambda(c) = s`:

- (L1) the letter `s` (as `s` or `s^{-1}`) occurs exactly twice in `r`;
- (L2) every other letter of `r` lies in `U` or is an active letter `> s`.

Write `A = {s_1 < ... < s_n}` and `H_i = <s_i, ..., s_n, U>`, with `H_{n+1} = <U>`.

Members of the class:
- the dual-forest matching of `fpbs-one-relator-twice-used-letter-fixed-price` (`n = 1`);
- the commuting-direction chains of the node's first dead attempt (cells `[s_i, c]` with `c` later or in `U`);
- every iteration of these along a Magnus/Tietze hierarchy, over any generating set and any list (for example `P_L`).

(M3) is not used below. Only (M1), (M2), (L1) and (L2) are used, so the bounds hold for the larger class without
well-foundedness.

## 2. Mass count

**Lemma 1.** `mu(M) <= n = |A|`.

*Proof.* By (M2) the removed edges are distinct, and every removed edge is an `s`-edge for some `s` in `A`. Each
letter carries `nu`-measure `1` of edges. Theorem A(b) gives `mu(M) = nu(E_M) <= |A|`. ∎

## 3. The tower lemma (any group)

**Lemma 2.** Suppose `s = s_i` is active. Then some cyclic rotation of a word `r` in (L1)–(L2) has one of two forms.
In both, `u, v` are words in letters of `H_{i+1}`.

- (−) `s u s^{-1} v`, with `u != 1` in `Gamma`. Then `s u s^{-1} = v^{-1}` lies in `H_{i+1}`.
- (+) `s u s v`, with `g = s u != 1` in `Gamma`. Then `g^2 = v^{-1} u` lies in `H_{i+1}`, and `g` lies in
  `s H_{i+1}`.

*Proof.* Rotate and, if needed, invert `r` so that it begins with `s`. Rotation and inversion are bijections of cells
that preserve the set of traversed edges, and the relation `r = 1` holds for every rotation.

With the path convention of Section 1 of the criterion, the two `s`-edges of the cell `(x, r)` are `(h_1.x, s)` and
`(h_2.x, s)`:

- in case (−), `h_1 = s^{-1}` and `h_2 = (s u)^{-1}`;
- in case (+), `h_1 = s^{-1}` and `h_2 = (s u s)^{-1}`.

By freeness, the two edges coincide iff `h_1 = h_2`. That is iff `u = 1` in case (−), and iff `s u = 1` in case (+).

The matched edge is an `s`-edge. By (M1) it is traversed exactly once, so the two `s`-edges are distinct. The
identities follow from `r = 1`. ∎

**Corollary 3 (tower).** If `|U| <= 1` and every letter of `S` is active or in `U`, then `Gamma = H_1` is reached from
the cyclic group `H_{n+1} = <U>` by `n` steps `H_i = <H_{i+1}, s_i>`. Each step is either

- a *nontrivial commensuration*: `s_i u s_i^{-1}` lies in `H_{i+1}` for some `u` in `H_{i+1} \ {1}`; or
- a *nontrivial root*: some `g != 1` in `s_i H_{i+1}` has `g^2` in `H_{i+1}`.

So a matching with more than `|S| - 2` units of mass must come from such a *cyclic root-commensuration tower*.

## 4. Theorem (cyclic-CSA groups)

**Definition.** `Gamma` is *cyclic-CSA* if it is torsion-free and every maximal abelian subgroup is cyclic and
malnormal. Then every `g != 1` lies in a unique maximal abelian subgroup, namely `C(g)`, and `C(g) = C(g^k)` for all
`k != 0`.

Torsion-free hyperbolic groups are cyclic-CSA: centralizers are cyclic, and maximal cyclic subgroups are malnormal.

**Theorem.** Let `Gamma` be cyclic-CSA and not cyclic. For every finite generating set `S`, every list `R` of
trivial words, every essentially free p.m.p. action and every LTU matching `M`:

```text
mu(M) <= |S| - 2.
```

On Bernoulli this gives:
- LTU deficit `z(Phi_S) - mu(M) >= 1 - beta_1^(2)(Gamma)`, uniformly in `S` and `R`, including `R = P_L` for all
  `L`;
- the Theorem A cost certificate is `|S| - mu(M) >= 2`.

*Proof.* By Lemma 1 we may assume `|U| <= 1`, since otherwise `mu(M) <= |A| <= |S| - 2`. Suppose `|U| <= 1`. We
derive a contradiction by showing that every `H_i` lies in one cyclic subgroup `E`.

*Base.*
- If `H_{n+1} = 1`, apply Lemma 2 at `s_n`.
  - Case (−) needs `u != 1` in `H_{n+1} = 1`, which is impossible.
  - Case (+) gives `g != 1` with `g^2 = 1`, which contradicts torsion-freeness.
  - So `s_n` is not active, which is a contradiction.
- Hence `H_{n+1} = <t>` with `t != 1`. Put `E = C(t)`, which is cyclic and contains `H_{n+1}`.

*Step.* Assume `H_{i+1} <= E`. Apply Lemma 2 at `s = s_i`.
- Case (−). `s u s^{-1}` is a nontrivial element of `E`, and `u` lies in `E \ {1}`. So `s E s^{-1} ∩ E != 1`, and
  malnormality gives `s ∈ E`.
- Case (+). `g != 1`, so `g^2 != 1` by torsion-freeness, and `g^2` lies in `E`. Then `g ∈ C(g^2) = E`, since `E` is
  the unique maximal abelian subgroup containing `g^2`. So `s = g u^{-1}` lies in `E`.

So `H_i <= E` for all `i`, hence `Gamma = H_1 <= E` is cyclic. This is a contradiction.

The Bernoulli consequences follow from `z(Phi_S) = |S| - 1 - beta_1^(2)` and Theorem A(c). ∎

## 5. Consequences and calibration

**Where the class dies.** The bottom of the letter order.
- The last active letter must root-commensurate the cyclic group `<U>`.
- Malnormality then locks every later letter into `C(t)`.
- *Invariant:* the maximal cyclic subgroup `C(t)`, which is closed under nontrivial commensuration and square roots.

**Groups where it bites** (`beta_1^(2) = 0`, so the LTU deficit is `>= 1` at every `S` and `R`):
- **Closed hyperbolic 3-manifold groups.** They are torsion-free hyperbolic, and `beta_1^(2) = 0` (Lott–Lück). They
  have fixed price `1`: by Agol, a finite-index subgroup fibres, so it has an infinite, finitely generated, normal
  subgroup of infinite index. Gaboriau's normal-subgroup criterion then gives cost `1` with fixed price, and
  `C - 1` scales with the index. So the Bernoulli cost equals `1 + beta_1` there, and LTU still stays a whole unit
  short.
- **Torsion-free finite-index subgroups of cocompact lattices in `Sp(n,1)`, `n >= 2`.** These are hyperbolic with
  property (T), so `beta_1^(2) = 0`.

**Consistency checks.**
- *Two-generator torsion-free one-relator groups with a twice-used letter.* The word is `a b^p a^{-1} b^q` (a
  Baumslag–Solitar group) or `a b^p a b^q` (`x^2 = b^(p-q)`, with a nontrivial centre). Neither is cyclic-CSA unless
  cyclic. So the positive theorem (`mu = 1 = z`, `|S| - 2 = 0`) never conflicts with the Theorem.
- *Hyperbolic one-relator groups on `>= 3` generators.* Here `beta_1 = |S| - 2 >= 1`, so the bound is vacuous, as
  it must be.
- *Surfaces.* Here `beta_1 >= 1`, so the bound is vacuous. One layer suffices there.
- *Fibred 3-manifold groups `pi_1(Sigma_g) ⋊_phi Z`* with `S = {t, a_1, ..., b_g}`.
  - The natural LTU matching has two layers: `t` (cells `t a t^{-1} phi(a)^{-1}`) and `a_1` (the surface relator).
  - Its mass is `<= 2`. Against `z = 2g`, its deficit is `>= 2g - 2`.
  - Gaboriau's cost-1 proof is a measured normal-subgroup argument that does not factor through Cayley cell
    matchings of this kind.

**What survives.** Any proof of `fpbs-morse-deficit-vanishes-for-full-presentations` on a cyclic-CSA group with
`beta_1 = 0` must use at least one of the following on a set of cells of positive measure:
- (a) a matched letter used `>= 3` times in its cell (the regime of `fpbs-single-letter-morse-matchings-die-on-bernoulli`
  and `fpbs-letter-saturated-morse-matchings-die-on-bernoulli`, capped per (type, letter) when the transport group is
  nonamenable); or
- (b) a cyclic letter dependency: a matched `s`-cell containing an active letter `s'` whose matched cells contain `s`.

Case (b) is the balanced multi-letter regime of w9 Proposition D. This result isolates it as the only remaining
twice-used option.

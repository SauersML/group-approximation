---
rg: 2
id: f2xf2-crossed-products-ce-make-sl2-centralizer-hnn-hyperlinear
kind: claim
title: If every essentially free crossed product of F2 x F2 is Connes-embeddable, the SL2 homogeneous crossed products embed and every rank-two centralizer HNN group is hyperlinear
distinct_from:
  f2xf2-on-dyadic-lattice-quotient-bounds-vertex-action: that uses the same real-times-p-adic lattice duality at p=2 to move SOFICITY between the dyadic vertex action and one F2 x Fr action; this moves CONNES EMBEDDABILITY of crossed products through corners of the coupling algebra, at every prime, and lands on the homogeneous crossed product M_2 and hence on the rank-two projective transfer inequality and hyperlinearity of the centralizer HNN group.
  tree-lattices-hyperlinear-if-f2xf2-crossed-products-ce: that derives hyperlinearity of torsion-free lattices in products of trees from the same hypothesis through a compact-open corner theorem; this derives hyperlinearity of the S-arithmetic centralizer HNN groups H_p, which are not tree lattices, through the SL2(R) x SL2(Q_p) coupling, where no compact open subgroup is available.
  sl2-homogeneous-quotient-crossed-product-is-connes-embeddable: that is the open embeddability of M_2 at p=2; this proves it for every prime under the F2 x F2 hypothesis and does not decide it.
  dyadic-vertex-soficity-equals-frame-dynamics-soficity: that is a soficity equivalence on the 2-adic face, whose sofic side gives Cartan microstates of M_2 only as a remark; this uses the weaker hypothesis of Connes embeddability of crossed products, not soficity of any action.
  paunescu-class-is-measure-equivalence-invariant: that is measure-equivalence invariance of the class of groups all of whose actions are sofic; this is a one-directional Connes-embedding transfer along one explicit coupling and proves no invariance theorem.
---

**ESTABLISHED** by route `f2xf2-crossed-products-ce-sl2-hnn-proof`. Not independently reviewed.

**Setting.** Fix a prime `p`. Put

```text
A = SL_2(Z[1/p]),   C = SL_2(Z),   L = SL_2(Q_p),   H' = SL_2(R) x L,
H_p = A *_C (C x Z) = < A, t | [t, c] = 1 (c in C) >,
```

with `A` embedded diagonally in `H'`. Let `Lambda' < L` be a torsion-free cocompact lattice with
at least two `K`-orbits on `X = L/Lambda'` (`K = SL_2(Z_p)`), and put

```text
M_2^(p) = L^infinity(X) rtimes A,                                    (FX0)
Delta = Gamma(3) x Lambda'  <  H'   (Gamma(3) = ker(SL_2(Z) -> SL_2(Z/3))),
Delta acting on the right of  A \ H'  (Haar probability).            (FX1)
```

`Delta` is isomorphic to `F_3 x F_r` with `2 <= r < infinity`, hence to a subgroup of index
`2(r-1)` of `F_2 x F_2`.

**Theorem.**

1. `(FX1)` is an essentially free p.m.p. action, and `M_2^(p)` embeds trace-preservingly into a
   finite corner of a matrix amplification of `L^infinity(A\H') rtimes Delta` in the following
   precise sense: if `L^infinity(A\H') rtimes Delta` is Connes-embeddable, so is `M_2^(p)`.
2. If `L^infinity(Y) rtimes (F_2 x F_2)` is Connes-embeddable for every essentially free p.m.p.
   action `F_2 x F_2 -> Aut(Y, nu)`, then for every prime `p` and every such `Lambda'`:
   - `M_2^(p)` is Connes-embeddable. At `p = 2` this is
     `sl2-homogeneous-quotient-crossed-product-is-connes-embeddable`.
   - The rank-two instance of `projective-commutant-transfer-for-arithmetic-pair` fails at `p`.
   - `H_p` is hyperlinear.
   - `SL_2(Z[1/p])` is not flexibly Hilbert--Schmidt stable. At `p = 2` this answers
     `iwahori-local-global-defect-question` negatively.
3. **Contrapositive (the gate).** Suppose any one of the following holds at some prime `p`:
   - the rank-two PRCC inequality;
   - `relative-commutant-collapse-for-sl2-pair` (`p = 2`);
   - nonhyperlinearity of `H_p`;
   - flexible HS-stability of `SL_2(Z[1/p])`.

   Then the explicit essentially free action

   ```text
   F_2 x F_2  acting on  ((F_2 x F_2) x_Delta (A\H')) x {0,1}^(F_2 x F_2)      (FX2)
   ```

   (induction of `(FX1)` followed by a Bernoulli product) has a non-Connes-embeddable crossed
   product. By the standard fact that essentially free sofic actions have Connes-embeddable
   crossed products, it is also a nonsofic action, which would settle `f2xf2-admits-nonsofic-action`.
   That fact is not an edge here.

**What this changes.**

- **One gate for the whole rank-two arithmetic lane.** Every rank-two route in the
  commutant/HNN family ends at the same object:
  - the HS-stability route `hnn-over-codense-kazhdan-subgroup-not-hyperlinear` at `n = 2`;
  - PRCC at `n = 2`;
  - the SL2 relative-commutant collapse;
  - the spherical-leak exclusion at `n = 2`.

  Each of them, if true, produces a non-Connes-embeddable crossed product of the Haagerup group
  `F_2 x F_2` by an explicit algebraic action: the free Fuchsian group `Gamma(3)` translates the
  real coordinate of the S-arithmetic quotient `SL_2(Z[1/p]) \ (SL_2(R) x SL_2(Q_p))`, and the
  free p-adic lattice translates the tree coordinate.

  This graph records no crossed product of `F_2 x F_2` known to fail Connes embeddability.
  `f2xf2-lacks-kechris-property-md` gives actions outside the weak closure of finite actions,
  which is a weaker conclusion. So each of those statements is at least as hard as exhibiting an
  explicit non-CE crossed product. Each also implies `f2xf2-admits-nonsofic-action`.
- **The same hypothesis refutes the lane and proves the tree-lattice lane.** "All `F_2 x F_2`
  crossed products are CE" simultaneously:
  - refutes all four rank-two statements above, at every prime;
  - yields hyperlinearity of every torsion-free product-tree lattice
    (`tree-lattices-hyperlinear-if-f2xf2-crossed-products-ce`).

  A proof of either lane's positive statement is therefore a proof against the other lane's
  hypothesis.
- **Why rank two only.** The argument needs a free lattice in the archimedean factor, to land in
  `F_2 x F_2` by induction. For `n >= 3` every lattice of `SL_n(R)` has property (T), and (T)
  is a measure-equivalence invariant, so no such coupling of `SL_n(Z[1/p])` with a finite-index
  subgroup of `F_2 x F_2` exists. The `n >= 3` projective-transfer and collapse lanes are
  untouched by this gate. Kazhdan mechanisms for PRCC live only there.

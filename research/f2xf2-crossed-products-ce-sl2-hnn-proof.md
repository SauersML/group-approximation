---
rg: 2
id: f2xf2-crossed-products-ce-sl2-hnn-proof
kind: route
title: Extend M_2 to the S-arithmetic coupling algebra, pass between its two fundamental-domain corners, induce to F2 x F2, then read off PRCC, the HNN group and stability
target: f2xf2-crossed-products-ce-make-sl2-centralizer-hnn-hyperlinear
requires:
  - homogeneous-quotient-ce-refutes-arithmetic-commutant-collapse
  - rank-two-projective-transfer-equals-hnn-nonhyperlinearity
  - hnn-over-codense-kazhdan-subgroup-not-hyperlinear
artifacts:
  - research/artifacts/fournier-facio-simple-factor-corner-2026-09-16.md
---

"CE" means Connes-embeddable. The facts (CE1)--(CE3) of the artifact, Section 1.3, are used as
stated there:
- (CE1) trace-preserving subalgebras of CE algebras are CE;
- (CE2) `M_n` of a CE algebra is CE;
- (CE3) corners of a CE algebra, with the normalized trace, are CE.

One more standard fact is used:

- **(CE5)** Let `(N, tau)` be a finite von Neumann algebra and `p_n` an increasing sequence of
  projections with strong limit `p`. If every `p_n N p_n` is CE, so is `pNp`.

  *Proof.* Use the microstate characterization of Connes embeddability for separable tracial
  algebras: every finite tuple of contractions has matricial approximants of all bounded-length
  `*`-moments. Let `x_1, ..., x_k` be contractions in `pNp`. Then
  `||p_n x_i p_n - x_i||_2 -> 0` and `tau(p_n)/tau(p) -> 1`. So every normalized moment of the
  `p_n x_i p_n` in `p_n N p_n` converges to the corresponding normalized moment of the `x_i` in
  `pNp`, uniformly over words of bounded length. Microstates of the former are therefore
  microstates of the latter. ∎

Notation as in the target: `A = SL_2(Z[1/p])` diagonal in `H' = SL_2(R) x L`,
`L = SL_2(Q_p)`, `K = SL_2(Z_p)`, `Delta = Gamma(3) x Lambda'`, and `m` is Haar measure on `H'`.

1. **`A` is a lattice in `H'`.**
   - **Density.** `A` contains the elementary matrices with entries in `Z[1/p]`, which is dense
     in `Q_p`. These are dense in the two unipotent subgroups, which generate `L`. So `A` is
     dense in `L`, and `L = A K` because `K` is open.
   - **Factorization.** Given `(g, x) in H'`, write `x = a k` with `a in A`, `k in K`. Then
     `(g, x) = a (a^(-1) g, k)`, so `H' = A (SL_2(R) x K)`.
   - **Overlap.** If `a (g, k) = (g', k')` with `k, k' in K`, then `a_p in K cap A = SL_2(Z)`.
   - **Quotient.** Hence `A \ H' = SL_2(Z) \ (SL_2(R) x K)`. This has finite measure, because
     `SL_2(Z)` is a lattice in `SL_2(R)` and `K` is compact.
   - **Discreteness.** `A` meets `U x K` in the finite set `SL_2(Z) cap U` for every relatively
     compact `U`.
2. **`Delta` is a lattice isomorphic to a finite-index subgroup of `F_2 x F_2`.**
   - **The factor `Gamma(3)`.** `-I` is not congruent to `I` mod `3`, and `Gamma(N)` is
     torsion-free for `N >= 3`. So `Gamma(3)` maps isomorphically onto a torsion-free subgroup
     of `PSL_2(Z) = C_2 * C_3`. Its index there is `|PSL_2(F_3)| = 12`.
   - **Freeness of `Gamma(3)`.** By Kurosh it is free. Its rank is `1 + 12/6 = 3` (rational
     Euler characteristic `-1/6`).
   - **The factor `Lambda'`.** It is discrete and torsion-free, so it meets every vertex
     stabilizer of the Bruhat--Tits tree trivially. `L` acts without inversions. So `Lambda'`
     acts freely on the tree and is free (Serre).
   - **Rank of `Lambda'`.** Cocompactness makes it finitely generated. A cocompact lattice in the
     nonamenable group `L` is not virtually cyclic. So `Lambda' ≅ F_r` with `2 <= r < infinity`.
   - **Lattice.** `Delta` is a product of lattices, hence a lattice.
   - **Embedding in `F_2 x F_2`.** By the Schreier index formula, `F_3` and `F_r` occur as
     subgroups of `F_2` of index `2` and `r - 1`. So `Delta` is isomorphic to a subgroup
     `Gamma_0` of index `2(r-1)` in `F_2 x F_2`.
3. **`M_2^(p)` sits inside the left crossed product.**
   - `H'/Delta = SL_2(R)/Gamma(3) x X` carries the product of the invariant probability
     measures. It is the unique `H'`-invariant probability measure.
   - `A` acts diagonally. The projection `H'/Delta -> X` is `A`-equivariant and measure-preserving.
   - So `f u_a -> (f o pr) u_a` preserves `tau(f u_a) = delta_(a,e) integral f`. It extends to a
     trace-preserving embedding `M_2^(p) = L^infinity(X) rtimes A -> L^infinity(H'/Delta) rtimes A`.
4. **Both actions are essentially free.**
   - **`A` on `H'/Delta`.** By item 1 of `homogeneous-quotient-ce-refutes-arithmetic-commutant-collapse`,
     the action of `A` on the factor `X` is essentially free. A point whose image in `X` has
     trivial stabilizer has trivial stabilizer itself.
   - **`Delta` on `A\H'`.** `delta != 1` fixes `A h` iff `h delta h^(-1) in A`. For each of
     countably many `a in A`, the set `{h : h delta h^(-1) = a}` is empty or a coset of the closed
     centralizer `Z(delta) = Z_R(delta_R) x Z_p(delta_p)`.
   - **Null cosets.** A closed subgroup has positive Haar measure only if it is open. If `Z(delta)`
     were open:
     - `Z_R(delta_R)` would be open in the connected group `SL_2(R)`, so `delta_R = +-I`, hence
       `delta_R = I` in torsion-free `Gamma(3)`;
     - `Z_p(delta_p)` would contain an open congruence subgroup, which is Zariski dense, so
       `delta_p = +-I`, hence `delta_p = I` in torsion-free `Lambda'`.

     That forces `delta = 1`. So for `delta != 1` the fixed set is null.
5. **The coupling algebra and its two corners.**
   - **Domains.** Let `F` be a Borel fundamental domain for right `Delta`-translation and `E` one
     for left `A`-translation. Both have finite measure by items 1 and 2.
   - **The relation.** Put `W = E cup F` and let `R` be the relation on `W` given by
     `x ~ y` iff `y in A x Delta`. Its classes are countable. It preserves `m|_W`, because left and
     right translations preserve `m` (`H'` is unimodular). Let `N = L(R)`, with trace from the
     normalized `m|_W`.
   - **Corner at `F`.** `F` is identified with `H'/Delta`, and `R|_F` is the orbit relation of `A`
     there. By item 4 and Feldman--Moore, `1_F N 1_F = L(R|_F) = L^infinity(H'/Delta) rtimes A`,
     with normalized traces.
   - **Corner at `E`.** Likewise `1_E N 1_E = L^infinity(A\H') rtimes Delta`.
6. **From the `E`-corner to the `F`-corner.**
   - **Partial isometries.** Enumerate `A = {a_1, a_2, ...}`. Since `A E = H'` a.e., the sets
     `F_i = {x in F : a_i^(-1) x in E} \ (F_1 cup ... cup F_(i-1))` partition `F` a.e. On `F_i`
     the map `x -> a_i^(-1) x` is a measure-preserving injection into `E` whose graph lies in
     `R`. It gives partial isometries `v_i in N` with `v_i^* v_i = 1_(F_i)` and
     `v_i v_i^* <= 1_E`.
   - **Amplified corners.** With `p_n = 1_(F_1 cup ... cup F_n)` and `q = 1_E`, the map
     `Psi_n(x) = [v_i x v_j^*]_(i,j<=n)` sends `p_n N p_n` into `M_n(qNq)`.
     - It is multiplicative, since `sum_k v_k^* v_k = p_n`.
     - It is injective, since `x = sum_(i,j) v_i^* Psi_n(x)_(ij) v_j`.
     - It satisfies `Tr_n(Psi_n(x)) = tau(x)`.

     So it is a trace-preserving isomorphism, for normalized traces, onto the corner of
     `M_n(qNq)` cut by `Psi_n(p_n)`.
   - **Conclusion.** If `qNq` is CE, then by (CE2), (CE3) and (CE1) every `p_n N p_n` is CE. By
     (CE5), with `p_n -> 1_F`, `1_F N 1_F` is CE. With items 3 and 5 and (CE1), this proves item 1
     of the target: **if `L^infinity(A\H') rtimes Delta` is CE, so is `M_2^(p)`.**
7. **Induction to `F_2 x F_2`.** Let `Y = (F_2 x F_2) x_(Gamma_0) (A\H')` be the induced p.m.p.
   action. By Lemma 3 (FI3) of the artifact, `L^infinity(A\H') rtimes Gamma_0` embeds
   trace-preservingly into the corner `q'(L^infinity(Y) rtimes (F_2 x F_2))q'`, where
   `q' = 1_([e, A\H'])`.
   - The artifact's proof is short and self-contained. The set `[e, A\H']` is
     `Gamma_0`-invariant with disjoint translates. The map `a v_h -> a~ v_h q'` is multiplicative.
     The normalized trace computation gives `delta_(h,e) integral a`.
   - `Y` is essentially free: the stabilizer of `[g, x]` is `g Stab_(Gamma_0)(x) g^(-1)`, and
     item 4 makes it trivial a.e.

   Under the hypothesis of item 2 of the target, `L^infinity(Y) rtimes (F_2 x F_2)` is CE. By
   (CE3), (CE1) and item 6, `M_2^(p)` is CE, for every prime `p` and every admissible `Lambda'`.
8. **Consequences.**
   - **PRCC and the SL2 collapse.** By item 4 of
     `homogeneous-quotient-ce-refutes-arithmetic-commutant-collapse` at `n = 2`, CE of
     `M_2^(p)` refutes the general-pair inequality `(PRT1)` of
     `projective-commutant-transfer-for-arithmetic-pair` at `(2, p)`. At `p = 2` it also refutes
     `relative-commutant-collapse-for-sl2-pair`.
   - **Hyperlinearity of `H_p`.** By `rank-two-projective-transfer-equals-hnn-nonhyperlinearity`
     (items 1 and 5), the rank-two PRCC inequality at `p`, for any `h`, `S` and presentation, has
     the truth value of nonhyperlinearity of `H_p = A *_C (C x Z)`. So `H_p` is hyperlinear.
   - **Stability.** By the `(tau)` form of `hnn-over-codense-kazhdan-subgroup-not-hyperlinear`,
     flexible HS-stability of `SL_2(Z[1/p])` would make
     `G_p = < SL_2(Z[1/p]), t | [t, SL_2(Z)] = 1 > = H_p` nonhyperlinear. So `SL_2(Z[1/p])` is not
     flexibly HS-stable. This proves item 2.
   - **The gate.** Item 3 is the contrapositive, with the freeness upgrade (FI4) of the artifact:
     the crossed product of `Y` sits trace-preservingly inside that of the essentially free
     diagonal action on `Y x {0,1}^(F_2 x F_2)`. So non-CE of the former gives non-CE of `(FX2)`.
     ∎

**Where the argument is tight.**
- **Only one corner transfer runs.** Item 3 is an inclusion, not an equality. So CE of `M_2^(p)`
  does not by this route give CE of `L^infinity(A\H') rtimes Delta`. The real factor
  `SL_2(R)/Gamma(3)` makes `A ↷ H'/Delta` an extension of the frame dynamics `A ↷ X`. Connes
  embeddability passes from the extension's crossed product to the factor's, but not back.
- **A converse would need more.** The rank-two lane is equivalent to non-CE of `(FX2)` only if
  that extension step could be reversed.

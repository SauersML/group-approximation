---
rg: 2
id: bounded-cluster-period-preserves-kazhdan-fixed-algebras
kind: claim
title: A compressor of bounded period on the Kazhdan clusters of a sofic representation makes the compressor-group graph expander-decomposable and preserves the fixed algebra, with no property (T) of the compressor group
distinct_from:
  kun-thom-sofic-centralizer-normalization: that needs property (T) of the ambient group to get the ambient expander decomposition; here the compressor group <L,u> is arbitrary (typically it maps onto Z) and the decomposition is built from bounded cluster period of u alone.
  sofic-groups-kill-rigid-compression-defects: that is the group-level kill for a Kazhdan compressor group; this is an ultraproduct statement about one sofic representation of a possibly non-Kazhdan compressor group, at the fixed-algebra level.
  per-compressor-component-matching-over-shared-decompositions: that formalizes the component matching when an ambient expander decomposition is given as data; this constructs such a decomposition from a combinatorial period condition, where none is given.
  kt-per-compressor-assembly-over-cluster-frames: that assembles Kun--Thom 4.1 for infranormal Kazhdan pairs with both groups Kazhdan; this removes the need for (T) of the ambient group at the decomposition step only.
  kt-genuine-atomic-vertex-coordinate-models-normalize: that concerns ultraproduct models of the Theorem E actor with atomic vertex coordinates; this is a general criterion for any Kazhdan L and any compressor u.
artifacts:
  - research/artifacts/kun-thom-2608-06222-verified.md
---

**ESTABLISHED.**

## Setting

- `L` is a Kazhdan group with finite symmetric generating set `S`.
- `u` is an element of an ambient group with `u L u^-1 <= L`, and `H = <L, u>`.
  Then `L` is infranormal in `H`, since `L ∪ {u}` lies in `P_L = {g : gLg^-1 <= L}`.
- `sigma : H -> S_U` is a sofic representation in the sense of Kun--Thom Definition 2.1
  (trace zero off the identity), with lifts `sigma_n(g) in Sym(Y_n)`. Write `u_n = sigma_n(u)`.
- A **cluster frame** for `sigma|_L` is a sequence of partitions `Q_n = {Q_(n,i)}` of `Y_n`
  and `h > 0` such that, after changing `o_U(|Y_n|)` edges, the `S`-generator graph of
  `sigma_n` is the disjoint union of the induced graphs on the `Q_(n,i)`, each of Cheeger
  constant `>= h`. One exists by [13, Theorem 1] (quoted verbatim in the artifact), since
  `L` has (T).
- **Dominant target and loss.** `pi_n(i)` is an index `j` maximizing
  `|u_n Q_(n,i) ∩ Q_(n,j)|` (ties broken arbitrarily), and
  `ell_n(i) = |Q_(n,i)| - |u_n Q_(n,i) ∩ Q_(n,pi_n i)|`.
- **Weight.** For a set `I` of indices, `w_n(I) = |union_(i in I) Q_(n,i)| / |Y_n|`.

Two conditions on the frame:

```text
(BP_p)  lim_U w_n( Per_(n,p) ) = 1,  Per_(n,p) = { i : pi_n^q(i) = i for some 1 <= q <= p };
(FD_k)  lim_U w_n( I_n ) = 1        for some index sets |I_n| <= k.
```

`BP_p` says that `u` has **bounded cluster period** `<= p` on almost all of the mass.
`FD_k` says that `k` clusters carry almost all of the mass.

## Statement

1. **(Loss bound.)** `sum_i ell_n(i) = o_U(|Y_n|)`, for every cluster frame and every
   compressor `u`.
2. **(BP ⇒ ED.)** If the frame satisfies `BP_p`, then the `(S ∪ {u})`-generator graph of
   `sigma` becomes, after `o_U(|Y_n|)` edge changes, a disjoint union of graphs of
   Cheeger constant `>= min(h,1)/(8p)`.
3. **(FD ⇒ BP.)** `FD_k` implies `BP_k`.
4. **(Fixed-algebra invariance.)** Under `BP_p` or `FD_k`, for every `g in H`,

   ```text
   sigma(g) D_U^(sigma(L)) sigma(g)^-1 = D_U^(sigma(L)).
   ```
5. **(FD is finite dimension.)** For every cluster frame, `FD_k` holds if and only if
   `dim D_U^(sigma(L)) <= k`. This uses Kun--Thom Lemma 2.3,
   `D_U^(sigma(L)) = prod_U D(Q_n)`.

Item 4 is Kun--Thom Proposition 3.1, verbatim in the artifact, applied to the pair
`L <= H`. Its hypotheses are:
- both groups are finitely generated;
- `L` is infranormal in `H`;
- the `L`-graph decomposes, by [13, Theorem 1];
- the `H`-graph decomposes, by item 2.

Nowhere is `H` assumed Kazhdan. In the cases of interest it is not, because `H` is an
ascending HNN quotient that maps onto `Z`.

## Why it matters

Kun--Thom need property (T) of the ambient group only to produce the ambient expander
decomposition (Lemma 4.4, "Let 𝒜_n be the component partition of the edited G-generator
graph"). This node replaces that input with a checkable combinatorial invariant: the
period of the dominant-target map `pi_n` of the compressor on the `L`-clusters.

The log-drift model shows that monotonicity of cluster sizes along `pi_n` alone cannot
replace ambient expansion. Bounded period is exactly what closes the drift: a `pi_n`-cycle
of length `<= p` of good clusters has comparable sizes and is an expander block.

`ambient-decomposition-kun-thom-normalization` is the centralizer-level version.
`bounded-period-compressors-carry-no-sofic-defect` is its group-level consequence for
compression defects.

Derivation: `bounded-cluster-period-fixed-algebra-proof`.

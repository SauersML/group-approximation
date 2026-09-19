---
rg: 2
id: fpbs-normal-zd-fibres-give-bounded-degree-spread-out-uniqueness
kind: claim
title: On any group with a normal Z^d, d at least 2, spread-out site percolation has a unique infinite cluster at bounded mean degree, so the spread-out spine criterion is attained on nonamenable groups, while Z fibres and periodic hard-core groups defeat fibre merging
distinct_from:
  fpbs-spread-out-uniqueness-gives-sparse-spines: that proves the transport Theorem A, the criterion Corollary B and the square-root lower bound Corollary C, and records that Corollary B is not known to apply to any nonamenable group; this proves that its hypothesis holds, with room of order L^(1-d), on every group with a normal Z^d, d >= 2, and gives the matching upper bound p_u^site |T| = O(1) there
  fpbs-no-fiid-sparse-spines-on-nonamenable-groups: that is the refuted root; groups with an infinite normal amenable subgroup already have FIID spines by the lift theorem, so this gives no new spine-bearing group; it is a calibration of the spread-out criterion, not a new refutation
---

**ESTABLISHED (agent-verified, not refereed).** Proof in
`fpbs-normal-zd-fibres-give-bounded-degree-spread-out-uniqueness-proof`.

**Setting.**
- `Gamma` is a finitely generated group with finite symmetric generating set
  `S`, and `A ⊴ Gamma` is a normal subgroup isomorphic to `Z^d`, `d >= 2`,
  with basis `e_1, ..., e_d`. `S' = S ∪ {e_i^(±1)}`.
- `B_L ⊂ A` is the `l^1` ball of radius `L` in these coordinates, and

  ```text
  T_L = ( S·B_L ∪ B_L·S ∪ B_L ) \ {e}.
  ```

  `T_L` is symmetric, `T_L ⊂ B_(S')(L+1)`, and
  `|T_L| <= (2|S|+1)(2L+1)^d`.
- Site percolation, `p_u^site` and FIID spines are as in
  `fpbs-spread-out-uniqueness-gives-sparse-spines`.
  `pi_2 = p_c^site(Z^2) < 1`, and `c_0 = log(1/(1-pi_2))`.

**Theorem 1 (bounded-degree uniqueness).** For `L >= 2(d+1)` and every
`p > kappa_d L^(-d)`, where `kappa_d = c_0 (2(d+1))^d`, site percolation of
density `p` on `Cay(Gamma, T_L)` has exactly one infinite cluster a.s. Hence

```text
p_u^site(Cay(Gamma,T_L)) <= kappa_d L^(-d),     p_u^site(T_L) |T_L| <= kappa_d (2|S|+1) 3^d.
```

**Theorem 2 (fibre-merging principle).** Let `A ⊴ Gamma` be any infinite
finitely generated normal subgroup, `T_A` a finite symmetric generating set
of `A` not containing `e`, and `T ⊇ T_A ∪ (S \ A)` finite symmetric with
`e ∉ T`. If site percolation of density `p` on `Cay(A,T_A)` has a unique
infinite cluster, then:
- a.s. all the fibre clusters (the copies of that cluster on the cosets
  `gA`) lie in one open cluster `U` of `Cay(Gamma,T)`. `U` is a
  `Gamma`-equivariant factor of the iid labels;
- the FIID spine bound of Theorem A holds with `U` in place of the unique
  cluster, so `Cay(Gamma,S')` carries an FIID connected infinite subgraph of
  density at most `p + p^2 |T| (L'-1)`, where `T ⊂ B_(S')(L')`. This does not use
  uniqueness in `Gamma`;
- `U` is the only infinite cluster (indistinguishability, Step 5 of the
  route).

**Corollary 3 (the criterion is attained on nonamenable groups).** Under
Theorem 1, take `p_L = 2 kappa_d L^(-d)`. Then `p_L -> 0` and

```text
p_L^2 |T_L| L  <=  4 kappa_d^2 (2|S|+1) 3^d L^(1-d)  ->  0.
```

So Corollary B of `fpbs-spread-out-uniqueness-gives-sparse-spines` applies.
The spines have density `O(L^(1-d))`. This includes nonamenable groups such
as `F_2 x Z^2` and `Z^2 ⋊ SL_2(Z)`.

**Corollary 4 (two-sided calibration of the mean degree at uniqueness).**
Let `M(T) = p_u^site(Cay(Gamma,T)) |T|` be the mean open degree at the
uniqueness threshold.
- If `Gamma` has a normal `Z^d`, `d >= 2`, then `M(T_L) = O(1)`, so
  `p_u^site/p_c^site` stays bounded along `T_L`, since `p_c^site >= 1/(|T|-1)`.
- If `C*(Gamma) > 1`, then `M(T) >= c (|T|/L)^(1/2)` for every `T ⊂ B_S(L)`
  (Corollary C there).

(Q) asks where a periodic hard-core group sits in this range. On such a
group, the rigorous range of possible profiles is now the whole interval
from `O(1)` up to the square root.

**Proposition 5 (where fibre merging dies).**
- **(D1) Linear fibres.** For `A ≅ Z` and every finite range, site
  percolation on `Cay(Z, [-L,L] \ {0})` has `p_c^site = 1`: `L` consecutive
  closed sites disconnect it, and a.s. such runs occur on both sides. So
  fibre merging over a normal or central `Z` certifies nothing at any `p < 1`.
  It dies at the fibre-existence step, exactly at `d = 1`. On `F_2 x Z`,
  Corollary B remains untested.
- **(D2) Periodic hard core.**
  - In a Tarski monster, every proper subgroup is finite, so Theorem 2 has no
    admissible fibre.
  - In a group all of whose infinite normal subgroups are nonamenable (for
    example a free Burnside group of large odd exponent, whose infinite
    subgroups are nonamenable), Theorem 2 needs fibre uniqueness on a
    nonamenable `Cay(A,T_A)` at the same density. That is a spread-out
    uniqueness statement of type (Q) for `A`. The Burton–Keane step of the
    route (Step 2), the only place where amenability enters, is unavailable.

So fibre merging proves (Q)-type uniqueness only by importing it from an
infinite normal subgroup, and the Z^d coarse-graining of Step 1 needs
`d >= 2`.

**What this does and does not advance.**
- *Advances.*
  - It gives the first verification on the board that the spine criterion
    Corollary B is non-vacuous on nonamenable groups.
  - The margin is large. Corollary B needs `p^2 |T| L -> 0`, and here it
    decays like `L^(1-d)`.
  - It pins the lower end of the mean-degree range that (Q) probes.
  - It names the two points where the natural construction dies: `d = 1`
    fibres and the absence of infinite amenable normal subgroups.
- *Does not advance.* Every group covered already has FIID sparse spines by
  the lift theorem. It does not decide (Q) on any hard-core group, and it
  does not advance `fpbs-benjamini-schramm-universal` directly.

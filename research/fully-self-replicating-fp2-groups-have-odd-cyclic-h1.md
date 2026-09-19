---
rg: 2
id: fully-self-replicating-fp2-groups-have-odd-cyclic-h1
kind: claim
title: The coinvariant bound H_*(R;k) >= (H_*(R;k)^(tensor X))_P for R = R wr_X P holds over every field, including characteristic 2 and the primes dividing |P|; so a fully self-replicating group of type FP_2 (in particular a finitely presented one) has H_1(R;Z) finite cyclic of odd order, one of type FP_3 is perfect, and every b_1 = 1 candidate on the Tits route is not finitely presented
artifacts:
  - experiments/self-replicating-mod2-homology-2026-09-18/nakaoka_mod_p_check.g
  - experiments/self-replicating-mod2-homology-2026-09-18/nakaoka_mod_p_check.out
distinct_from:
  fully-self-replicating-fp-infinity-groups-are-acyclic: that proves the coinvariant identity only for fields whose characteristic does not divide |P|, where the Lyndon-Hochschild-Serre sequence collapses for elementary reasons, and so allows b_1 = 1 and any H_1 torsion at primes of |P| for finitely presented R; this uses Nakaoka's collapse, which holds over every field, and in characteristic 2 the Koszul sign disappears, so b_1 = 1 and 2-torsion are excluded at FP_2.
  self-wreathing-groups-are-not-fp-infinity: that finds the retracts W_n of R and shows R is not FP_k in the first nonzero degree k of H_*(P), which for superperfect P such as M_11 says nothing about finite presentation; this is a degree-2 statement about the homology of R itself, and it constrains finite presentation for every transitive P.
  fp-self-similar-finitely-supported-loops-give-characters: that produces characters G -> Z from finitely supported loop cocycles and stops such groups at FP_(|X|-1); combined with this, every such group with an infinite loop character is not finitely presented.
---

**ESTABLISHED (unreviewed).** Proof: `fully-self-replicating-fp2-groups-have-odd-cyclic-h1-proof`.
The proof is by hand from Nakaoka's theorem, which is cited. The GAP script checks the
degree-2 prediction, at primes dividing `|P|` and at `p = 2`, on finite wreath products.

**Setting.** As in `fully-self-replicating-fp-infinity-groups-are-acyclic`, except for the
field. `X` is a finite set with `d = |X| ≥ 2`, and `P ≤ Sym(X)` is transitive. `R` is any
group with an isomorphism `R ≅ R ≀_X P = R^X ⋊ P`. Every fully self-replicating
`R ≤ Aut(X*)` with root image `P` is such a group. **`k` is any field.**
`h_n = dim_k H_n(R; k)`, a cardinal. A basis tensor is a tensor over `X` of homogeneous
basis vectors of `H_*(R; k)`, with the unit class `1 ∈ H_0` included in the basis.

**Theorem.**

1. **Coinvariant bound over every field.** `(H_*(R; k)^{⊗X})_P`, with `P` permuting
   factors with the Koszul sign, is a direct summand of `H_*(R; k)`. So
   `h_n ≥ h_n + dim E_n(k)` for every `n`, where `E_n(k)` has one basis vector for each
   `P`-orbit of basis tensors of degree `n` with at least two non-unit factors whose
   stabilizer acts on them by `+1`. **`E_n(k) = 0` in every degree with `h_n < ∞`.**
2. **Excess classes.** Let `u ≠ v` be basis classes in degrees `a, b ≥ 1`, and `x ≠ y` in
   `X`.
   - (i) `u` at `x`, `v` at `y` spans a class of `E_{a+b}(k)`. This includes `a = b`.
   - (ii) If `char k = 2` and `h_a ≠ 0`, then `E_{2a}(k) ≠ 0`, from `u` at `x` and at `y`.
     No sign can appear.
   - (iii) The items 2(ii), 2(iii) and 3 of
     `fully-self-replicating-fp-infinity-groups-are-acyclic` hold for every field. The
     characteristic restriction there is not needed.
3. **Finite presentation.** If `R` is of type `FP_2`, in particular if `R` is finitely
   presented, then **`H_1(R; Z)` is finite cyclic of odd order.** Equivalently:
   - `H_1(R; F_2) = 0`;
   - `dim_k H_1(R; k) ≤ 1` for every field `k`.

   So `b_1(R) = 0`, `R^{ab}` has no 2-torsion, and all its Sylow subgroups are cyclic.
4. **`FP_3`.** If `R` is of type `FP_3`, then `R` is perfect. A class `u ∈ H_1(R; F_p)`
   has the Bockstein partner `v ∈ H_2(R; F_p)`, the image of `Tor(H_1(R; Z), F_p)`, and
   item 2(i) makes `H_3(R; F_p)` infinite-dimensional. When the first nonzero degree of
   `H_*(P; Z)` is `3`, as for `M_11`, `FP_3` already fails by
   `self-wreathing-groups-are-not-fp-infinity`, and item 4 is empty. It has content for
   `P` with `H_1 = H_2 = H_3 = 0`.
5. **Tits hosts.** By `tits-hosts-for-transitive-local-actions`, the Tits host
   `(R ≀ F) *_{R×R} (R ≀ F)` is finitely presented iff `R` is. So item 3 is a necessary
   condition for a finitely presented section-closed Tits host.

**What it kills on the Tits route of `boone-higman-conjecture`.** Every fully
self-replicating candidate with `b_1 ≥ 1` or with 2-torsion in `H_1` is not finitely
presented, and neither is its Tits host, whatever the contraction behaviour. On the
graph:

- `R' = ⟨M_11, b, c'⟩` of `m11-separated-loop-host-has-b1-one` has `H_1 ⊇ Z`, so it is
  **not finitely presented**. Previously it was only known not to be `FP_10`.
- `R' = ⟨M_11, a, b, c⟩` of `m11-torsion-linear-host-has-b1-one` has `b_1 = 1`, so it is
  **not finitely presented**. It "passed the acyclicity bound at `FP_2`" only because that
  bound was proved away from `2`.
- Item 4 of `fp-self-similar-finitely-supported-loops-give-characters` improves to this:
  a fully self-replicating group with an infinite loop character is not finitely
  presented, for every transitive root image. So every design with a separated loop
  state, or with an odometer state (which keeps `b_1 ≥ 1`), is dead at `FP_2`.
- `R'' = ⟨M_11, b, c⟩` of `m11-odometer-free-linear-host-h1-is-z55-squared` has
  `dim H_1(R''; F_5) = 2`. Item 3 kills it again, independently of the ray-loop argument
  of `m11-odometer-free-host-is-not-finitely-presented`.

**What survives.** `R_0 = ⟨M_11, b⟩` and the balanced-loop host `R° = ⟨M_11, b, C⟩` have
`H_1 = Z/55`, which is odd and cyclic (`m11-balanced-loop-host-h1-is-z55`). `R_0` is
contracting, so Bartholdi's theorem kills it. `R°` passes. So after this node the
homological screen at `FP_2` is exactly this: odd cyclic `H_1`, with no condition on
`H_2`. In degree 2 the only possible excess comes from pairs of degree-1 classes. With one
degree-1 class in odd characteristic, a swap of the pair acts by `−1`, and every
2-transitive `P` has such a swap.

**Calibration.**

- The script computes `dim H_2(R ≀_X P; F_p)` for `R ∈ {C_2, C_3, C_4, C_5, S_3, C_2²}`,
  `P ∈ {C_2, C_3, S_3, A_4, C_5, A_5}` and `p ∈ {2, 3, 5}`, whenever `|R ≀ P| ≤ 2000`. The predicted value is
  `h_2(R) + (2-subset part) + h_1(R) · dim H_1(P_x; F_p) + dim H_2(P; F_p)`. In the
  2-subset part, a swapped pair contributes the symmetric square in characteristic `2`
  and the exterior square otherwise. All cases agree, including `p | |P|` and `p = 2`.
  This is the degree-2 case of the Nakaoka decomposition used in item 1.
- `R = C_2` on two points, `p = 2`: `H_2(C_2 ≀ C_2; F_2)` is 3-dimensional, and the
  class `u ⊗ u` is one of the three. Away from `2` that class would be killed by the
  Koszul sign. This is exactly the class that item 2(ii) uses.
- Thompson's group `V` is finitely presented and acyclic (Szymik--Wahl), so it meets
  item 3. It is not of the form `R ≀_X P` with `P` finite, which is consistent with
  `self-wreathing-groups-are-not-fp-infinity`.

**What it does not do.** It gives no obstruction for a group with odd cyclic `H_1`, for
instance `R°`. Whether a finitely presented fully self-replicating group exists stays open.

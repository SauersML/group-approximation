---
rg: 2
id: fully-self-replicating-fp2-groups-have-odd-cyclic-h1-proof
kind: route
title: Proof of the all-characteristic coinvariant bound by the Steenrod-Nakaoka chain-level argument, and of the FP_2 and FP_3 consequences by excess classes from pairs of degree-1 classes and from Bockstein partners
target: fully-self-replicating-fp2-groups-have-odd-cyclic-h1
requires:
  - fully-self-replicating-fp-infinity-groups-are-acyclic
  - self-wreathing-groups-are-not-fp-infinity
  - tits-hosts-for-transitive-local-actions
  - fp-self-similar-finitely-supported-loops-give-characters
artifacts:
  - experiments/self-replicating-mod2-homology-2026-09-18/nakaoka_mod_p_check.g
  - experiments/self-replicating-mod2-homology-2026-09-18/nakaoka_mod_p_check.out
---

**Status: ESTABLISHED (unreviewed).** The proof is by hand. The one outside input is
Nakaoka's theorem, and its proof is given in §1: M. Nakaoka, *Homology of the infinite
symmetric group*, Ann. of Math. 73 (1961); L. Evens, *The Cohomology of Groups* (Oxford,
1991), the chapter on wreath products; I. J. Leary, *On the integral cohomology of wreath
products*, J. Algebra 198 (1997).

## 1. Nakaoka's decomposition over any field

**Proposition 1.** Let `G` be any group, `P ≤ Sym(X)` with `X` finite, and `k` any
field. Put `H = H_*(G; k)`, as a graded vector space with zero differential. Then

`H_*(G ≀_X P; k) ≅ H_*(P; H^{⊗X})`,

where `P` permutes the tensor factors with the Koszul sign. In particular
`H_0(P; H^{⊗X}) = (H^{⊗X})_P` is a direct summand of `H_*(G ≀_X P; k)`, graded by the
internal degree.

*Proof.* Let `F → k` be a free `kG`-resolution, and `W → k` a free `kP`-resolution. Then
`W ⊗ F^{⊗X}` is a free resolution of `k` over `k[G ≀_X P]`, with `G^X` acting on
`F^{⊗X}` factorwise and `P` acting diagonally, permuting the factors of `F^{⊗X}` with the
Koszul sign. This is Steenrod's construction; see Evens. Taking coinvariants in two
steps gives

`H_*(G ≀_X P; k) = H_*(W ⊗_P C^{⊗X})`, with `C = F ⊗_G k`.

`C` is a complex of `k`-vector spaces, so there are chain maps `f : H → C` and
`g : C → H` with `gf = 1`, and `f` is a quasi-isomorphism. The map `f^{⊗X}` commutes
with the signed permutation action, because it is the same map `f` in every factor and
`f` has degree `0`. By Künneth over a field, it is a quasi-isomorphism. `W` is a
bounded-below complex of free `kP`-modules, so `1 ⊗ f^{⊗X} : W ⊗_P H^{⊗X} → W ⊗_P C^{⊗X}`
is a quasi-isomorphism: filter by the degree in `W`, and compare the spectral sequences
at `E^1`. The left side has zero internal differential, so its homology is
`⊕_q H_*(P; (H^{⊗X})_q)`. The `P`-degree-0 part is `(H^{⊗X})_P`. ∎

No finiteness of `H_*(G; k)` is used. The characteristic of `k` enters only through the
signs, which are trivial in characteristic 2. (The characteristic restriction in
`fully-self-replicating-fp-infinity-groups-are-acyclic` is needed there only for the
equality `H_*(R) = (H^{⊗X})_P`, which uses the vanishing of `H_{>0}(P; −)`. The bound
here does not need it.)

## 2. Item 1: the coinvariant bound

Take `G = R` and compose with the isomorphism `R ≅ R ≀_X P`. By Proposition 1,
`(H^{⊗X})_P` in degree `n` is a direct summand of `H_n(R; k)`.

Choose a homogeneous basis `B` of `H` containing `1 ∈ H_0`. The basis tensors
`⊗_x b_x`, with `b_x ∈ B`, form a basis of `H^{⊗X}` on which `P` acts by signed
permutations. So `H^{⊗X} = ⊕_O k[O]_ε`, over `P`-orbits `O` of basis tensors. Here
`k[O]_ε ≅ Ind_{P_t}^P ε_t` for a representative `t ∈ O`, where `P_t` is the stabilizer of
`t` and `ε_t : P_t → {±1}` is its sign. Coinvariants are `k` if `ε_t = 1` in `k`, and `0`
otherwise.

- The orbits with one non-unit factor are indexed by `B ∖ {1}`, since `P` is transitive.
  Each has `ε = 1`, because a single factor gives no reordering sign. They contribute
  exactly `H_{>0}(R; k)`.
- The orbit of `1^{⊗X}` gives `k` in degree `0`.
- The rest is `E_*(k)`.

So `h_n ≥ h_n + dim E_n(k)`, and `E_n(k) = 0` when `h_n < ∞`. ∎

## 3. Item 2: excess classes

The Koszul sign of `g ∈ P_t` is the sign of the permutation that `g` induces on the
positions of the odd-degree factors of `t`.

(i) Let `t` have `u` at `x`, `v` at `y`, and `1` elsewhere, with `u ≠ v`. An element of
`P_t` must send the `u`-position to the `u`-position and the `v`-position to the
`v`-position. So `P_t = P_{x,y}`, the pointwise stabilizer. It moves no odd factor, so
`ε_t = 1`. Here `|X| ≥ 2` is used.

(ii) Let `t` have `u` at `x` and at `y`. `P_t` is the setwise stabilizer of `{x, y}`, and
`ε_t(g) = ±1`. In characteristic `2` this is `1`.

(iii) The proofs of 2(ii), 2(iii) and 3 in
`fully-self-replicating-fp-infinity-groups-are-acyclic-proof` use only the inequality
`h_n ≥ h_n + dim E_n` and sign computations. Both are now available over every `k`. ∎

## 4. Item 3: `FP_2`

If `R` is of type `FP_2`, then it is finitely generated, and `H_2(R; k)` is
finite-dimensional for every field `k`. That holds because `k` has a resolution by
finitely generated free `kR`-modules up to degree 2.

- If `H_1(R; F_2) ≠ 0`, then `E_2(F_2) ≠ 0` by 2(ii) with `a = 1`, contradicting item 1.
- If `dim_k H_1(R; k) ≥ 2`, then `E_2(k) ≠ 0` by 2(i) with `a = b = 1`, again a
  contradiction.

Write `H_1(R; Z) = Z^r ⊕ T` with `T` finite. `H_1(R; F_2) ⊇ (Z/2)^r ⊕ T/2T`, so `r = 0`
and `|T|` is odd. `dim H_1(R; F_p) = dim T/pT ≤ 1`, so every Sylow subgroup of `T` is
cyclic, and `T` is cyclic. ∎

## 5. Item 4: `FP_3`

Suppose `R` is of type `FP_3`, and let `p` divide `|H_1(R; Z)|`. By item 3,
`H_1(R; Z) = T` is finite. By universal coefficients,

`H_2(R; F_p) = H_2(R; Z) ⊗ F_p ⊕ Tor(T, F_p) ≠ 0`,

and `H_1(R; F_p) = T/pT ≠ 0`. Take basis classes `u` in degree `1` and `v` in degree `2`.
By 2(i), `E_3(F_p) ≠ 0`. But `H_3(R; F_p)` is finite-dimensional, since `R` is `FP_3`.
This contradicts item 1. So `T = 0`. ∎

The last sentence of item 4 of the claim is item 3 of
`self-wreathing-groups-are-not-fp-infinity`, with `k = 3` for `M_11` as cited there.

## 6. Item 5 and the applications

Item 5 is item 5 of `tits-hosts-for-transitive-local-actions`: the host is finitely
presented iff `R` is.

The applications only need the hypotheses of item 3. Each group below is fully
self-replicating with a transitive root image `M_11`, as stated in its node.

- `m11-separated-loop-host-has-b1-one`: `H_1 = Z ⊕ (finite)`, so `H_1(R'; F_2) ≠ 0`.
- `m11-torsion-linear-host-has-b1-one`: `b_1 = 1`.
- `fp-self-similar-finitely-supported-loops-give-characters`, item 4: an infinite loop
  character `Φ` gives `b_1 ≥ 1`, which gives `H_1(G; F_2) ≠ 0`.
- `m11-odometer-free-linear-host-h1-is-z55-squared`: `H_1 = (Z/55)²`, which is not
  cyclic.

In every case item 3 fails, so the group is not finitely presented, and by item 5
neither is its host.

## 7. The script

`nakaoka_mod_p_check.g` computes `dim H_2(W; F_p)` for finite `W = R ≀_X P` with GAP's
`AbelianInvariants` and `AbelianInvariantsMultiplier`, using universal coefficients. It
compares this with the degree-2 part of Proposition 1:

`H_2(R; F_p)^X_P ⊕ (Λ-or-S part of H_1^{⊗2})_P ⊕ H_1(P; H_1(R; F_p)^X) ⊕ H_2(P; F_p)`.

The third term is `h_1(R) · Σ_{orbits} dim H_1(P_x; F_p)`, by Shapiro's lemma. The
2-subset part is computed orbit by orbit: `h_1²` without a swap, `h_1(h_1+1)/2` with a
swap in characteristic `2`, and `h_1(h_1−1)/2` with a swap otherwise. The script covers 3
primes, 6 groups `R` and 6 groups `P`, for every pair with `|R ≀ P| ≤ 2000`. In all 70 cases it finds agreement, and its last line reports this
in every case. A failure at `p = 2` or `p | |P|` would have refuted the collapse used in
§1.

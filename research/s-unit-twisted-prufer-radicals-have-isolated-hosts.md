---
rg: 2
id: s-unit-twisted-prufer-radicals-have-isolated-hosts
kind: claim
title: Every finite sum of Prüfer modules K_𝔭/O_𝔭 (any number field, any prime above p, split, inert or ramified), twisted by 𝔭-adic S-units times unipotent integral matrices, is the normal corner radical of an isolated group; the only finite-presentation input is Kneser's criterion applied over Q to one Cornulier block group
distinct_from:
  twisted-prufer-corners-embed-in-isolated-cornulier-hosts: that proves the host theorem (Theorem A) for a given lattice datum and treats the full module K_p/O_p twisted by GL_r(Z[1/m']); this constructs the lattice datum for each single prime 𝔭 above p and every S-unit-times-unipotent twist, so irrational eigen-Prüfer twists at split, inert and ramified primes are all covered uniformly.
  partial-torus-abels-quotients-are-isolated: that handles completely split primes with 1×1 corners and one worked example (G_λ); this is the general statement for every number field and prime.
  every-decidable-group-embeds-in-an-isolated-group: that is CGP Question 4 in general; this supplies isolated hosts for every S-unit-twisted Prüfer radical, the ingredient needed for its soluble minimax case.
---

**ESTABLISHED** (lane proof, bh-free-60, 2026-09-19; elementary given the imports listed in the
route; not reviewed). No priority is claimed. The finite-presentation input is Kneser's criterion
(Abels, LNM 1261, 0.2.8) and Cornulier's verification of Abels' Theorem 3.1 for his block group
(arXiv:math/0502140v4, Lemmas 3.2, 3.6), both read at source and recorded in
`twisted-prufer-corners-embed-in-isolated-cornulier-hosts`.

## Statement

**Data.** For `i = 1, …, s`:
- a number field `K_i` with ring of integers `O_i`, a prime `𝔭_i` of `O_i` above a rational
  prime `p_i`, and an integer `k_i >= 1`;
- a finite set `T_i` of rational primes not containing `p_i`, with `m_i = p_i ∏_(T_i) q`;
- `S_i` = the primes of `O_i` dividing `m_i`, except `𝔭_i`; `O_(S_i)` = the `S_i`-integers;
- the **twist group** `Δ_i = O_(S_i)^× × U_(k_i)(O_i)`: scalar `S_i`-units, which are
  `𝔭_i`-adic units, times upper unitriangular `k_i × k_i` matrices over `O_i`. The two
  factors commute.

**Radical.** `D = ⊕_i D_i` with `D_i = (K_(i,𝔭_i)/O_(i,𝔭_i))^(k_i)`. As a group, `D_i` is
`(Q_(p_i)/Z_(p_i))^(k_i e_i f_i)`, with `e_i f_i = [K_(i,𝔭_i) : Q_(p_i)]`. `Δ_i` acts on `D_i`
by `x ↦ u N x`.

**Theorem.** There is an isolated group `Γ` containing `D` as a normal subgroup and containing
`Δ = ∏ Δ_i`, such that conjugation by `δ ∈ Δ` induces the given action on `D`. One can take
`Γ = ∏_i Γ_i`, where

    Γ_i = ( 𝐇_(r_i)(Z[1/m_i]) ⋊ Δ_i ) / O_(S_i)^(k_i),     r_i = k_i [K_i : Q].

Here `𝐇_r` is Cornulier's block group with blocks `(r, 3, 3, 1)`, as in
`twisted-prufer-corners-embed-in-isolated-cornulier-hosts`. Its corner `(*)_14` is identified
with `O_i[1/m_i]^(k_i) ≅ Z[1/m_i]^(r_i)` by restriction of scalars, and `Δ_i` acts on it by
multiplication.

**Consequently**, for any group `E` and homomorphisms `E → Δ_i`, the twisted radical `D` with
`E` acting through them lies in an isolated group. Special cases:
- rational S-units (`K = Q`);
- irrational `p`-adic units on one eigen-Prüfer factor at a split prime (for example `G_λ`,
  with `K = Q(√5)` and `𝔭 = (4+√5)` above 11);
- inert and ramified primes;
- Jordan blocks (`k >= 2`).

## Proof

Fix `i` and drop the index. Put `R = O[1/m]`, `L = O_S^k ⊆ R^k`.

1. **`R = O_(S ∪ {𝔭})`.** An element of `K` is in `O[1/m]` iff it is integral at every prime
   not dividing `m`. The primes dividing `m` are `S ∪ {𝔭}`.
2. **`R^k/L ≅ D` equivariantly.** Map `R → K_𝔭/O_𝔭`.
   - It is onto. Given `y = p^(-n) w`, `w ∈ O_𝔭`, the Chinese remainder theorem gives
     `w' ∈ O` with `w' ≡ w` mod `p^n O_𝔭`, and `p^(-n)w' ∈ R` maps to `y`.
   - Its kernel is `R ∩ O_𝔭 = O_S` (integral outside `S`).
   - It commutes with multiplication by `K`, so it is `Δ`-equivariant coordinatewise.
3. **Hypotheses (i)–(iii) of Theorem A.**
   - (i) For each `𝔮 ∈ S` choose `a_𝔮 ∈ O` with `𝔮^h = (a_𝔮)` (`h` the class number). Then
     `a_𝔮 ∈ O_S^× ⊆ Δ`, and `O_S = O[a_𝔮^(-1) : 𝔮 ∈ S]`: for `x ∈ O_S`, `x ∏ a_𝔮^N ∈ O` for
     large `N`. So `L` is generated as a `Z[Δ]`-module by `ω_j e_l`, with `(ω_j)` a `Z`-basis
     of `O` and `e_l` the standard basis of `O^k`.
   - (ii) If `Rx ⊆ L`, then `p^(-n)x ∈ O_𝔭^k` for all `n`, so `x = 0`.
   - (iii) `D ≅ (Q_p/Z_p)^(k[K_𝔭:Q_p])` is finitely cogenerated.
   - `L` is `Δ`-invariant: `S`-units and matrices over `O` preserve `O_S^k`.
4. **`Δ` is finitely presented and sits in `GL_r(Z[1/m])`.**
   - `O_S^×` is finitely generated abelian (Dirichlet's `S`-unit theorem; standard, not re-read).
   - `U_k(O)` is finitely generated torsion-free nilpotent.
   - Both are finitely presented, and the scalars are central, so the direct product is
     finitely presented.
   - `S`-units are units of `R`, so `Δ ≤ GL_k(R) ≤ GL_r(Z[1/m])` by restriction of scalars
     along `R ≅ Z[1/m]^([K:Q])`. This works because `O` is free over `Z`.
5. **Theorem A** of `twisted-prufer-corners-embed-in-isolated-cornulier-hosts`, with
   `(m, r, Δ, L)`, makes `Γ_i` finitely presented and finitely discriminable, hence isolated.
   Its normal subgroup `V/L ≅ R^k/L ≅ D_i` carries the `Δ_i`-action.
6. **Product.** A finite product of isolated groups is isolated
   (`ascending-hnn-of-isolated-groups-embed-in-isolated-groups`, item 1). `∎`

## Where each input is used

- **Finite presentation: only Kneser's criterion over Q.**
  - `𝐇_r(Q_q)` is compactly presented at every rational prime `q` (Cornulier's verification of
    Abels 3.1; its weights do not depend on `q`).
  - So `𝐇_r(Z[1/m])` is finitely presented (Kneser, Abels 0.2.8).
  - The number field never enters the algebraic group. No compact presentability over any
    `K_v`, no Weil restriction of `𝐇`, no strong approximation and no Behr's theorem are used.
- **The number field enters only through the module.** It enters through the corner module
  `R^k`, its lattice `O_S^k` (Chinese remainder theorem, class group) and the twist group
  (Dirichlet). So non-split primes cost nothing: the prime `𝔭` is chosen by the lattice.
- **The finite part of a Chernikov radical is not needed here.** In the soluble minimax
  reduction (Theorem B of the host node) it is absorbed by residual finiteness of `G/D`.

## Consequence for Question 4 on soluble minimax groups

By Theorem B of `twisted-prufer-corners-embed-in-isolated-cornulier-hosts`, a finitely generated
soluble minimax `G` embeds in an isolated group once, for each prime `p`, some homomorphism from
`G` to a `Γ` as above (or to any isolated group) is injective on `D_p[p]`. This node removes
every restriction on the *twist*, provided it is by S-units times unipotents. Two questions
remain OPEN:
- **Twist algebraicity.** Does every finitely generated soluble minimax group act on the
  composition factors of its divisible radical through S-units of number fields? Kropholler–Lorensen's
  π-integrality condition (arXiv:1510.07583, Theorem 1.13) is the likely source. It was not read
  in full.
- **Corner realizability.** Is the radical always reached, injectively on `D_p[p]`, by a map into
  such a corner?

## Lesson for general BH

**The number field lives in the module, not in the group.**
- Finite presentation is paid once, over `Q`, by Kneser's criterion for one Cornulier block
  group.
- Every number field, every prime above `p` (split, inert or ramified), every S-unit twist and
  every unipotent Jordan part enters only through the corner module `O_K[1/m]^k`, its lattice
  `O_S^k` and a finitely presented twist group (Dirichlet).
- Commutator descent to the corner then makes the quotient isolated.
- So for S-unit twists, the arithmetic side of Question 4 on soluble minimax inputs is complete.
  What remains is structural: whether every such input's radical is algebraic and reachable
  through a corner.

---
rg: 2
id: partial-torus-abels-quotients-are-isolated
kind: claim
title: Abels groups over S-integers of a number field in which the inverted primes split completely, extended by a group of outer diagonal automorphisms and divided by a suitable corner lattice, are isolated; so soluble minimax groups whose Prüfer radical is twisted by a rational S-unit (scaling by 2) or by an irrational p-adic unit (a golden-ratio unit at p = 11) embed in isolated groups
distinct_from:
  partial-torus-abels-quotients-are-finitely-presented-with-max-n: that claimed max-n for these hosts, which is false (Abels LNM 1261, 0.2.17); this proves the property actually needed, finite discrimination, so the hosts are isolated, and adds number-field corners.
  hall-type-prufer-quotients-embed-in-isolated-abels-groups: that is the central case over Z[1/p], via CGP Lemma 5.13; this handles a torus that acts nontrivially on the corner, where Lemma 5.13 does not apply.
  fg-soluble-minimax-groups-embed-in-fp-max-n-groups: that is the gate for all soluble minimax groups; this settles its two named test cases, G_2 and G_λ.
---

**ESTABLISHED** (lane proof, bh-free-60, 2026-09-18; elementary given the imports; not
reviewed). No priority is claimed.

## Imports

**H. Abels, *Finite Presentability of S-Arithmetic Groups. Compact Presentability of Solvable
Groups*, LNM 1261 (Springer 1987).** The Introduction was read at source: PDF downloaded on MSI
through institutional access and read page by page on 2026-09-18.
- *0.2.8 Theorem (Kneser 1964).* "The S-arithmetic subgroup Γ of G is finitely generated
  (finitely presented) iff G_{Q_p} is compactly generated (compactly presented) for every
  p ∈ S." Here `G` is a linear algebraic group over `Q`, and `S` is a finite set of primes.
- *0.2.17.* For `G_4 = {X ∈ GL_4 : X_11 = X_44 = 1, X_ij = 0 for i > j}`, "G_{4,Q_p} has a
  compact presentation". The same paragraph says Abels' group `Γ = G_{4,Z[1/p]}` answers
  negatively P. Hall's question whether every normal subgroup of a finitely presented
  soluble group is finitely normally generated: "In Γ even the center is not finitely
  generated, since it is Z_{Z[1/p]} ≅ Z[1/p]".
- The same criterion is quoted in Cornulier–de la Harpe, arXiv:1403.3796 §1.E.

**Other inputs.**
- CGP Prop. 5.6 (via `hall-type-prufer-quotients-embed-in-isolated-abels-groups`): `A_n(Z[1/q])`
  is finitely presented for every prime `q` and `n >= 4`. By Kneser, `𝐀_n(Q_q)` is then
  compactly presented.
- **Kneser, not strong approximation.** The input is Kneser's compact-presentation criterion.
  Strong approximation is not used. Restriction of scalars reduces the number-field case to
  the `Q`-form above, so no number-field statement is needed.

## Statement

**Data.**
- `K` is a number field with ring of integers `O`, and `m >= 2` is such that every prime
  `q | m` splits completely in `K`. Put `R = O[1/m]` and `n >= 4`.
- `𝐀_n(R)` is the group of upper triangular `n × n` matrices over `R` with `a_11 = a_nn = 1`.
- `Δ` is a finitely generated group of diagonal matrices `diag(δ_1, …, δ_(n−1), 1)` with
  `δ_i ∈ R^×`, and `P = 𝐀_n(R) · Δ ≤ GL_n(R)`.
- `Δ` acts on the corner `e_1n(R)`, the centre of `𝐀_n(R)`, by `χ(δ) = δ_1`.

**Hypotheses on `L ⊆ R`.**
- (i) `L` is a `χ(Δ)`-invariant subgroup, finitely generated as a `Z[χ(Δ)]`-module.
- (ii) `L` contains no `cR` with `c ≠ 0`.
- (iii) The abelian group `R/L` is finitely discriminable, that is, finitely cogenerated.

**Theorem.** `Γ = P/e_1n(L)` is finitely presented and finitely discriminable, hence isolated.

**Examples.**
1. **`G_2`** (radical scaled by `2`). As in
   `partial-torus-abels-quotients-are-finitely-presented-with-max-n` item 3, `G_2` embeds in
   `Γ_2`. Here `K = Q`, `m = 2p` with `p` an odd prime, `n = 4`,
   `Δ = ⟨diag(2,1,1,1)⟩`, and `L = Z[1/2]`. `R/L ≅ C_(p^∞)`, and the embedding given there
   applies unchanged.
2. **`G_λ`** (radical twisted by an irrational p-adic unit). Take `K = Q(√5)`,
   `O = Z[φ]` with `φ = (1+√5)/2`, `λ = φ^2`, and `11 = ππ'` with `π = 4+√5`, `π' = 4−√5`.
   - Let `R = O[1/11]`, and let `H_λ = N ⋊ ⟨s, a⟩`, where:
     - `N = {(ξ, η, ζ) : ξ, ζ ∈ R, η ∈ Z[1/11]}` with
       `(ξ,η,ζ)(ξ',η',ζ') = (ξ+ξ', η+η', ζ+ζ'+ξη')`;
     - `s(ξ,η,ζ) = (11ξ, 11^{-1}η, ζ)` and `a(ξ,η,ζ) = (λξ, η, λζ)`.
   - Put `G_λ = H_λ / {(0,0,ζ) : ζ ∈ O[1/π']}`. Then:
     - `G_λ` is a 4-generator soluble minimax group;
     - `τ(G_λ) = R/O[1/π'] ≅ K_π/O_π ≅ C_(11^∞)`;
     - `a` acts on `τ(G_λ)` by the image of `λ` in `Z_11^×`, which is irrational.
   - `G_λ` embeds in `Γ_λ` with `Δ = ⟨diag(λ,1,1,1), diag(π',1,1,1)⟩` and `L = O[1/π']`.

   As an abstract group, `R ≅ Z[1/11]^2`, and `a` acts through the companion matrix of
   `x^2 − 3x + 1` in `SL_2(Z)`.

## Proof

**1. Finite presentation.**
- `𝐀_n(R)` is commensurable with the S-arithmetic group of `G = R_{K/Q} 𝐀_n`, for `S` the
  primes dividing `m`.
- For `q ∈ S`, `G(Q_q) = 𝐀_n(K ⊗ Q_q) ≅ 𝐀_n(Q_q)^{[K:Q]}`, since `q` splits completely.
- A finite product of compactly presented groups is compactly presented: take the union of
  the compact generating sets, the relators of each factor, and the commutators between
  generators of different factors.
- So `G(Q_q)` is compactly presented, and `𝐀_n(R)` is finitely presented by Kneser (0.2.8).
- `P/𝐀_n(R)` is a quotient of `Δ`, which is finitely generated abelian. So `P` is finitely
  presented.
- `e_1n(L)` is central in `𝐀_n(R)` and `Δ`-invariant, so it is normal. By (i) it is the normal
  closure of finitely many elements. So `Γ` is finitely presented.

**2. Every nontrivial normal subgroup `M` of `Γ` meets `D = e_1n(R)/e_1n(L) ≅ R/L`.** Let `U`
be the unipotent upper triangular group over `R`, and `Z_1 ⊂ Z_2 ⊂ … ⊂ Z_(n−1) = U` its upper
central series. `Z_k` consists of the unipotent matrices supported on `j − i >= n − k`, and
`Z_1 = e_1n(R) ⊇ e_1n(L)`.
- **(A) `M` meets the image `Ū` of `U`.**
  - Let `g ∈ M` map to a diagonal `d ≠ 1`. Since `d_n = 1`, some simple root has
    `d_k ≠ d_(k+1)`.
  - Write `g = vd` with `v ∈ U`. For `x ≠ 0`, `[g, e_(k,k+1)(x)] ∈ M` is unipotent. Modulo
    `U' ⊇ Z_1` it equals `e_(k,k+1)((d_k/d_(k+1) − 1)x) ≠ 0`, so it is nontrivial in `Γ`.
- **(B) Descent to the corner.**
  - Take `1 ≠ h̄ ∈ M ∩ Ū` with lift `h ∈ Z_k − Z_(k−1)`. If `k = 1`, then `h̄ ∈ D − {0}`.
  - If `k >= 3`, some `u ∈ U` has `[u, h] ∈ Z_(k−1) − Z_(k−2)`. That element is not in
    `Z_1 ⊇ e_1n(L)`, so its image lies in `M` and is nontrivial.
  - For `k = 2`, `h` has `h_(1,n−1) ≠ 0` or `h_(2,n) ≠ 0`. Then `[e_(n−1,n)(x), h]` or
    `[e_(1,2)(x), h]` equals `e_1n(±xc)` with `c ≠ 0`. By (ii) some `x ∈ R` has `xc ∉ L`.
- **(C) Conclusion.** `M ∩ D` is a nontrivial subgroup of `D`. By (iii) it contains one of the
  finitely many elements of a cogenerating set of `D`, which is therefore a discriminating
  set for `Γ`.

**3. The examples.**
- **Embedding `G_λ`.** `φ(ξ,η,ζ) = I + ξE_12 + ηE_24 + ζE_14` is an injective homomorphism
  `N → U`. Put `s ↦ diag(1, 11^{-1}, 1, 1) ∈ 𝐀_4(R)` and `a ↦ diag(λ, 1, 1, 1) ∈ Δ`. These
  scale `(E_12, E_24, E_14)` by `(11, 11^{-1}, 1)` and `(λ, 1, λ)`, as `s` and `a` do.
  Moreover `φ(0,0,ζ) ∈ e_14(L)` iff `ζ ∈ O[1/π']`.
- **Hypotheses (i)–(iii).**
  - (i): `Z[λ^{±1}, π'^{±1}] = O[1/π']`, because `Z[λ] = Z[φ] = O`. So `L` is generated by `1`.
  - (ii): `cπ^{−N} ∉ O[1/π']` for large `N`.
  - (iii): `R/O[1/π'] ≅ K_π/O_π ≅ Q_11/Z_11`, since `O` is a PID (class number 1) and
    `R = O[1/π, 1/π']`.
- **The radical of `G_λ`.** `λ` acts on `K_π/O_π` through the π-adic embedding. `H_λ/N` and
  `N/z(R)` are torsion-free, so `τ(G_λ) = z(R)/z(O[1/π'])`.
- **Generation.** Conjugates of `(1,0,0)` by `s^i a^j` span `Z[λ^{±1}][1/11] = R`, and
  commutators fill the corner.
- **`G_2`.** Take `K = Q`, `R = Z[1/2p]`, `Δ = ⟨diag(2,1,1,1)⟩` and `L = Z[1/2]`. The
  hypotheses are immediate, and `diag(1, p^{-1}, 1, 1) ∈ 𝐀_4(R)`. `∎`

## Consequence

`G_2` and `G_λ` satisfy Cornulier–Guyot–Pitsch Question 4. So do all their finitely generated
overgroups inside the `Γ`'s, and finite products and finite extensions of those. Boone–Higman
for them is OPEN.

## Lesson for general BH

**Isolation needs one invisible corner, not Noetherianity.**
- In an S-arithmetic unipotent-by-diagonal host, a nontrivial diagonal part produces
  unipotents by commutators, and unipotents descend by commutators to the corner. So every
  normal subgroup reaches the corner, and a finitely cogenerated corner quotient makes the
  host finitely discriminable.
- Finite presentation comes from Kneser and Abels, and restriction of scalars carries it to
  any number field at primes that split completely.
- An outer torus that sees only some primes, or only one prime above `p`, twists the Prüfer
  radical by any S-unit, rational or not. So the soluble inputs that no locally moving host
  carries have isolated arithmetic hosts. For them Question 4 is arithmetic, and it is
  strictly more accessible than Boone–Higman.

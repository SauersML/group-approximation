---
rg: 2
id: fg-soluble-minimax-groups-embed-in-fp-max-n-groups
kind: claim
title: Every finitely generated soluble minimax group embeds in a finitely presented group with max-n (weak form, which suffices for CGP Question 4 on this class, a homomorphism to such a group injective on the periodic radical)
distinct_from:
  isolated-embedding-of-soluble-minimax-groups-via-max-n-hosts: that proves this gate implies Cornulier–Guyot–Pitsch Question 4 for all finitely generated soluble minimax groups; this is the gate itself.
  fg-soluble-minimax-groups-satisfy-boone-higman: that asks for a finitely presented simple overgroup; this asks only for a finitely presented Noetherian (max-n) one.
  partial-torus-abels-quotients-are-finitely-presented-with-max-n: that is the family of hosts that settles the known cases; this is the statement for every input.
---

Inputs this claim recorded under the older schema (not a proof; they do not establish it): `isolated-embedding-of-soluble-minimax-groups-via-max-n-hosts`.

**OPEN** (stated by bh-free-60, 2026-09-18).

**Update (2026-09-18): the max-n formulation is not the operative one.**
- **Max-n is too strong.** Finitely presented soluble minimax groups need not have max-n:
  Abels' `A_4(Z[1/p])` has a centre that is not finitely normally generated (LNM 1261, 0.2.17).
  A host with a normal Prüfer subgroup never has max-n.
- **The operative open question** is Question 4 on this class: a homomorphism from `G` to an
  *isolated* group that is injective on `τ(G)`. That suffices by item 2 of
  `isolated-embedding-of-soluble-minimax-groups-via-max-n-hosts`.
- **Both named test cases are settled** in that form by
  `partial-torus-abels-quotients-are-isolated`: `G_2` (radical scaled by `2`) and `G_λ`
  (radical twisted by an irrational 11-adic unit).
- **This max-n statement stays OPEN.** It is implied by Boone–Higman for soluble minimax groups,
  since finitely presented simple groups have max-n.


**Statement.** Every finitely generated soluble minimax group `G` embeds in a finitely presented
group with max-n.

**Weak form.** There is a homomorphism from `G` to a finitely presented max-n group that is
injective on the periodic radical `τ(G)`.
- This suffices for Question 4: the proof of item 3 of
  `isolated-embedding-of-soluble-minimax-groups-via-max-n-hosts` only uses injectivity on its
  finite set `Φ ⊆ τ(G)`.
- One may pass to a quotient of `G` by any normal subgroup maximal among those missing `Φ`.
  That quotient is finitely discriminable, and for finitely discriminable inputs the weak form
  is the full statement.

## Structure of the reduced inputs (lane proof, elementary)

Let `G` be finitely generated, soluble, minimax and finitely discriminable.
- Every minimal normal subgroup `M` of `G` is finite elementary abelian.
  - `M` is abelian, since `M'` is normal in `G` and properly contained in `M`.
  - If `M` has torsion, then some `M[p]` is normal and nontrivial, so `M = M[p]`. An
    elementary abelian minimax group is finite.
  - If `M` is torsion-free, then `qM ≠ M` for some prime `q`, since a torsion-free minimax
    abelian group is not divisible (`Q` is not minimax). Then `qM` is a smaller nontrivial
    normal subgroup, a contradiction.
- So `G` has a finite socle that meets every nontrivial normal subgroup.
- If `G` is infinite, it is not residually finite (CGP: residually finite and finitely
  discriminable implies finite), so `τ(G)` is infinite.

## Literature (searched 2026-09-18)

- **Metabelian case.** Baumslag (1973) and Remeslennikov (1973): every finitely generated
  metabelian group embeds in a finitely presented metabelian group. Those satisfy max-n (P.
  Hall). Standard; not re-read.
- **Abels (1979) and CGP §5.4.** `A_n(Z[1/p])` is finitely presented for `n >= 4`, while Hall's
  `A_3` is not. Read in CGP.
- **Kropholler–Lorensen**, *Virtually torsion-free covers of minimax groups* (arXiv:1510.07583;
  Ann. Sci. ENS 2020), main theorem read in HTML. Every finitely generated virtually soluble
  minimax group is a quotient of a virtually torsion-free one, with the Fitting subgroup, derived
  length and nilpotency class preserved.
  - They make no claim that the kernel is central or polycyclic.
  - Their Question 1.6 asks whether it can be taken abelian, and they expect a negative answer.
  - So covers alone do not produce max-n overgroups in which the kernel stays normal.
- **Kneser (1964)**, as quoted in Cornulier–de la Harpe, arXiv:1403.3796 §1.E: `𝐆(Z_S)` is
  finitely presented iff every `𝐆(Q_p)`, `p ∈ S`, is compactly presented.
- **Not found.** No statement of this gate, or of its failure, was found for soluble minimax
  groups. Lennox–Robinson, *The Theory of Infinite Soluble Groups* (2004), Ch. 11 treats
  finitely presented soluble groups, but it was not accessible here.

## Known cases

1. **Residually finite `G`.** Not needed for the weak form, since then `τ(G)` is finite.
2. **Central Prüfer radical of Hall–Abels type.** `hall-type-prufer-quotients-embed-in-isolated-abels-groups`.
3. **Prüfer radical twisted by rational S-units.** `partial-torus-abels-quotients-are-finitely-presented-with-max-n`.
   Every finitely generated subgroup of `(A_n(Z[1/m]) ⋊ Δ)/e_1n(L)` is a case. This includes
   `G_2`, whose Prüfer radical is scaled by `2`.

## The next test case (open)

**The group `G_λ`.**
- Let `A ∈ SL_2(Z)` be hyperbolic with eigenvalues `λ^{±1} ∈ Z_p`, with `p` split in `Q(λ)`
  and `λ ≢ λ^{-1}` mod `p`.
- Build the Heisenberg-type group `H = N ⋊ ⟨s, A⟩`:
  - coordinates `x ∈ Z[1/p]^2`, `y ∈ Z[1/p]` and corner `z ∈ Z[1/p]^2`, with `z = x·y`;
  - `s` acts by `(p, p^{-1}, 1)`, and `A` acts by `(A, 1, A)`.
- `Z[1/p]^2/Z^2 = E_λ ⊕ E_{λ^{-1}}` splits into eigen-Prüfer groups. Let `L'` be the preimage
  of `E_{λ^{-1}}`, and put `G_λ = H/L'`.
- Then `τ(G_λ) ≅ C_(p^∞)`, and `A` acts on it by the irrational p-adic unit `λ`.

**Why the hosts above miss it.**
- In the corner realization over `Z[1/m]` (rational partial-torus Abels hosts), `L'` is not finitely normally generated. Elements
  acting on the corner by units preserve orders in `E_{λ^{-1}}`, and elements acting by `p`
  do not normalize `L'`.

**Candidate host.**
- Over `O = Z[λ]`, take `π` generating a power of the prime `𝔭` above `p`, and let
  `R' = O[1/π]`. Then `R'/O ≅ Q_p/Z_p`, with `λ` acting by multiplication.
- So `(A_4(R') ⋊ ⟨λ⟩)/e_14(O)` would work. Its finite presentation needs Kneser's theorem over
  number fields for `S = {𝔭}` alone. That was not read, since the Q-form quoted above covers
  only the `S`-integers of `Q`.

## Attempts

1. **Partial-torus Abels hosts (bh-free-60, 2026-09-18).** They settle known cases 2 and 3.
   What remains is Prüfer radicals twisted by irrational p-adic units, and non-abelian
   Chernikov actions.
   - The general mechanism: finite presentation comes from an S-arithmetic core (Kneser and
     Abels).
   - A non-arithmetic outer torus makes the lattice kernel normal and finitely normally
     generated.

## Lesson for general BH

- **The invariant.** Question 4 for soluble minimax groups is governed by how the group acts on
  its Prüfer radical.
  - Central actions need Hall–Abels corners.
  - Actions by rational S-units need one outer torus.
  - Algebraic but irrational units need number-field Abels groups at a single prime above `p`.
- **Why it matters.** Every such host is finitely presented and max-n, hence residually
  isolated. So the remaining problem is arithmetic: finite presentation of partial-torus
  S-arithmetic groups. It is not a word-problem problem.

## Attempts (continued)

2. **Isolated partial-torus hosts over number fields (bh-free-60, 2026-09-18).**
   `partial-torus-abels-quotients-are-isolated` settles `G_λ`.
   - **Inputs.** Kneser's criterion (Abels LNM 1261, 0.2.8, read at source) and compact
     presentability of `𝐀_4(Q_q)` (0.2.17).
   - **How it works.** Restriction of scalars to `Q` makes `𝐀_4(O_K[1/m])` finitely presented
     at split primes. Commutator descent to the corner makes the quotient finitely
     discriminable.
   - **Next tests (open).**
     - (a) Primes that do not split completely, where `𝐀_n(K_v)` for a proper extension
       `K_v/Q_p` needs Abels' criterion 0.2.18 over `K_v`.
     - (b) Radicals of rank at least 2 with non-semisimple (Jordan-block) actions.
     - (c) Chernikov radicals whose finite part acts non-trivially.

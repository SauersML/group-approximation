---
rg: 2
id: self-wreathing-groups-are-not-fp-infinity
kind: claim
title: A group isomorphic to its own wreath product R wr_X P over a nontrivial finite P retracts onto every iterated wreath product of P, so H_k(R) contains H_k(P)^n for all n in the first nonzero degree k of P; R is never FP_infinity, never finitely generated if P is not perfect, and never finitely presented if P has nontrivial Schur multiplier, which kills every section-closed Tits host with local action A_(d+1)
artifacts:
  - experiments/self-wreathing-homology-2026-09-17/iterated_wreath_multipliers.g
  - experiments/self-wreathing-homology-2026-09-17/iterated_wreath_multipliers.out
  - experiments/self-wreathing-homology-2026-09-17/explicit_central_extension.g
  - experiments/self-wreathing-homology-2026-09-17/explicit_central_extension.out
distinct_from:
  fully-self-replicating-fp-infinity-groups-are-acyclic: that works away from |P|, where the Lyndon-Hochschild-Serre sequence collapses, and derives acyclicity from the hypothesis FP_infinity; this works at the primes dividing |P|, using the split complement and its iterated wreath powers, and shows the hypothesis FP_infinity is never met, and finite presentation fails outright for root image A_d.
  fully-self-replicating-tree-groups-give-fg-tits-hosts: that reduces finite presentation of the Tits host Gamma_R to finite presentation of R; this proves R is never finitely presented when the root image is A_d, so that reduction lands on an impossible statement.
  tits-independence-vertex-groups-are-branch-type: that shows vertex groups of locally finite (P)-hosts are branch-type and asks for a finitely presented branch group; this settles the self-branching case R = R wr_X P negatively for every P with a nontrivial Schur multiplier or abelianization, and leaves branching over proper subgroups open.
---

**ESTABLISHED (unreviewed).** Proof: `self-wreathing-groups-are-not-fp-infinity-proof`.
The degree-one and degree-two growth is checked in GAP by the attached scripts.

**Setting.** `P` is a nontrivial finite group acting on a finite nonempty set `X`
(any action). `A ≀_X P = A^X ⋊ P`, with `P` permuting coordinates. `W_1 = P` and
`W_{n+1} = W_n ≀_X P`, the `n`-level iterated wreath product. `R` is any group with an
isomorphism `R ≅ R ≀_X P`. No tree, no finite-state or contraction hypothesis, and no
transitivity is assumed.

Let `k ≥ 1` be the least degree with `H_k(P; Z) ≠ 0`. It exists, since a nontrivial
finite group has nonzero integral homology in some positive degree.

**Theorem.**

1. **Retracts.** Every `W_n` is a retract of `R`.
2. **Growth.** `H_j(W_n; Z) = 0` for `0 < j < k`, and
   `H_k(W_{n+1}; Z) ≅ H_k(W_n; Z)^{o} ⊕ H_k(P; Z)`, where `o ≥ 1` is the number of
   `P`-orbits on `X`. So `H_k(P; Z)^n` is a direct summand of `H_k(W_n; Z)`.
3. **Obstruction.** `H_k(R; Z)` contains `H_k(P; Z)^n` as a direct summand for every
   `n`, so it is not finitely generated. Hence `R` is **not of type `FP_k`**, and in
   particular **not of type `FP_∞`**. The same holds over `F_p` for each prime `p`
   dividing `|H_k(P; Z)|`.
4. **Special cases.**
   - (a) If `P` is not perfect (`k = 1`), `R` is **not finitely generated**. This covers
     `A_3` and `A_4`, and every solvable `P`.
   - (b) If `P` is perfect with `H_2(P; Z) ≠ 0` (`k = 2`), `R` is **not finitely
     presented**, and `dim H_2(R; F_p) = ∞` for each `p` dividing the Schur multiplier.
     This covers `A_d` for every `d ≥ 5`, where the multiplier is `Z/2`, or `Z/6` for
     `d = 6, 7`.
   - (c) If `P` is superperfect (`H_1 = H_2 = 0`), the theorem gives failure of `FP_k`
     for some `k ≥ 3`, and nothing about finite presentation.

**What it does to the Tits route of `boone-higman-conjecture` (Attempt 8).**

- `fully-self-replicating-tree-groups-give-fg-tits-hosts` builds the simple amalgam
  `Γ⁺ = (R ≀ A_{d+1}) *_{R×R} (R ≀ A_{d+1})` from any fully self-replicating
  `R ≤ Aut(X*)` with root image `A_d`. Such an `R` is isomorphic to `R ≀_X A_d`, and
  `Γ⁺` is finitely presented iff `R` is.
- By item 4, no such `R` is finitely generated for `d = 3, 4`, and none is finitely
  presented for `d ≥ 5`. So **no section-closed host `Γ_R` with local action `A_{d+1}`
  is finitely presented, for any `d`**. This holds whatever the contraction behaviour,
  so it also covers the non-contracting candidates that Bartholdi's theorem leaves open.
- Option (a) of the previous lane asked for a `Z[1/d!]`-acyclic `FP_∞` fully
  self-replicating group with root image `A_d`. It does not exist, for any root image,
  by item 3. The `FP_∞` hypotheses of
  `fully-self-replicating-fp-infinity-groups-are-acyclic` are never satisfied.
- It gives a new proof, independent of contraction, that the certified instance
  `R = ⟨A_5, b⟩` is not finitely presented: `H_2(R; Z) ⊇ (Z/2)^n` for every `n`.

**What survives.** The argument uses only a split complement `P ≤ R` and the
self-similar structure. Two classes are untouched:

- **Superperfect root images.** Replacing `A_{d+1}` by a transitive `F ≤ Sym(d+1)` whose
  point stabilizer `F_0` is superperfect, for instance `M_12 ⊃ M_11` on 12 points or
  `M_24 ⊃ M_23` on 24 points, gives a host with `Γ⁺ = (R ≀ F) *_{R×R} (R ≀ F)` and
  `R ≅ R ≀ F_0`. Here the theorem only says that `R` is not `FP_k` for the least nonzero
  degree `k ≥ 3` of `F_0`. The script checks that `M_11` is perfect with trivial
  multiplier. For `M_23` the trivial multiplier is cited, not computed. For `M_11` the least
  `k` is `3`, since `H^*(M_11; F_2)` has its first generator in degree `3` (Benson--Carlson;
  cited, not checked here).
- **Non-split self-branching.** Locally finite (P)-hosts whose half-tree rigid stabilizer
  `R` has `R^X` as a normal subgroup with finite quotient but no complement. The
  retraction of item 1 is unavailable there.

**Calibration.**

- `P = Z/2` on two points: `W_n` is the Sylow 2-subgroup of `Sym(2^n)`, whose
  abelianization is `(Z/2)^n`, as item 2 predicts.
- `P = Z/3` and `A_4`: the script finds `H_1(W_n) = (Z/3)^n` for `n ≤ 4` and `n ≤ 3`.
- `P = A_5`: item 2 predicts `H_2(A_5 ≀ A_5) = (Z/2)^2`. The second script builds a
  perfect central extension of `A_5 ≀ A_5` with kernel `(Z/2)^2` from `SL(2,5)`, so the
  multiplier maps onto `(Z/2)^2`.
- `R = Fin(A_d)`, the finitary group, satisfies `R ≅ R ≀ A_d`. It is locally finite and
  not finitely generated, so nothing is contradicted.
- Trivial `P` is excluded, and must be: Tyrer Jones gives finitely presented groups
  `G ≅ G × G`, which is `R ≅ R ≀_X 1` with `|X| = 2`.
- Acyclic infinite `P` would escape the argument, which needs `H_k(P) ≠ 0`. This is why
  the statement is restricted to finite `P`.

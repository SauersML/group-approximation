---
rg: 2
id: self-wreathing-groups-have-full-sigma-invariants
kind: claim
title: A finitely generated group R isomorphic to R wr_X P has full BNS invariant, full Sigma^n over every field below degree |X| when it is FP_n, and zero L2-Betti numbers below degree |X|, so no character, Sigma-invariant or L2 argument can show a fully self-replicating group is not finitely presented
distinct_from:
  fully-self-replicating-fp-infinity-groups-are-acyclic: that computes ordinary homology H_*(R;k) as P-coinvariants of the tensor power and gets b_1 <= 1 for finitely presented R; this is about the invariants attached to infinite-order characters (Bieri-Neumann-Strebel-Renz Sigma^n) and to the regular representation (L2-Betti numbers), which that node does not touch, and it shows they carry no obstruction at all below degree |X|.
  self-wreathing-groups-are-not-fp-infinity: that obstructs FP_infinity through the finite retracts W_n of R; this proves the complementary blindness of the infinite-order invariants, which is what the open superperfect case of the Tits route would have to use.
  tits-hosts-for-transitive-local-actions: that proves finite-quotient and retract arguments are blind at FP_2 when the root image is superperfect; this extends the blindness to character-kernel, Bieri-Strebel HNN and L2 arguments, for every finite transitive root image.
---

**ESTABLISHED (unreviewed).** Proof: `self-wreathing-groups-have-full-sigma-invariants-proof`.
Item 1 is proved from scratch there. Items 2 and 3 use cited standard theorems
(the Bieri--Geoghegan product formula over a field, Bieri--Renz finite-index
invariance, and Lück's Künneth and finite-index formulas).

**Setting.** `X` is a finite set with `d = |X| ≥ 2`, `P ≤ Sym(X)` is transitive, and
`R ≠ 1` is a finitely generated group with an isomorphism `ψ : R ≅ R ≀_X P = R^X ⋊ P`.
Every fully self-replicating `R ≤ Aut(X*)` with root image `P` is an example, through its
section map. `S(R)` is the character sphere `(Hom(R, ℝ) ∖ 0)/ℝ_{>0}`.

**Theorem.**

1. **BNS.** `Σ¹(R) = S(R)`. Hence every normal subgroup `N ≥ [R, R]` of `R` is
   finitely generated. In particular `[R, R]` is finitely generated, and so is `ker χ`
   for every character `χ : R ↠ ℤ`.
2. **Higher Σ over a field.** Let `k` be a field and `1 ≤ n ≤ d − 1`. If `R` is of type
   `FP_n` over `k`, then `Σ^n(R; k) = S(R)`. So every `N ≥ [R, R]` is of type `FP_n` over `k`.
3. **L²-Betti numbers.** `b_j^{(2)}(R) = 0` for `0 ≤ j ≤ d − 1`. No finiteness hypothesis
   is needed. If `R` is finitely presented, its deficiency is at most `1`, and this also
   holds for every finite-index subgroup.
4. **Characters restrict diagonally.** For every nonzero `χ ∈ Hom(R, ℝ)`, the character
   `χ ∘ ψ^{-1}` restricted to `R^X` equals `(λ, …, λ)` for one nonzero `λ ∈ Hom(R, ℝ)`,
   with `λ(r) = χ(ψ^{-1}(r at coordinate x))` for every `x`.

**What this kills.** These are the obstruction families to `FP_2` that use
infinite-order structure rather than finite quotients.

- **Bieri--Strebel.** A finitely presented group with a character to `ℤ` is an HNN
  extension with finitely generated base and associated subgroups. If it has no
  non-abelian free subgroup, the extension is ascending in one direction. Polynomial-activity
  automaton groups have no free subgroups (Sidki). So the natural argument against a
  finitely presented polynomial-activity `R` with `b_1(R) = 1` would show that `ker χ` is
  not an ascending union of conjugates of a finitely generated subgroup. By item 1, it
  **dies**: `ker χ` is always finitely generated, so `±χ ∈ Σ¹` and both ascending
  descriptions hold.
- **BNS/Renz Σ-invariants.** These invariants cannot separate a finitely presented `R`
  from a non-finitely-presented one. By items 1 and 2 they are the whole sphere as far
  as the ambient finiteness allows.
- **L²-Betti numbers, deficiency and Euler characteristic.** A finitely presented group
  has `b_2^{(2)}` finite. When `d ≥ 3`, item 3 gives `b_2^{(2)}(R) = 0` outright, so
  these invariants cannot contradict finite presentation either.

With `tits-hosts-for-transitive-local-actions` item 7 and
`fully-self-replicating-fp-infinity-groups-are-acyclic`, the following are now all
blind at `FP_2` in the superperfect case of the Tits route of `boone-higman-conjecture`:

- finite quotients;
- retracts;
- rational homology (up to the constraint `b_1 ≤ 1`);
- character invariants;
- `L²` invariants.

What remains are arguments that see the defining relators themselves. Examples are
Bartholdi-type branch/L-presentation arguments, which need contraction, and direct
Dehn-function or asymptotic-cone arguments.

**What it does not do.** It proves nothing about finite presentation in either
direction. A finitely presented `R` with `b_1(R) = 1` and `d ≥ 3` would have
`ker χ` of type `FP_2` over every field. It would also be finitely presented
*if* Meinert's inequality holds over `ℤ` (cited, not checked here). Such a
kernel would contradict nothing that is known.

**Calibration.**

- `ℤ² = ℤ × ℤ` is not of the form `R ≀ P`, but item 1's product step reproduces the
  standard fact that `Σ¹(ℤ²)` is the whole circle.
- `F_2 × F_2`: `Σ¹(F_2)` is empty, and the product formula makes the complement of
  `Σ¹(F_2 × F_2)` exactly the two subspheres `χ_1 = 0` and `χ_2 = 0`. So
  `(χ_1, χ_2) ∈ Σ¹` iff both components are nonzero, as the product step of item 1
  predicts. The diagonal characters used here avoid both subspheres.
- The finitary group `Fin(P)` satisfies `Fin(P) ≅ Fin(P) ≀ P` but is locally finite with
  `S = ∅`, consistent with items 1 and 3 (all `b^{(2)}_j` vanish). It is not finitely
  generated, so item 2 is vacuous there.
- `R = ⟨M_11, b⟩` of `tits-hosts-for-transitive-local-actions` has finite abelianization,
  so `S(R) = ∅`. The non-contracting candidate `m11-linear-activity-self-replicating-group`
  has `b_1 ≤ 2`, since only its generators `a` and `c` can have infinite image in
  `H_1`. If `b_1 = 2`, it is not finitely presented by
  `fully-self-replicating-fp-infinity-groups-are-acyclic`. If `b_1 ≤ 1`, this theorem
  shows that its characters carry no obstruction.

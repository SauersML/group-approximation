---
rg: 2
id: lifted-thompson-t-chromatic-codes-force-t-nonhyperlinear
kind: claim
title: "Every bounded-area commutator code in the lifted Thompson group descends to Thompson's T and to every rotation centralizer with a nontrivial mark, so the whole chromatic-code approach to T-bar requires T to be non-hyperlinear and hence non-sofic"
distinct_from:
  infinite-chromatic-commutator-code-kills-mf-mark: that is the sufficient criterion in operator norm for one presented group; this pushes a T-bar code to the quotients T and C_T(r_k), proves the pushed mark is nontrivial, and proves the normalized Hilbert--Schmidt version of the criterion, so a T-bar code refutes hyperlinearity of T.
  thompson-t-is-sofic: that is the open soficity of T; this proves that soficity (even hyperlinearity) of T rules out every bounded-area commutator code in T-bar, in T, and in each C_T(r_k), for every mark.
  lifted-thompson-t-is-not-mf: that is the target of the codes; this measures what any code-based proof of it would also prove.
  non-hyperlinear-group: that asks for some nonhyperlinear group; this shows a T-bar code would make T itself that group.
artifacts:
  - research/lifted-thompson-t-chromatic-codes-force-t-nonhyperlinear-proof.md
---

**ESTABLISHED (written proof; not Lean-verified).**  Proof route:
`lifted-thompson-t-chromatic-codes-force-t-nonhyperlinear-proof`.

## Setting

Fix a finite presentation `T̄ = ⟨S | R⟩` of the lifted Thompson group with
the central translation `z(x) = x+1` given by a word.  For `k >= 0` put

```text
Q_k = ⟨S | R ∪ {z^(2^k)}⟩ ≅ T̄/⟨z^(2^k)⟩ ≅ C_T(r_k),   Q_0 ≅ T
```

(`lifted-thompson-t-quotients-are-rotation-centralizers`).  A *commutator
code* in a presented group is the data of
`infinite-chromatic-commutator-code-kills-mf-mark`.  It consists of:

- a graph `G` with `chi(G) = infinity`;
- a mark word `x`;
- words `c_v, h_v, a_v` for each vertex, satisfying (CCC1) with constant
  `A_Delta` and (CCC2) with constant `A_0`.

## Statement

1. **(Descent.)**  A commutator code in `T̄` with mark `x` is, with the same
   words and constants, a commutator code in every `Q_k`.  If `x != 1` in
   `T̄`, then its image is nontrivial in every `Q_k`, and in particular in
   `T`.
2. **(Hilbert--Schmidt criterion.)**  Let `Gamma` be finitely presented.
   Suppose `Gamma` carries a commutator code whose mark `x` is nontrivial
   in `Gamma`.  Then `Gamma` is not hyperlinear, and hence not sofic.
3. **(Cost of the chromatic class.)**  Suppose `T̄` carries a commutator code
   with a nontrivial mark.  Then:
   - `T` is not hyperlinear, and so not sofic;
   - every `C_T(r_k)` is not hyperlinear;
   - `V` and `2V` are not sofic;
   - `T` is an explicit nonhyperlinear group.

   Contrapositively, a sofic or hyperlinear `T` rules out every commutator
   code, for every mark, in `T̄`, in `T` and in each `C_T(r_k)`.  This kills
   the whole chromatic-code approach to `lifted-thompson-t-is-not-mf` and to
   `thompson-t-has-full-mf-radical`.

## What this changes

- **Hidden prerequisite.**  The chromatic lane on `lifted-thompson-t-is-not-mf`
  (waves 17--19) carries an unlisted prerequisite, `not thompson-t-is-sofic`.
  That prerequisite can fail.
  - It is strictly stronger than the lane's own target seen from `T`:
    a non-MF `T` says nothing about hyperlinearity.
  - It resolves the root `non-hyperlinear-group`.
  - For this reason, a bounded answer to the one Dehn-function question left
    by `lifted-thompson-t-template-envelope-contains-shift-graphs`
    (`sup Area([k c k^(-1), h]) < infinity` over the triple-shift arcs)
    would prove `T` nonhyperlinear.  It need not prove the same of `F`.
- **Where the mark lives does not matter.**  The descent holds for every
  code, central or not.  A mark cannot be a nonzero power of `z` (Step 2 of
  the proof), so no code on `T̄` is invisible from `T`.  No choice of mark
  avoids the cost.
- **Metric independence.**  The proof uses only bi-invariance and the
  finiteness of covering numbers.  So the same conclusion holds for
  approximation by any compact groups with bi-invariant metrics, for
  example symmetric groups with the normalized Hamming metric.
- **Remaining non-code routes are unaffected.**  The eigencorner route
  (`lifted-thompson-t-not-mf-via-central-eigencorners`) and the uniform-gap
  reformulation for rotation centralizers are operator-norm statements that
  need not imply non-hyperlinearity.  They are the lanes of the target that
  do not pay this cost.

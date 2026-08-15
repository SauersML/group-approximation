---
rg: 2
id: atlas-kernel-window-length-nine
kind: claim
title: No atlas relator list of X-length below nine can ever be usable
distinct_from:
  atlas-relator-central-sufficiency: that characterizes which lists are usable; this proves every list of short words fails the characterization, via a finite-quotient screen, and pins the exhaustion stopping point at nine or more.
  finite-quotient-blindness: that is the compression collapse in finite quotients of the Kun--Thom pair; this uses a finite-quotient obstruction in the opposite direction — a surviving finite quotient certifies a relator list as insufficient — for the atlas source of a different group.
artifacts:
  - research/artifacts/atlas-relator-extraction-2026-08-15.md
  - experiments/atlas_relator_projection_screen.py
  - experiments/atlas_relator_finite_quotient_screen.py
  - experiments/atlas-kernel-radius5-summary.json
---

Let `P̄ = A₈ * A₈ ↠ Q`, `R̄ = ker`, `N̄ = [P̄, R̄]` as in
`atlas-relator-central-sufficiency`, and let X-length be word length in
the twelve adjacent-transvection generators.

**Theorem.**

1. **(Screen.)**  If a homomorphism `φ : P̄ → F` onto a nontrivial finite
   group kills every word of a finite `T ⊆ R̄`, then `N̄ ≰ ⟨⟨T⟩⟩` and `T`
   is unusable.  (A usable `T` makes `P̄/⟨⟨T⟩⟩` a perfect central
   extension of the infinite simple `Q`, and such a group has no
   nontrivial finite quotient: a finite-index normal subgroup has central
   or full image in the simple quotient, forcing an abelian — hence
   trivial — finite quotient by perfectness.)
2. **(Computation.)**  Every kernel element of X-length at most `8` lies
   in the kernel of the retraction `(p₁,p₂) : A₈ * A₈ ↠ A₈ × A₈`: the
   radius-4 spanning-tree generators (2,734 words) all die under it, and
   by the recorded exhaustion lemma
   (`docs/FALSE_RECURSIVE_ATLAS_EXHAUSTION.md`, Proposition 4) they
   generate every kernel element of X-length `≤ 8` as a subgroup.  The
   bound is sharp: a kernel word of X-length `9` with nontrivial factor
   projections exists at the radius-5 boundary.
3. **(Consequence.)**  Every usable relator list must contain a word of
   X-length at least `9`; the cumulative families `C_L` (`L ≤ 8`) and
   `D_r` (`r ≤ 4`) of the recursive-exhaustion program are all provably
   insufficient, and its stopping point satisfies `L₀ ≥ 9`.  In
   particular the twenty radius-2 kernel words — the repo's "first
   rigorous small target" — cannot be a relator list, though they remain
   valid necessary constraints for the nonhyperlinearity direction.

Two structural notes.  Enumeration alone can never certify a list — it
produces subgroups of `R̄`, never an upper bound on `N̄` — so a
certificate must come from the algebra side
(`atlas-steinberg-rank-five-translation`).  And the earlier
constraint-scan sweeps missed exactly the degenerate sector this theorem
exploits: their maps had both factor restrictions injective, while the
surviving quotient kills one factor outright.  Of the 234 radius-5
boundary words, 178 are already certified trivial in `U_Q` — they lie in
`N̄` and contribute nothing beyond it — leaving 4 cyclic classes as the
only enumerated candidates for nonzero classes in `R̄/N̄ = H₂(Q, ℤ)`.

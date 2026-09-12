---
rg: 2
id: stw99-problem-lxxx-central-sequence-characters
kind: claim
title: Character-free central sequence algebras force Z-stability (STW Problem LXXX, Kirchberg-Rordam)
root: true
artifacts:
  - research/artifacts/stw99-final-band-cluster-2026-08-30.md
---

**Problem LXXX of Schafhauser--Tikuisis--White, arXiv:2506.10902**
(Kirchberg--Rordam, IJM Question 3.1).  If `A` is unital separable and
`A_ω ∩ A'` has no characters, is `A` `Z`-stable?

## Attempts

* `Z`-stability IS a statement about `A_ω ∩ A'` (a unital copy of
  `Z`, equivalently of some `Z_{n,n+1}`), so this problem is exactly
  the Dadarlat--Toms/Jiang--Su embedding problem (LXV) specialized to
  central sequence algebras: route `stw99-lxv-implies-lxxx` — LXV's
  expected characterisation (no finite-dimensional representations ⟹
  unital `Z`-embedding) applied to `B = A_ω ∩ A'` needs only the
  known upgrade from "no characters" to "no finite-dimensional
  representations" for central sequence algebras (Kirchberg--Rordam
  prove `A_ω ∩ A'` has a character iff it has a finite-dimensional
  representation in the relevant setting), plus the ω-saturation
  fact that a unital `Z` copy in `A_ω ∩ A'` gives `Z`-stability of
  `A`.  So LXXX is the central-sequence face of the Global-Glimm/LXV
  complex; saturation actually HELPS here (the coherence residue of
  LXV trivializes in ultrapowers: scale-wise `Z_{n,n+1}`-embeddings
  for all `n` combine by countable saturation), so LXXX may be
  STRICTLY EASIER than LXV — recorded: LXXX follows from Global
  Glimm (LXXIII) for `A_ω ∩ A'` alone, since GGP gives all
  `(n,n+1)`-divisibilities and saturation assembles them.  This
  makes LXXIII ⟹ LXXX the sharper route
  (`stw99-lxxiii-implies-lxxx`).

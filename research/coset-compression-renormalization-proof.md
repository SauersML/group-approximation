---
rg: 2
id: coset-compression-renormalization-proof
kind: route
title: Right-coset self-cover plus torsion collapse plus stable-kernel factorization
target: coset-compression-renormalization
requires:
  - compression-torsion-collapse
  - radical-automorphization
  - pushforward-limit-kernel-is-the-union-of-stage-kernels
artifacts:
  - research/artifacts/radical-renormalization-2026-08-23.md
---

Well-definedness is the one-line calculation
`g gamma s^-1 Gamma = g s^-1 (s gamma s^-1) Gamma = g s^-1 Gamma`.
Surjectivity uses the preimage `g s Gamma`; equivariance is immediate.  The
`n`-th iterate is right multiplication by `s^-n`, so eventual equality is
membership of `h^-1 g` in `union_n s^-n Gamma s^n`, i.e. equality in
`G/Gamma_infty`.

For an element `a` of a countable abelian torsion lamp group at `s Gamma`, the
compressed subgroup `s Gamma s^-1` fixes the site, while the `Gamma`-orbit
consists of commuting coordinate lamps.  `compression-torsion-collapse`
therefore identifies every pair in the first fibre in every corona
representation.  Conjugating by `G` gives all fibres, and these pair differences
generate the pushforward kernel.  Thus `ker R_s <= Rad_MF`.  Apply
`radical-automorphization`; the formalized pushforward-limit kernel theorem
identifies its stable kernel with the pushforward kernel to `G/Gamma_infty`.
The MF terminal-quotient clause follows from the exact radical quotient
criterion.  For countable torsion-generated `K`, the existing
fibre-abelianization argument is inserted at the first stage and the remaining
iterations run on `K_ab`.

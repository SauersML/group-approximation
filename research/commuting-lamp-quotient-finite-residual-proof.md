---
rg: 2
id: commuting-lamp-quotient-finite-residual-proof
kind: route
title: Blindness on the module side plus level folding
target: commuting-lamp-quotient-finite-residual
requires: [commuting-lamp-quotient-structure, finite-quotient-blindness]
artifacts:
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
---

## Direct proof

*`L_0` dies.*  Let `phi` map the quotient to a finite group, put
`M = F_2[X]/(ker phi cap F_2[X])`.  `M` is finite, so the action
`V -> GL(M)` has a finite-index normal kernel `N` acting trivially.
Blindness in the finite group `V/N` gives `q(Gbar_k) = q(Gbar)` for every
`k`, hence `q(T) = q(Gbar)`, i.e. `T <= Gbar . N`.  Conjugating by any `g`
with `x = g Gbar` and using normality of `N` gives
`T <= Stab_V(x) . N`.  Levels are `T`-orbits, so for same-level `x, x'` write
`x' = h x` with `h = sigma n`, `sigma in Stab_V(x)`, `n in N`; then in `M`,
`m_{x'} = sigma . (n . m_x) = m_{sigma x} = m_x`.  Same-level pairs span
`L_0`, so `L_0 <= ker phi`.

*Nothing else dies.*  `V` is a finitely generated subgroup of `GL_4(Q)`,
hence residually finite by Malcev, which separates every element with
nontrivial `V`-part.  A nonzero level-parity vector of diameter `< m` is
separated by folding `Z` to `Z/m`, giving the finite quotient
`(sum_{Z/m} F_2) semidirect (V / level^{-1}(mZ))`.  Section 4 of the cited
note is the complete argument.

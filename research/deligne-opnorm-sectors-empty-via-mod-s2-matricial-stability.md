---
rg: 2
id: deligne-opnorm-sectors-empty-via-mod-s2-matricial-stability
kind: route
title: Untwist a Maslov model to Mod(S_2), perturb it to an exact representation by matricial stability, and hit the operator-norm Torelli-scalar gap
target: deligne-nontrivial-maslov-opnorm-sectors-are-empty
requires:
  - mod-s2-real-untwisting-identifies-deligne-norm-parameters
  - mod-s2-is-point-norm-matricially-stable
  - mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap
---

Notation as in `mod-s2-real-untwisting-identifies-deligne-norm-parameters`. The two nontrivial
mod-three Maslov multipliers are represented by `c_(1/3)` and `c_(2/3)`. Point-norm models for
cohomologous multipliers correspond: multiply `U_n` by the `T`-valued 1-cochain. So the gate fails
iff `1/3` or `2/3` lies in `P_op`, that is, iff `1/3` lies in `P_op`.

**Proof.** Suppose the gate fails. Then `1/3` lies in `Z_op` by (U4), so there are point-norm
asymptotic homomorphisms `V_n : M -> U(d_n)` with `||V_n(t_s) - omega I||_op -> 0`. The same
holds for `omega^2` after complex conjugation.

By `mod-s2-is-point-norm-matricially-stable`, even in its weaker form, there are honest
representations `rho_n` of `M` on `C^(d_n)` with `||rho_n(t_s) - V_n(t_s)||_op -> 0`. So
`||rho_n(t_s) - omega I||_op -> 0`, which contradicts
`mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap`. QED.

## Why this decomposition

- **Each prerequisite can fail on its own.**
  - The gap is *necessary* for the flagship (see its node). If it fails, `Rad_MF(E_3) = C_3` is refuted.
  - The stability claim is independent of Deligne's arithmetic. It can fail through an
    almost-flat obstruction invisible to rational homology, and then this route dies with the
    flagship still open.
- **It meets the calibration of the gate.** The attempt by w6-deligne-last2 on
  `deligne-nontrivial-maslov-opnorm-sectors-are-empty` says a genuinely easier proof must use
  something normalized-HS limits lose: operator-norm liftability, or the finite dimension. Matricial
  stability of `M` is exactly operator-norm liftability, with the dimension fixed. The
  normalized-HS analogue `mod-s2-exact-models-are-fd-character-limits-of-deligne-sectors` (E3) needs
  *flexible HS* stability, which is a different hypothesis.
- **It avoids the recorded failure modes.**
  - The tensor-cube and lifting attempts over `Sp_4(Z)` died on matricial instability of `Sp_4(Z)`
    through Dadarlat windings. On `M` the Maslov class is a real coboundary (U1), and `H_2(M;Q) = 0`.
  - The ISW operator-norm transplant died because coronas only see `lim theta_n`. Here there is no
    moving parameter: the untwisted models are ordinary asymptotic homomorphisms of one fixed group.
  - The flexible-subgroup class kill does not apply, because stability is used for `M` itself.

**Equivalence under stability.** If `mod-s2-is-point-norm-matricially-stable` holds, then
`Z_op = Z_hon`, so the flagship holds **iff** the gap holds.

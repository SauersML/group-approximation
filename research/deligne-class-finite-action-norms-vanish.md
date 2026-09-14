---
rg: 2
id: deligne-class-finite-action-norms-vanish
kind: claim
title: The Deligne class of Sp_4(Z) has vanishing Hamming norm along finite Sp_4(Z)-actions
distinct_from:
  deligne-class-congruence-cosystole-bounded-below: that asks for a positive lower bound along some descending chain with trivial intersection, possibly non-cofinal; this asks for the infimum over ALL finite actions to be 0, which fails every such bound and needs vanishing only along a cofinal chain.
  deligne-triple-cover-is-sofic: that is soficity of E_3; this is a finite-action sufficient condition for it, and under stability of Sp_4(Z) in finite actions an equivalent one.
artifacts:
  - research/artifacts/sk-deligne-sofic-2026-09-14-part1.md
---

**OPEN.** Let `alpha in H^2(Sp_4(Z), Z/3)` classify Deligne's triple cover `E_3`. Then
`inf_X nu_X(alpha) = 0` over finite `Sp_4(Z)`-sets `X`, with `nu_X` the normalized defect of the best torsor cochain on
the presentation complex of the action (`finite-actions-with-vanishing-class-norm-make-extension-sofic`).

**Why it matters.**
- It implies `deligne-triple-cover-is-sofic` (route `deligne-triple-cover-sofic-from-vanishing-finite-norms`), hence
  Alekseev--Thom Open problem 6.1.
- If `Sp_4(Z)` is stable in finite actions, it is equivalent to soficity of `E_3`
  (`stable-finite-actions-extension-sofic-iff-class-norm-vanishes`).

**Well posed and not vacuous.**
- `nu_X(alpha) > 0` on every finite `X`, since `Res_fin(E_3) = C_3`. Only the infimum can vanish.
- Remark, with the congruence subgroup property recalled and not re-read (Mennicke 1965, Bass--Milnor--Serre 1967):
  the infimum is the limit of `nu_(Gamma/Gamma(k!))(alpha)` over the principal congruence covers. See artifact §4.

## Attempts
- **Exact monomial truncations.** Dead (`deligne-monomial-twisted-modules-have-no-folner-truncations`). A witness
  sequence must vary its cochains with `n`.
- **Detecting-cycle floors.** `4 nu / A_0(N)` and `[Gamma:N] <= m A_0(N)` do not refute it: `A_0(N)` grows with the
  systole.
- **Cycle packing and property (T).** Packing gives `(log m)^-2`; (T) controls dimension 1 only (attempts recorded on
  `deligne-class-congruence-cosystole-bounded-below`).
- **Local patching.** Heuristic evidence AGAINST, since tilings of the non-amenable symmetric space have walls of
  constant volume fraction. Non-local constructions are not excluded.

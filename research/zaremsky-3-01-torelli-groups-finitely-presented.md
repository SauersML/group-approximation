---
rg: 2
id: zaremsky-3-01-torelli-groups-finitely-presented
kind: claim
title: "Zaremsky Problem 3.1 resolved: are the Torelli groups of Out(F_n), MCG(S_g) and Aut(F_n) finitely presented for large n or g?"
root: true
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 3, Problem 1, verbatim:
"Is the Torelli group of Out(Fn) (or MCG(Sg), or Aut(Fn)) finitely presented for
large enough n or g?"

This claim is the question. It is established only through the answer route
`zaremsky-3-01-by-all-three-families`, which requires one resolution claim per
family:

- `zaremsky-3-01-out-torelli-resolved`: the Torelli group
  `T_n = ker(Out(F_n) -> GL_n(Z))`;
- `zaremsky-3-01-surface-torelli-resolved`: the Torelli group
  `I_g = ker(Mod(S_g) -> Sp_{2g}(Z))` of the closed oriented surface of genus `g`;
- `zaremsky-3-01-aut-torelli-resolved`: `IA_n = ker(Aut(F_n) -> GL_n(Z))`.

Each resolution claim has exactly two admissible routes, one per answer. Never
write a `requires: []` route into this claim or into a resolution claim.

**Reading.** "For large enough n or g" is read as eventual finite presentability.
The yes-answer for a family says there is `n_0` (or `g_0`) such that every member
beyond it is finitely presented. The no-answer is the negation: infinitely many
members are not finitely presented. Results about a single parameter (for example
"`T_4` is not finitely presented") are partial and land as their own claims.

**Why "large enough".** The small cases are settled:

- `T_1` and `T_2` are trivial (Nielsen), so `IA_2 = Inn(F_2) ≅ F_2`.
- `T_3` is not finitely presented (Krstić–McCool, 1997). Bestvina–Bux–Margalit
  recover this from their Main Theorem (2), `H_{2n-4}(T_n; Z)` infinitely
  generated for `n >= 3`, at `n = 3` (arXiv:math/0603177). By
  `ia-n-fp-iff-outer-torelli-fp`, `IA_3` is not finitely presented either.
- `I_1` is trivial; `I_2` is not finitely generated (McCullough–Miller) and is an
  infinitely generated free group (Mess); `I_g` is finitely generated for `g >= 3`
  (Johnson). These are recorded in Kassabov–Putman, Math. Ann. 376 (2020), §1.

So the open cases are `n >= 4` for `T_n` and `IA_n`, and `g >= 3` for `I_g`.

**Two families have one answer.** For every `n >= 2`, `IA_n` is finitely presented
exactly when `T_n` is (`ia-n-fp-iff-outer-torelli-fp`). For `g >= 2`, finite
presentability of the Torelli group does not change when one marked point or one
boundary component is added (`surface-torelli-fp-invariant-under-puncture-and-boundary`).

**Status** (bounded check of arXiv listings on 2026-09-13; MathSciNet not
reached). No claimed answer was found for any open case. Kassabov–Putman (2020, §1):
"it is not known whether `I_g^b` is finitely presentable for `g >= 3`". Ershov
(arXiv:2601.01377, January 2026): "It is a long-standing open problem whether the
subgroup of IA-automorphisms `IA_n = Ker ρ_ab` is finitely presented for `n >= 4`."
He also
records that finite presentability of the surface partial Torelli groups is open
apart from the case `d = 0`. The homological obstruction in degree 2 has been
removed for surfaces: `H_2(I_g; Z)` is finitely generated for `g >= 4` (Gaifullin,
arXiv:2606.13517, Theorem A, preprint). The survey artifact
`research/artifacts/zp-torelli-finite-presentability-status-2026-09-13.md` gives
sources and the method map.

## Attempts

- 2026-09-13 (lane z3-01-torelli): the question, the family decomposition, the
  equivalences and the status map land first. Attacks are recorded on the six
  answer claims.
- 2026-09-17 (sw-096, transplanter, host-geometry): **Bieri–Geoghegan CAT(0)
  Σ-invariants.** The non-abelian transplant of the Renz Σ² route reads finite
  presentability of a point stabilizer off `Σ²(ρ)` for a cocompact, discrete-orbit
  isometric action `ρ` of the (type `F_∞`) ambient group on a proper CAT(0) space.
  Dead for all three families: `torelli-groups-are-not-cat0-cocompact-stabilizers`
  shows no such action of a finite-index subgroup of `Out(F_n)`, `Aut(F_n)`
  (`n >= 3`) or `Mod(S_g)` (`g >= 3`) has a stabilizer commensurable with the Torelli
  group. Exact step: the action would make a finite-index subgroup of `GL_n(Z)` or
  `Sp_{2g}(Z)` (modulo a finite group) a CAT(0) group, but it contains a Heisenberg
  group, which the Solvable Subgroup Theorem forbids. Open residue: actions whose
  stabilizers have infinite, virtually abelian image in `GL_n(Z)`.

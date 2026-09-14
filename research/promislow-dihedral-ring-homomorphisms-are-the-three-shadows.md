---
rg: 2
id: promislow-dihedral-ring-homomorphisms-are-the-three-shadows
kind: claim
title: Every ring homomorphism from Z[P] to the definite dihedral ring is one of the three shadows up to an endomorphism, so Case A units are exactly the units it cannot see
distinct_from:
  promislow-integral-units-have-monomial-definite-line-shadows: that constructs three homomorphisms Z[P] -> D(Z) and proves units are monomial under them; this proves those three are all of them, up to endomorphisms of D(Z) and sign characters.
  promislow-shadow-kernel-intersection-is-line-vanishing: that computes where Case A units live inside Z[P]; this characterizes Case A as invisibility under every homomorphism into D(Z).
  promislow-nonzero-twisted-classes-have-no-definite-shadows: that shows the twisted rings of nonzero classes have no homomorphism into D(Z); this classifies the homomorphisms of the zero class.
  integral-unit-conjecture-torsion-free: that is Higman's conjecture; this proves no triviality.
artifacts:
  - research/artifacts/hl-kaplansky-class-shadows-2026-09-14.md
  - research/artifacts/hl-kaplansky-class-shadows-2026-09-14/class_shadow_check.py
  - research/artifacts/hl-kaplansky-class-shadows-2026-09-14/class_shadow_check-run.log
---

**ESTABLISHED** by `promislow-dihedral-ring-homomorphism-classification-proof`.
Unreviewed; no novelty claimed.

Notation as in `promislow-integral-units-have-monomial-definite-line-shadows`:
`P` is the Promislow group, `D(Z) = Z[t^(+-1)]<u | u^2 = -1, u t = t^-1 u>`, and
`A`, `B`, `C` are the shadows with kernels `I_A`, `I_B`, `I_C`.

1. **Classification.** For signs `eps_1, eps_2` and integers `m_1, k_2`,
   `t -> eps_1 t^(m_1)`, `u -> eps_2 t^(k_2) u` defines a ring endomorphism `e` of
   `D(Z)`. Every unital ring homomorphism `phi: Z[P] -> D(Z)` is either
   - `e o S` for one such `e` and one `S in {A, B, C}`; or
   - a sign character, with `phi(a), phi(b) in {+-1}`.

   Which case holds is read off from `phi(a)` and `phi(b)`:
   - `A`: `phi(a) = +-t^m` and `phi(b) = +-t^k u`;
   - `B`: the mirror image;
   - `C`: both of the form `+-t^m u`.
2. **Case A is D(Z)-invisibility.** A unit `v` of `Z[P]` lies in
   `epsilon + (I_A cap I_B cap I_C)` for a sign `epsilon` exactly when every
   unital ring homomorphism `Z[P] -> D(Z)` sends `v` to `+-1`.
3. **Twisted classes.** For a nonzero class `[c]`, `Z^c[P]` has no unital ring
   homomorphism into `D(Z)` at all
   (`promislow-nonzero-twisted-classes-have-no-definite-shadows`).

**What this means for the integral problem on `P`.** Every input of the form
"map into `D(Z)` and use its monomial units" is exhausted by the three shadows.
The Case A units that main leaves open are precisely those such inputs cannot
see. So closing Case A needs a target outside `D(Z)`, and by the twisted claim
that target must still see the zero class.

The natural candidates are the degree-2 algebras on the other `K4`-fixed lines,
over formally real fields without `sqrt(2)`. They do see the class, but their unit
groups are infinite: on the line `x, y -> +1` the quotient is `Z[D_inf]`, which
has the unit `1 + (1-a)b(1+a)` (checked in the artifact). In degree 4 no
analogue of the sum-of-squares identity `N(X) = X X*` is known.

**Exact gap.** A class-sensitive rigidity input for units of `Z[P]` that does
not factor through `D(Z)`. Candidates that would qualify:
- a positivity or height statement on the degree-4 fibres that fails over
  `Z[zeta_8]`;
- a global (non-fibrewise) integrality argument.

None is known. This claim proves that no refinement of the `D(Z)` shadows can
supply one.

DERIVATION
[[promislow-dihedral-ring-homomorphism-classification-proof]]

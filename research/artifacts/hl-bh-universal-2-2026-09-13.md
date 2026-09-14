# Boone–Higman universal routes, second pass: complexity wall for covered actors, and the shell gate for Z^2, 2026-09-13

Lane `hl-bh-universal-2`. Target: `boone-higman-conjecture`, through the live universal
routes in `research/artifacts/hl-bh-universal-route-map-2026-09-13.md`.

## Verdict

- **Route (b), covered Cantor-module actors.** Whether the complexity wall applies is not
  decided. Section 1 records why this is not a cheap test. The unbounded direction implies
  the OPEN `type-a-actors-with-arbitrarily-hard-word-problem`. The bounded direction needs
  a classification of commutants of covering subgroups of `V`. No claim is landed.
- **Route (a), shell stabilizers.** Three theorems and one citation import, all
  ESTABLISHED in Cairn and not independently reviewed; no novelty is claimed.
  - `shell-ascending-gate-is-a-finite-window-inclusion`: the ascending gate is equivalent
    to one finite inclusion `s^-eps lambda(P) s^eps <= <s^(eps j) lambda(P) s^(-eps j) : 0 <= j <= N>`.
  - `square-spiral-z2-enumeration-passes-the-finite-window-gate`: the square spiral
    enumeration of `Z^2` passes the gate with `N = 2`. This is the first gate witness for
    an input that is not virtually cyclic, and it has `B` strictly larger than
    `lambda(P)`, as the one-ended obstruction requires.
  - `square-spiral-z2-near-shift-group-is-not-finitely-presented`: for the same
    enumeration `R_nu` is metabelian and not finitely presented, so `Q`, `F_nu` and `A_1`
    are not finitely presented.
  - `fp-groups-without-free-subgroups-split-ascendingly-over-kernels`: the citation
    import (Cornulier–de la Harpe, Corollary 8.C.4).
- **Exact failing clause for spiral `Z^2`.** Finite presentation of the near shift group
  `R_nu`, not the ascending gate.

## 1. Route (b): the complexity wall for covered actors

**Setting.** `M = C(C, F_2)` with Thompson's `V` acting by precomposition. `W` is *covered*
if `W = <V, x_1, ..., x_r>` and each `x_j` commutes with some `C_j <= V` whose translates of
finitely many functions span `M`.

**What is automatic.** A finitely presented covered `W` gives a finitely presented
orbit-finite affine actor `M ⋊ W` (`amalgamated-module-extensions-are-fp`), hence a type (A)
actor. So `W` has solvable word problem. The question is only whether one recursive time
bound covers the whole class.

**The unbounded direction implies an open problem.** A covered `W` that beats every
recursive bound is a type (A) actor subgroup with arbitrarily hard word problem. By the
hard-actors chain on main, that yields `fp-simple-groups-with-arbitrarily-complex-word-problem`.
So a separating example is at least as hard as that OPEN question.

**The bounded direction needs commutants.**
- Each `x_j` is determined by finitely many images. Computing `x_j f` needs a decomposition
  of `f` over `F_2[C_j]`, so the complexity is governed by `End_(F_2[C_j])(M)` and by the
  subgroup `C_j`.
- Computed examples:
  - for `C = V` the commutant is `{0, id}` (on main);
  - for `C = V_[0] x V_[1]` it is finite dimensional;
  - for the diagonal `{s_0 h t_0 + s_1 h t_1}` it is `M_2(F_2)`.
- Gadget: for any covering `D <= V` and any linear `H` commuting with `D`,
  `x_H = 1 + s_00 H t_01` is an automorphism (its nilpotent part squares to 0). It commutes
  with the covering subgroup `{s_00 h t_00 + s_01 h t_01 + s_1 k t_1 : h in D, k in V}`.
  So covered generators are at least as rich as commutants of covering subgroups.
- A uniform bound would need every such commutant, together with the decomposition
  problem, to be uniformly computable. I found no argument and no counterexample.

**Status.** Route (b) stays live. It dies exactly when commutants of covering subgroups of
`V` are uniformly computable in bounded time.

## 2. Route (a): the finite-window form of the gate

`shell-ascending-gate-is-a-finite-window-inclusion` (proof
`shell-ascending-gate-finite-window-proof`):
- `ker(eta) = <c_k : k in Z>` with `c_k = s^k lambda(P) s^-k`.
- A finitely generated exhausting `B` lies in a finite window `<c_k : |k| <= M>`.
  Exhaustion forces every far negative label into that window, and a conjugation moves the
  window to nonnegative labels containing `c_-1`.
- Conversely `B = W_N` satisfies `B <= s B s^-1`, absorbs all negative labels by
  induction, and exhausts.

The gate is therefore certified by finitely many words, the identities for `s^-1 lambda_g s`.

## 3. The square spiral enumeration of Z^2

**Successor map.** `sigma` is a four-piece translation, with the piece decided by the signs
of `a = x - y` and `b = x + y`:

| piece | condition | step |
|---|---|---|
| `R` | `a > 0, b > 0` | `+e2` |
| `T` | `a <= 0, b > 0` | `-e1` |
| `Lf` | `a < 0, b <= 0` | `-e2` |
| `B` | `a >= 0, b <= 0` | `+e1` |

**Window corrections.** For `j = -1, 1, 2, 3` and `h = +-e1, +-e2`,
`sigma^j L_h sigma^-j = L_h . delta_j(h)`. Here `delta_j(h)` is a product of one-step shifts
along diagonal half-lines, and the pattern is ring independent (`vectors.json`, rings 60,
61, 90, 91, no other defects). Encoding shift amounts as Laurent polynomials:
- quadrant I half-lines `a = c` as `t^c` (`Q1`), and quadrant III as `Q3`;
- quadrant II and IV half-lines `b = d` as `u^d` (`Q2`, `Q4`).

The label-`j` vectors satisfy `Q3 = -t^j Q1` and `Q4 = -u^(j+1) Q2`. Translation `L_k`
multiplies by `t^(k1-k2)` and `u^(k1+k2)`.

**Solving for the label `-1` vectors.** Take `delta_-1(e1) = (Q1, Q2) = (1, 1)`. Solving
`p_1 + p_2 = 1`, `t p_1 + t^2 p_2 = t^-1` gives `p_1 = 1 + t^-1 + t^-2`,
`p_2 = -(t^-1 + t^-2)`, and similarly in `u`. These are realized by three translates of
`delta_1(-e1)` and by `delta_2(e1)`. The identities are

    sigma^-1 L_e1 sigma = L_e1 . delta_1(-e1) . T_(-e1)(delta_1(-e1)) . T_(-2e1)(delta_1(-e1)) . delta_2(e1)
    sigma^-1 L_e2 sigma = L_e2 . T_(1,-1)(delta_1(-e2)) . T_(0,-1)(delta_1(-e2)) . T_(-1,-1)(delta_1(-e2)) . delta_2(e2)

**Exact check.** `spiral_verify.py`, `RMAX=240` on MSI, covers radius 40 to 228 (202608
points): the piece formula, `word_e1` and `word_e2` all have 0 mismatches (`verify.json`). The
proof route reduces "at all but finitely many points" to this annulus through diagonal
invariance.

**Search record.** A brute-force search over words of length at most 3, in translations
and window conjugates of labels 1 or 1–2, found nothing (`search13.txt`, `search23.txt`).
The actual identities use about 20 letters, which is why the certificate came from the
Laurent computation rather than from search.

## 4. Why spiral Z^2 still fails

- **Metabelian structure.** `R_nu = <L_e1, L_e2, sigma>` has derived subgroup inside the
  abelian group `D` of diagonal line shifts.
- **The character.** `chi_1` (offset change on quadrant-I half-lines: `L_h -> h1 - h2`,
  `sigma -> -1`) is a surjective homomorphism. The quadrant-I coordinate of `R_nu'` is a
  nonzero ideal `I` of `Z[t^(+-1)]`.
- **The contradiction.** A finite presentation would give an ascending splitting of
  `ker(chi_1)` over a finitely generated `H` (Cornulier–de la Harpe Corollary 8.C.4; no
  free subgroups). In the class-2 nilpotent quotient `ker(chi_1)/(R_nu' ∩ ker pi_1)`, `H`
  meets the central copy of `I` in a finitely generated subgroup. Its shifts in one
  direction cannot exhaust `I`.
- **In Bieri–Strebel language.** `R_nu'` is not tame, since the characters `+-chi_1` are
  both in the complement of Sigma.

## 5. Updated status of route (a)

`decidable-inputs-have-fp-shell-stabilizers` stays OPEN. For one-ended inputs a successful
enumeration must now satisfy:
1. window width at least 1 (`one-ended-shell-inputs-admit-no-shift-normalizing-enumeration`);
2. a finite window inclusion (Section 2);
3. a finitely presented near shift group `R_nu`.

Clause 2 is satisfiable for `Z^2`. The heuristic lesson from Section 4: enumerations whose
successor map is a finite-piece polyhedral translation produce Houghton-type line-shift
modules on which `R_nu` acts through characters of rank one, and those are never tame.
This is proved here only for the square spiral. A witness needs a successor map whose
corrections do not form a rank-one Laurent module, for example strips with nontrivial
periodic dynamics, or a non-solvable `R_nu`.

## Files

- `research/shell-ascending-gate-is-a-finite-window-inclusion.md`,
  `research/shell-ascending-gate-finite-window-proof.md`
- `research/square-spiral-z2-enumeration-passes-the-finite-window-gate.md`,
  `research/square-spiral-z2-finite-window-gate-proof.md`
- `research/square-spiral-z2-near-shift-group-is-not-finitely-presented.md`,
  `research/square-spiral-z2-near-shift-group-not-fp-proof.md`
- `research/fp-groups-without-free-subgroups-split-ascendingly-over-kernels.md`,
  `research/fp-groups-without-free-subgroups-ascending-splitting-citation.md`
- `research/artifacts/hl-bh-universal-2-2026-09-13/`: `spiral_common.py`,
  `spiral_vectors.py`, `spiral_verify.py`, `vectors.json`, `verify.json`, `search13.txt`,
  `search23.txt`

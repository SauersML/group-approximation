# sk-rigidity-ring: plan (2026-09-13)

Lane `sk-rigidity-ring` (SK swarm; rules in the coordinator's scratchpad `sk/RULES.md`). Target: the sharpest TRUE
statement of what `G_X = EL_3(LC(X,F_2) ⋊_T Z)` remembers about the minimal subshift `(X,T)`, proved through ring
theory. Open target on main: `subshift-elementary-group-isomorphism-forces-orbit-equivalence`.

## The chain
- **(a) Group to ring.** `EL_3(R_X) ≅ EL_3(R_Y)` should give a ring isomorphism or anti-isomorphism
  `M_3(R_X) ≅ M_3(R_Y)`.
  - Known only for `GL_3` with `q` odd (`subshift-gl3-iso-gives-matrix-ring-iso-odd-q`, via Zel'manov 1985, which
    needs `1/2`).
  - The note's case `q = 2`, `n = 3`, `G = E_3` is the crux.
- **(b) Ring to K-theory.**
  - A ring (anti-)isomorphism preserves `(K_0, K_0^+, [1_{M_3}])`, with `[1_{M_3}] = 3[1]`.
  - `K_0(R_X) = C(X,Z)/(1−T)` (`subshift-crossed-product-k0-is-coinvariant-group`).
  - The cone `K_0^+(R_X)` equals the HPS cone. One inclusion comes from nonnegative functions. For the other, a
    nonzero idempotent class is strictly positive on every state (Ara–Claramunt faithful `rk_μ`, plus states =
    invariant measures), and a strictly positive element of a simple dimension group is positive.
- **(c) Unit, then GPS.**
  - Dimension groups are torsion-free, so a group isomorphism sending `3[1_X]` to `3[1_Y]` sends `[1_X]` to `[1_Y]`.
    That removes the "height-3 Kakutani towers" caveat recorded in the target's Attempts.
  - Giordano–Putnam–Skau then give strong orbit equivalence of `X` and `Y` themselves.
  - Anti-isomorphisms need nothing extra: `Σ f_n u^n ↦ Σ u^(−n) f_n` is an anti-automorphism of `R_Y`, so
    `M_3(R_Y)^op ≅ M_3(R_Y)`.

## Firewalls to test for (a) in characteristic 2
- Zel'manov and Golubchik–Mikhalev 1981/83 assume `1/2`. Golubchik 1992 (`GL_n`, `n ≥ 4`, arbitrary rings) and
  Golubchik 1995 (projective groups) are being read.
- `E_3` versus `GL_3`: `K_1(R_X) ≅ Z` by the ABC fibration, so `E_3(R_X) ≠ GL_3(R_X)`, and theorems stated for
  `GL_n` do not apply verbatim.
- `R_X` has no minimal idempotents (Cantor set), so rank-one / residual-space methods do not start.
- Maximal elementary abelian 2-subgroups of `E_3(R_X)` are not all unipotent radicals `U_P`. Over towers of height
  `h`, `E_3` contains `GL_(3h)(F_2)`, where commuting square-zero pairs with `N_1 N_2 ≠ 0` exist, e.g.
  `N_1 = E_12 + E_34`, `N_2 = E_13 + E_24`.

## Deliverable for the note
- If (a) closes with a short proof or a verbatim import: a proposal stating "`G_X ≅ G_Y` implies `X` and `Y` are
  strongly orbit equivalent". "Continuum many" then follows from continuum many Sturmian dimension groups.
- Otherwise the chain (b)–(c) lands as an established reduction with an honest open (a), plus a firewall, and the note
  keeps its current corollary.
- Does not duplicate `sk-rigidity-intrinsic` (group-theoretic reconstruction of the clopen algebra) or
  `sk-word-problem`.

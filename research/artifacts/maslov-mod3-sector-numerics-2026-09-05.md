---
rg: 2
title: Universal-cover lifts of the root relators of Sp_4(Z) and a first numerical probe of the mod-three Maslov sector (2026-09-05)
kind: artifact
---

# Purpose

`maslov-mod3-projective-defect-gap` asks whether the two nontrivial mod-three
Maslov projective sectors of `Sp_4(Z)` have a dimension-free normalized-HS
relator defect gap, and its Attempts list says that direct nonlinear
optimization in increasing dimension "should be run first".  No explicit
presentation of `Sp_4(Z)` with the Maslov exponents of its relators was
recorded anywhere in the graph, which is why the run had not happened.  This
record supplies the exponents without any cocycle formula, records one exact
structural fact they reveal, and reports a first optimization run that turns
out to be uninformative for a reason worth recording.  Scripts and raw
numbers are in `experiments/maslov_sector/`.

# Setup

Generators: the eight root elements `x_alpha(1)` of `C_2`, as `4x4` integer
matrices for the symplectic form `J = [[0,I],[-I,0]]`: the long roots
`2e_1, 2e_2` (upper unipotent with `S = E_11, E_22`), the short roots
`e_1+e_2` (upper unipotent, `S = E_12+E_21`) and `e_1-e_2`
(`diag(A, A^{-T})`, `A = I + E_12`), and their transposes for the negative
roots.  Letters `0..7` are `x_alpha(1)`, letters `8..15` are `x_alpha(-1)`.
Every `x_alpha(t) = I + t N_alpha` with `N_alpha^2 = 0`, so each letter
carries a canonical one-parameter path in `Sp_4(R)`.

Lifts.  For a relator word `r = s_1 ... s_m` (a closed loop in the Cayley
graph) concatenate the one-parameter paths, take at each time the unitary
part `u(t) = g(t)(g(t)^T g(t))^{-1/2}`, which lies in
`Sp_4(R) cap O(4) = U(2)`, read `u(t)` as the complex `2x2` matrix
`P + iQ` for `u = [[P,Q],[-Q,P]]`, and integrate the phase of its
determinant.  Since `U(2)` is a deformation retract of `Sp_4(R)` and
`det` induces an isomorphism `pi_1(U(2)) = Z`, the winding number `k_r` is
the exponent of the central generator `zeta` in the lift
`r~ = zeta^{k_r}` to the universal-cover lattice `Sp~_4(Z)`.  Deligne's
triple cover is `E_3 = Sp~_4(Z)/<zeta^3>`, so the mod-three Maslov sector
imposes `rho(r) = omega^{k_r} I`, `omega = e^{2 pi i/3}`; the metaplectic
double cover `E_2 = Sp~_4(Z)/<zeta^2>` imposes `rho(r) = (-1)^{k_r} I`.
All winding numbers came out integral to `2e-15`.  Sanity: `w_alpha^4`
winds once for each long root and zero times for each short root, as it
must, since the short-root circles land in `SO(2) subset U(2)` where
`det` is trivial.

Relators.  Breadth-first search to radius `6` in the sixteen letters
(`1,148,696` elements) gives, from the non-tree edges, every closed loop of
length at most `13`; after free and cyclic reduction and identification up to
rotation and inversion there are `304,412` relators, all of even length
(`Sp_4(Z)` maps onto `Z/2` with every root generator going to the
generator), all verified to evaluate to the identity in `Sp_4(Z)`.  Radius
`5` already contains every closed loop of length at most `11`, and the
fundamental cycles of the BFS tree generate all loops inside the ball.

# The exact fact

Every one of the `34,294` relators of length at most `11` lifts with exponent
`0`.  Among the `270,118` relators of length `12` exactly `20` lift with
exponent `1` and the rest with exponent `0`.  The twenty are the length-12
words in the long-root pairs `(x_{2e_i}(1), x_{-2e_i}(1))`, `i = 1, 2`,
listed in `experiments/maslov_sector/lifted_relators.txt`; they are the
relators of the long-root `SL_2(Z)` whose lift to the braid group `B_3` is
the kernel generator `Delta^4`.  So, in the eight root generators, every
relation of `Sp_4(Z)` of length below twelve holds already in `Sp~_4(Z)`,
and the central class first appears at length twelve, entirely through the
two long-root copies of `SL_2(Z)`.  This is the exact content of
`sp4-root-relators-below-length-twelve-lift-to-universal-cover`.

An integer echelon form of the exponent-sum lattice of all `304,412`
relators with the lift column appended has central relation generator
`c_0 = 1`: some integer combination of relators has zero exponent sums and
lift `1`.  Hence `zeta` lies in the commutator subgroup of the group
presented by these relators, its abelianization is finite, and no sector
admits one-dimensional solutions.  This matches the true lattice and is a
first consistency check on the completeness of the relator set at the
abelianization level; completeness itself is not proved here.

# The optimization run and why it is uninformative

Objective: over eight unitaries in `U(d)`, the mean normalized-HS squared
defect over a sample of unlifted relators (`600` or `400`) plus the mean over
all twenty lifted relators with their sector phases.  Riemannian gradient
descent with polar retraction (gradient verified against finite differences
to six digits), staged in relator length `6, 8, 10, 12`, six basin hops,
several restarts, from three initializations: random unitaries, the trivial
representation perturbed by `exp(i eps H)`, and the permutation
representation of `Sp_4(Z)` on `(Z/2)^4` (`d = 16`) so perturbed.  Results
(best over restarts; `maxdef` is the largest single-relator normalized-HS
defect):

```text
sector   init     d   mean unlifted  mean lifted  maxdef unlifted  maxdef lifted
mod 3    trivial  4   0.08125        0.000825     0.923            0.035
mod 3    trivial  8   0.08125        0.000825     0.923            0.035
mod 3    trivial  16  0.09785        0.001255     0.857            0.048
mod 3    perm2    16  0.05887        0.000686     0.735            0.041
mod 3    random   8   1.75889        0.000413     1.509            0.028
mod 2    trivial  4   0.10509        0.001085     1.057            0.040
mod 2    trivial  8   0.10509        0.001085     1.057            0.040
mod 2    trivial  16  0.11068        0.001257     0.998            0.056
mod 2    perm2    16  0.18021        0.003893     0.890            0.072
```

Three things are visible.  First, from the trivial representation the
minimizer is the same at `d = 4` and `d = 8` to six digits: the descent
never leaves the commutative regime, and what it finds is an abelian
relaxation (scalar phases times the identity) that satisfies the twenty
lifted relators and most unlifted ones and sacrifices a fixed fraction of
unlifted relators at defect near one.  The pure abelian relaxation on a
larger sample confirms this (mean squared defect `0.016` with max `1.39`
for mod three, `0.026` with max `2.00` for mod two).  Second, random starts
end at energies near those of random unitaries.  Third, and decisively, the
metaplectic sector is a control with exact finite-dimensional solutions
(Deligne: `E_2` is residually finite, and the theta-constant representations
realize `zeta -> -1`), yet the optimizer's best mod-two energies are worse
than its best mod-three energies.  So this class of local search does not
see the Deligne obstruction at all; its numbers say nothing about the gap in
either direction and must not be read as evidence.

# What a decisive run needs

Either an explicit exact solution of the metaplectic sector as a seed
(the theta-constant representation of `Mp_4(Z)` on the sixteen characteristics
of level two), so that the same optimizer can be shown to find known zeros
before its mod-three failures mean anything, or a global method in small
dimension (`d = 2, 3`, where the search space is small enough for exhaustive
restarts) to obtain the true minimum of the largest relator defect as a
function of `d`.  The relator data and lifts computed here are reusable for
both; nothing about the winding-number lifts depends on the optimizer.

# Files

`experiments/maslov_sector/presentation.py` (BFS, relators, vectorized
winding lifts), `lift_lattice_check.py`, `optimize.py`, `launch.sh`,
`lifted_relators_and_abelian_floor.py`, `lifted_relators.txt`, and
`RESULTS.txt` with the raw numbers.  The `13 MB` relator file `pres6.json`
lives on MSI at `/projects/standard/hsiehph/sauer354/maslov_experiment/` and
is regenerated by `presentation.py 6 13` in about six minutes.

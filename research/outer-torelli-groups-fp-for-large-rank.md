---
rg: 2
id: outer-torelli-groups-fp-for-large-rank
kind: claim
title: "There is n_0 such that the Torelli group of Out(F_n) is finitely presented for every n >= n_0"
---

Let `T_n = ker(Out(F_n) -> GL_n(Z))`. The claim: there is `n_0` such that `T_n` is
finitely presented for every `n >= n_0`. It is the yes-answer for the Out family of
Zaremsky Problem 3.1 (`zaremsky-3-01-out-torelli-resolved`). By
`ia-n-fp-iff-outer-torelli-fp` it is equivalent to
`ia-automorphism-groups-fp-for-large-rank`.

Known facts that bound it (Bestvina–Bux–Margalit, arXiv:math/0603177, Main Theorem):

- `T_n` is finitely generated for every `n` (Magnus; BBM part (3));
- for `n >= 3`, `T_n` has a `(2n-4)`-dimensional Eilenberg–MacLane space, and
  `H_{2n-4}(T_n; Z)` is infinitely generated, so `T_n` is never of type
  `FP_{2n-4}`;
- `T_3` is not finitely presented (Krstić–McCool; BBM part (2) at `n = 3`).

So for `n >= 4` the obstruction BBM find sits in degree `>= 4`, and the degree-2
question is open.

## Attempts

- **Brown's criterion through van Kampen peak reduction.** Ershov
  (arXiv:2601.01377, Theorem 1.1) proves that the partial Torelli overgroups
  `IAC_{n,d}` and `IAR_{n,d}` are finitely presented for `n >= d + 115`, and for
  `d = 1` when `n >= 26`. These are the preimages in `Aut(F_n)` of the matrices
  whose first `d` columns (or rows) are those of the identity. `IA_n` is the case
  `d = n`, far outside that range. Ershov writes that the result for smaller `d`
  does not suffice on its own. Where it dies: the peak-reduction order needs room
  (`n - d` large) that `d = n` does not leave.
- **Degree 2 homology.** Finite presentability forces `H_2(T_n; Z)` to be finitely
  generated. Only module-finiteness is known for the Aut version (Day–Putman,
  Geom. Topol. 21 (2017): an explicit finite generating set for `H_2(IA_n)` as a
  `GL_n(Z)`-module). Ershov records that the surface techniques of Minahan–Putman
  are not known to apply to `IA_n`. Status: open; necessary, not sufficient.
- **Actions on outer space.** `T_n` acts freely on the spine of outer space, but
  with infinitely many orbits of cells, since `T_n` has infinite index in `Out(F_n)`.
  Brown's criterion needs finitely many orbits in degrees `<= 2`, so a presentation
  obtained this way is finite only modulo the conjugation action of `Out(F_n)`
  (an equivariant presentation in the sense of Kassabov–Putman). Where it dies:
  passing from an equivariant presentation to a finite one.

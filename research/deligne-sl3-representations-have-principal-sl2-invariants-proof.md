---
rg: 2
id: deligne-sl3-representations-have-principal-sl2-invariants-proof
kind: route
title: Average the cuspidal character over PSL_2(F_q): only the identity and the regular unipotents contribute
target: deligne-sl3-representations-have-principal-sl2-invariants
requires: []
artifacts:
  - research/artifacts/sl3z-invariant-vector-witnesses-2026-09-12.md
---

`dim pi^(Omega_q) = |Omega_q|^(-1) sum_(h in Omega_q) Tr pi(h)`, with
`|Omega_q| = q(q^2-1)/2` since `Sym^2` has kernel `{+-1}`.

* `h = 1`: `(q-1)(q^2-1)`.
* `h = Sym^2(u)`, `u != 1` unipotent: `q^2 - 1` elements, all regular unipotent
  in `GL_3` because the nilpotent part squares to a nonzero multiple of `2`.
  Green's unipotent formula for cuspidal characters,
  `chi(u_mu) = prod_(i=1)^(l(mu)-1)(1-q^i)`, gives `1` at the regular class.
  It reproduces the two values printed in MdlS Example 2.2 (`(q-1)(q^2-1)` at
  `1`, `1-q` at transvections).
* Every other `h` is `Sym^2(g)` with `g` semisimple, eigenvalues `a, a^(-1)`,
  `a != +-1`, so `h` has eigenvalues `(a^2, 1, a^(-2))`.  It is `SL_3(F_q)`-
  conjugate to a block `SL_2` element `g'` with `(g'-1)^2 != 0`: if
  `a^2 != -1`, a regular semisimple element with a torus centralizer of
  surjective determinant; if `a^2 = -1`, `diag(-1,-1,1) = -I_2` in the block.
  MdlS Example 2.2 gives trace `0`.

Sum `(q-1)(q^2-1) + (q^2-1) = q(q^2-1)`, divided by `q(q^2-1)/2`, equals `2`.
The degree `(q-1)(q^2-1)` forces `pi` to be the whole restriction of the
`GL_3` cuspidal, so its character is constant on `GL_3`-classes.

Norm step: `pi(x)` fixes the invariant vectors with eigenvalue `4`; the regular
representation of `SL_3(Z)` restricted to `PSL_2(Z) = Sym^2(SL_2(Z))` is a
multiple of its regular representation, where Kesten's criterion gives norm
`< 4`.

Census check: for `q = 3` the exact computation in artifact Section 5 finds that
every irreducible representation of `SL_3(F_3)` has a principal-`SL_2` fixed
vector, while the four degree-16 cuspidals miss the block.

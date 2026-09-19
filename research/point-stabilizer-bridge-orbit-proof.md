---
rg: 2
id: point-stabilizer-bridge-orbit-proof
kind: route
title: Use point-stabilizer invariance and the unique off-diagonal pair orbit
target: point-stabilizer-local-hard-share-compiles-bridge-orbit
requires:
  - thompson-site-pulses-localize-hard-exits
---

If `g,g'` both carry `x_0` to `x`, then `g'^(-1)g` lies in `V_(x_0)` and
fixes both `A_0` and `u_0` by `(PSB2)`.  Hence `(PSB1)` and `u_x` are
well-defined.  Conjugating the middle relation of `(PSB2)` by `g` gives the
first equation in `(PSB3)`.

The stabilizer `V_(x_0)` is transitive on `X\{x_0}`.  Given `y!=x`, first
choose `g` with `gx_0=x`; then choose `h in V_(x_0)` with `hy_0=g^(-1)y`.
Conjugate the last relation of `(PSB2)` by `gh`.  Since `h` fixes `u_0`, the
result is `[u_x,B_y]=1`.

For the quantitative statement, express the required `g,h` in the standard
prefix-table and stabilizer generators.  Replacing exact stabilizer
invariance by the defining commutator relators costs their word lengths, and
all other instances are literal conjugates of the three prototype relation
types.  Polynomial normal-form length therefore gives polynomial van Kampen
area.  The final exact-model assertion follows by choosing `u_0` on the fixed
base-site factor; permutation of tensor sites implements `V` and its point
stabilizer acts trivially on that factor.

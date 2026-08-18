---
rg: 2
id: openai-nine-leaf-leavitt-configuration-proof
kind: route
title: Conjugate the elementary roots, block the six leaves into pairs, and read off the orthogonal corners
target: openai-nine-leaf-leavitt-configuration
requires: [elementary-group-property-t-over-free-algebras, leavitt-cylinder-swaps-generate-thompson-in-el, leavitt-gl-equals-el-and-perfect-unit-group]
artifacts:
  - official/counterexample.tex
---

## Why sufficient

**Membership of the compressors and of the witness.**  The second
prerequisite gives `V <= EL_D(R)`, hence `u, v in G` and `J = V_(1000) <= G`;
and it gives `V_l <= Gamma` for every `l` extending an `alpha_i`, which is
what places `u J u^(-1) = V_(0001)` inside `Gamma` once the table for `u` is
read off.

**Compression.**  For `g in {u, v}`, conjugating an elementary `alpha`-root
gives `g(1 + s_(alpha_i) r t_(alpha_j))g^(-1) = 1 + s_(alpha_i 0) r
t_(alpha_j 0)` for `i /= j`, because both tables send `alpha_i` to
`alpha_i 0`.  The image lies in `Gamma` because
`s_(alpha_i 0) r t_(alpha_j 0) = s_(alpha_i)(s_0 r t_0)t_(alpha_j)`, an
`alpha`-root with coefficient `s_0 r t_0`.  The inclusion is strict as a set
of coefficients, which is what makes the compression one-sided.

**Generation.**  Partition the six `alpha`- and `beta`-leaves into blocks
`C_i = {alpha_i, beta_i}` and set `X_i = s_(alpha_i) t_0 + s_(beta_i) t_1`,
`Y_j = s_0 t_(alpha_j) + s_1 t_(beta_j)`.  The inverse table for `u` gives
`u^(-1)(1 + s_(alpha_i) r t_(alpha_j))u = 1 + X_i r Y_j` for `i /= j`.  Given
`B = (b_(pq)) in M_2(R)`, taking `r = sum_(p,q) s_p b_(pq) t_q` yields
`X_i r Y_j = sum_(p,q) s_(l_(i,p)) b_(pq) t_(l_(j,q))` with `l_(i,0) =
alpha_i`, `l_(i,1) = beta_i`; a one-entry matrix therefore produces every
elementary root joining different blocks.  The commutator identity
`[1 + s_a r t_c, 1 + s_c t_b] = 1 + s_a r t_b`, with `c` chosen in a third
block, supplies the roots inside a block.  Hence
`EL_((alpha,beta))(R) <= <Gamma, u>`, and the same argument with `v` and the
blocks `{alpha_i, nu_i}` gives `EL_((alpha,nu))(R) <= <Gamma, v>`.  A last
application of the commutator identity across an `alpha`-leaf joins a
`beta`-leaf to a `nu`-leaf, so `<Gamma, u, v>` contains every elementary
`D`-root.

**The direct product.**  `0` and `1000` are incomparable, so
`e_0 e_1000 = e_1000 e_0 = 0`.  Every `g in Gamma` has `g - 1 in e_0 R e_0`
and every `j in J` has `j - 1 in e_1000 R e_1000`, so
`(g-1)(j-1) = (j-1)(g-1) = 0`, which is commutation; and an element of both
has its difference from `1` in both orthogonal corners, hence equal to `0`.

**Property (T) and finite generation.**  `R` is generated as a ring by
`{1, s_0, s_1, t_0, t_1}`, and the Steinberg identities
`x_(ij)(r + r') = x_(ij)(r)x_(ij)(r')`, `[x_(ij)(r), x_(jk)(r')] =
x_(ik)(rr')` make those five coefficients generate `EL_q(R)` for `q >= 3`;
so `Gamma` and `G` are finitely generated.  Both are infinite because
`r -> 1 + s_(a_i) r t_(a_j)` embeds the additive group of `R`.  Property (T)
is the chapter's citation of Ershov--Jaikin-Zapirain for `EL_n` over a
finitely generated ring, `n >= 3`; the first prerequisite discharges it here
without that citation, since `R` is a finite-type `ZMod 2`-algebra and the
free-algebra theorem descends to `EL_3(R)`.  The third prerequisite carries it
to rank nine: the prefix-code self-similarity `R =~ M_3(R)` and the block
flattening `EL_3(M_3(R)) = EL_9(R)` identify `G` with a rank-three elementary
group over a finite-type algebra.

## The one thing this route does not do

It does not verify that the configuration is an instance of this repository's
Lean `CompressionSetup`.  The fields of that structure are packaged
differently -- the centralizing condition there is stated for the compressed
copy of `Gamma` -- and no such instantiation has been built.  What is asserted
here is that the chapter's own hypothesis list is satisfied.

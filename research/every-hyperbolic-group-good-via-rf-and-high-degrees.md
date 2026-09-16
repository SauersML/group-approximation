---
rg: 2
id: every-hyperbolic-group-good-via-rf-and-high-degrees
kind: route
title: Residual finiteness effaces degrees one and two, and high-degree mod-p effacement on torsion-free subgroups does the rest
target: every-hyperbolic-group-is-good
requires:
  - hyperbolic-finite-residual-is-torsion-free
  - universal-hyperbolic-vtf-iff-rf
  - torsion-free-hyperbolic-mod-p-classes-die-virtually
  - effaceable-cohomology-makes-inflation-an-isomorphism
artifacts:
  - research/artifacts/hyperbolic-goodness-rf-plus-high-degree-reduction-2026-09-16.md
---

The complete argument is Sections 2-4 of the artifact (Theorem 4, `2 => 1`). A class
is *effaceable* if it restricts to zero on some finite-index subgroup. `(E_n)` is the
hypothesis of `effaceable-cohomology-makes-inflation-an-isomorphism`.

**Inputs.**

- (a) By `hyperbolic-finite-residual-is-torsion-free` and
  `universal-hyperbolic-vtf-iff-rf` (items 2 => 1 and 2 => 3), every word-hyperbolic
  group is residually finite and virtually torsion-free.
- (b) `torsion-free-hyperbolic-mod-p-classes-die-virtually`.
- Standard facts. Finite-index subgroups, and extensions with finite kernel, of a
  hyperbolic group are hyperbolic (quasi-isometry invariance). `H^2(H;M)` classifies
  extensions of `H` by `M` inducing the given action. Restriction corresponds to
  pullback, and the zero class to a split extension (Brown IV.3).

**Lemma A (degree one, any group).** Let `x in H^1(H;M)` be represented by a crossed
homomorphism `f`. On `U = ker(H -> Aut M)`, `f` is a homomorphism to the finite group
`M`. Its kernel `W` has finite index and `res^H_W x = 0`.

**Lemma B (degree two).** Let `x in H^2(H;M)` classify `1 -> M -> E -π-> H -> 1` with `M`
finite. Suppose `E` is residually finite. Then some finite-index normal `E_0` meets `M`
trivially. `π` maps `E_0` isomorphically onto the finite-index subgroup `W = π(E_0)`.
Its inverse splits the pullback over `W`, so `res^H_W x = 0`.

**Lemma C (finite index).** Let `H <= G` have finite index. If every class in
`H^q(H;M)` is effaceable, then so is every class in `H^q(G;M)`: restrict first to `H`,
then efface inside `H`.

**Lemma D (coefficients).** Let `C` be a class of groups closed under finite-index
subgroups, and fix `q`. Suppose that for all `U in C` and all primes `p`, every class in
`H^q(U;F_p)` is effaceable. Then every class in `H^q(U;M)` is effaceable for all
`U in C` and all finite `U`-modules `M`.

*Proof of Lemma D.* By Lemma C, pass to the kernel of the action, so `M` is trivial.
Induct on `|M|`, simultaneously for all `U in C`. Choose `P <= M` of prime order `p`. The
image of `x` in `H^q(U;M/P)` dies on some `W_1`. By exactness, `res^U_{W_1} x = i_* y` for
some `y in H^q(W_1;F_p)`. Since `W_1 in C`, `y` dies on some `W_2 <= W_1`. Hence
`res^U_{W_2} x = 0`.

**Derivation.** Let `G` be word-hyperbolic. By (a) it has a torsion-free finite-index
subgroup `H`, which is hyperbolic. We check `(E_n)` for `H`, for every `n`.

- `q = 1`: Lemma A.
- `q = 2`: every extension of `H` by a finite module has finite kernel. So it is
  hyperbolic, hence residually finite by (a). Apply Lemma B.
- `q >= 3`: the torsion-free hyperbolic groups form a class closed under finite-index
  subgroups. Apply (b) and Lemma D.

By Lemma C, `G` satisfies `(E_n)` for every `n`. By
`effaceable-cohomology-makes-inflation-an-isomorphism`, inflation
`H^q(G_hat;M) -> H^q(G;M)` is then an isomorphism for every `q` and every finite `M`.
So `G` is good. `QED`

**Sharpness (prose only, no converse route).** Universal goodness implies (a): item 3
of `good-cocompact-proper-groups-are-virtually-torsion-free` gives universal virtual
torsion-freeness, and `universal-hyperbolic-vtf-iff-rf` converts it. Universal goodness
also implies (b), by `good-groups-have-no-persistent-finite-cohomology`. So this route
splits the target exactly into Gromov's question and a cohomological assertion about
degrees `3..cd` on torsion-free hyperbolic groups.

When `vcd G <= 2`, (b) is vacuous. Hence, under (a), every hyperbolic group of
virtual cohomological dimension at most two is good. This includes `GHB_2(7)`, whose
kernel `ker ψ` acts freely and cocompactly on the 2-dimensional complex of
`cckw-ghb2-kms-group-structure`. Unconditionally, `GHB_2(7)` is good and residually
finite iff every finite-module extension of `ker ψ` is residually finite (artifact,
Section 5).

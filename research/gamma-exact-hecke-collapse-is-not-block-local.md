---
rg: 2
id: gamma-exact-hecke-collapse-is-not-block-local
kind: claim
title: At Gamma-exact lifts Theorems C and 4.1 reduce (MUI-O) to finite block rigidity, and block rigidity is false, since an admissible 28-point block of SL_3(F_2[e]) splits a Hecke double coset
distinct_from:
  mui-pair-measures-orbital-reduction: that reduces (MUI-J) at Gamma-exact lifts to (MUI-O) for Hecke couplings; this rectifies s(t) itself to an exact Gamma-to-Lambda intertwiner, uses Theorem C to show Lambda-orbits fill Gamma-orbits, reduces (MUI-O) to a statement about single finite Gamma-sets with no sofic data left, and then refutes that statement (part (6)), so the block-local class of proofs is dead.
  kun-thom-nonsofic-wreath: Theorem 4.1 is used here as a constraint on which local configurations can carry mass; part (6) exhibits an admissible block that still splits a Hecke double coset, so Theorem 4.1 plus Theorem C, applied block by block, does not give (MUI-O).
  approximate-collapse-for-kt-compressor: this is a wave step on its (MUI-O) sub-question, not the (AC) wall itself.
artifacts:
  - research/gamma-exact-hecke-collapse-is-not-block-local-proof.md
  - research/artifacts/kun-thom-2608-06222-verified.md
  - research/artifacts/dual-number-antiflag-block-2026-09-18.g
---

**ESTABLISHED (proposed; full proof in
`gamma-exact-hecke-collapse-is-not-block-local-proof`).** Inputs:
property (T) of `Gamma` through a Kazhdan pair `(S, kappa)`, Kun--Thom
Theorem C and Theorem 4.1 verbatim
(`research/artifacts/kun-thom-2608-06222-verified.md`), and
`mui-pair-measures-orbital-reduction` (2'), (3). Everything else is finite
counting, plus one exact GAP computation for (6)
(`research/artifacts/dual-number-antiflag-block-2026-09-18.g`).

**Outcome in one line.** At a Gamma-exact lift, the sofic data reduce
(MUI-O) to one rigidity statement per finite block, (LHR-adm). That
statement is **false** (part (6)). So Theorems C and 4.1, applied block by
block, cannot prove (MUI-O). Whatever does must see how blocks sit inside
the global `G`-structure.

This is the (MUI-O) step on `approximate-collapse-for-kt-compressor`, after
`mui-pair-measures-orbital-reduction`.

## Setting

As in `mui-pair-measures-orbital-reduction`. `s_n : G -> Sym(Y_n)` is a
Gamma-exact lift of a sofic `sigma`, `u_n` is uniform on `Y_n`, `T` is a
finite subset of the compression semigroup with `G = <Gamma, T>`. For
`t in T`, `phi_t(gamma) = t gamma t^-1` and `Lambda_t = phi_t(Gamma)`.
Orbits are `s_n(Gamma)`-orbits unless said otherwise. For a Gamma-orbit
`O` in some finite Gamma-set, `unif(O)` is its uniform measure.

## Theorem

**(1) Rectification.** For each `t in T` there are a Gamma-invariant
`Y'_n subset Y_n` and an injection `tau_n : Y'_n -> Y_n` with

```text
tau_n(s_n(gamma) y) = s_n(phi_t(gamma)) tau_n(y)   for all gamma in Gamma, y in Y'_n,
u_n({y in Y'_n : tau_n(y) = s_n(t) y}) -> 1.
```

`Y''_n = tau_n(Y'_n)` is `s_n(Lambda_t)`-invariant. `tau_n` maps each
Gamma-orbit `A` of `Y'_n` bijectively onto one `Lambda_t`-orbit `tau A`,
and `A` is Gamma-isomorphic to `phi_t^*(tau A)`. For MUI `nu`,
`||psi_n(t)_* nu_n - (tau_n x tau_n)_* nu_n||_TV -> 0` (for any bijective
extension of `tau_n`). The constant is explicit: the mass where
`tau_n != s_n(t)` is at most `(4/kappa^2)` times the `S`-defect of the
relation `t gamma = phi_t(gamma) t`.

**(2) Theorem C kills the leak.** For a Gamma-orbit `C` of `Y_n`, let
`A_C` be the Gamma-orbit of `Y'_n` whose image `tau A_C` is the largest
`Lambda_t`-orbit in `C` (if any), and put
`leak(C) = |C| - |tau A_C|`. Then

```text
sum_C leak(C) = o(|Y_n|).
```

Equivalently: `u_n`-almost every point lies in a Gamma-orbit `C` that is
filled up to relative error `o(1)` by the single `Lambda_t`-orbit
`tau A_C`, and the Gamma-orbits `A` that are not of the form `A_C` carry
`o(1)` mass.

**(3) Theorem 4.1 makes the good blocks admissible.** Call a Gamma-orbit
`A` of `Y'_n` **`(delta, delta')`-good** if `A = A_C` for `C = f(A)` (the
Gamma-orbit containing `tau A`), `leak(C) <= delta |C|`, and every
Gamma-automorphism `alpha` of `A` has `tau alpha tau^-1` agreeing with the
restriction of some Gamma-automorphism of `C` on at least
`(1 - delta')|C|` points. For all `delta, delta' > 0`, the `u_n`-mass of
Gamma-orbits that are not `(delta, delta')`-good tends to `0`.

**(4) Reduction to block rigidity.** Consider the finite statement

> **(LHR-adm) for `(Gamma, Lambda_t)`.** For every `c > 0` there are
> `delta, delta' > 0` such that: for every finite Gamma-set `Z`, Gamma-orbits
> `C, D` of `Z`, and `Lambda_t`-orbits `a subset C`, `b subset D` with
> `|a| >= (1-delta)|C|`, `|b| >= (1-delta)|D|`, such that every
> `Lambda_t`-automorphism of `a` (resp. `b`) agrees with a
> Gamma-automorphism of `C` (resp. `D`) on at least `(1-delta')|C|` (resp.
> `(1-delta')|D|`) points, every
> `Lambda_t`-orbit `O subset a x b` satisfies `|O| >= (1-c) |Gamma O|`.

If (LHR-adm) holds for every `t in T`, then (MUI-O) holds at every
Gamma-exact lift, hence (MUI-J) and (MUI-C) hold there
(`mui-pair-measures-orbital-reduction` (2'), (3);
`mui-commutant-reduces-to-internal-joining-invariance` (1)). Only the
sofic data enters through (1)--(3). What remains is a statement about one
finite Gamma-set at a time.

**(5) The admissibility clause cannot be dropped (subfield model).**
Take the Theorem E pair with `r = 3`, `d >= 3` and the compressor
`t in SL_d(Z)` given by `x_2 -> x_1 x_2`, `x_i -> x_i` for `i != 2` (the
elementary matrix `I + E_12` on exponent vectors), so
`t R_+ = F_q[x_1, x_1 x_2, x_3, ..., x_d]`. For `k >= 1` put `Q = q^k`, pick
`beta` with `F_q(beta) = F_Q` and `alpha` with `F_q(alpha) = F_{Q^2}`, and
let `rho_k : R_+ -> F_{Q^2}` send `x_2 -> alpha`, `x_3 -> beta`, and every
other `x_i -> 0`. Then `rho_k(Gamma) = SL_3(F_{Q^2})` and
`rho_k(Lambda_t) = EL_3(rho_k(t R_+)) = SL_3(F_Q)`. Let
`Z_k = P^2(F_{Q^2})`, a single Gamma-orbit `C`, and let `a` be its set of
non-`F_Q`-rational points.

- Each `z in a` lies on exactly one `F_Q`-rational line (the line through
  `z` and its Frobenius conjugate `z^Q`), and `SL_3(F_Q)` is transitive on
  `a` (transitive on rational lines; the line stabilizer acts on the line
  through `PGL_2(F_Q)`, which is transitive on `P^1(F_{Q^2}) - P^1(F_Q)`).
  So `a` is one `Lambda_t`-orbit with
  `|a| = Q^4 - Q = (1 - (Q^2+Q+1)/(Q^4+Q^2+1)) |C|`.
- `Gamma` is 2-transitive on `Z_k`. The Frobenius graph
  `O = {(z, z^Q) : z in a}` is a single `Lambda_t`-orbit of size `Q^4 - Q`
  inside the off-diagonal Gamma-orbit of size `|Z_k|(|Z_k|-1)`, so
  `|O| / |Gamma O| = O(Q^-4)`.

So, as `k -> infinity`, the admissibility-free form of (LHR-adm) fails with
`delta = O(Q^-2) -> 0` at every `c < 1`. The failing orbit is the graph of
the Frobenius `F`, a Lambda_t-automorphism of `a` that agrees with no
Gamma-automorphism of `C` anywhere on `a` (a 2-transitive set of size at
least 3 has no nontrivial automorphism). Pulled back by `tau`, `F` is an
automorphism of the kind (3) forbids on positive mass. So no Gamma-exact
lift of `G` carries these configurations on non-negligible mass. Hence
Theorem 4.1 is **not** a consequence of Theorem C plus the local finite
structure of Gamma-sets, and a proof of (MUI-O) has to use the Theorem 4.1
constraint or global G-structure.

**(6) Block rigidity is false (decisive computation, `q = 2`).** Take
`q = 2`, `r = 3`, `d >= 3`, and the compressor `t` of (5). Let
`rho : R_+ -> F_2[e]/(e^2)` send `x_2 -> e` and every other `x_i -> 0`.
Then `rho(Gamma) = SL_3(F_2[e])`, of order `43008 = 2^8 * 168`, and
`rho(Lambda_t) = SL_3(F_2)`, the constant matrices. Let
`K = ker(SL_3(F_2[e]) -> SL_3(F_2))`, which is `sl_3(F_2)`, the Steinberg
module, of order `2^8`. There is a subgroup `H` with

```text
|H| = 1536,   H ∩ K of order 64 (codim 2),   H K / K = S_4 (a maximal subgroup of SL_3(F_2)),
H ∩ SL_3(F_2) = S_3 (order 6),
```

such that on the 28-point Gamma-set `C = SL_3(F_2[e]) / H`:

- `Gamma` acts faithfully and with rank 3, with pair orbits of sizes
  `28, 84, 672`;
- `Lambda_t = SL_3(F_2)` is **transitive** on `C`: `C` is the set of 28
  antiflags of the Fano plane, so `leak = 0`;
- `Lambda_t` has pair orbits of sizes `28, 84, 84, 84, 168, 168, 168`, so the
  size-672 Gamma-orbit splits into five Lambda_t-orbits, the smallest of
  relative size `84/672 = 1/8`;
- `Aut_Gamma(C) = Aut_Lambda(C) = 1` (both centralizers in `Sym(28)` are
  trivial), so the block is admissible for every `delta'`.

So `(C = D, a = b = C)` satisfies the hypotheses of (LHR-adm) with
`delta = delta' = 0` and violates its conclusion for every `c < 7/8`.
**(LHR-adm) is false for `(Gamma, Lambda_t)` at `q = 2`.** The computation
is exact (GAP, subgroup and complement enumeration, and orbit counts); the
script is `research/artifacts/dual-number-antiflag-block-2026-09-18.g`.

A wider scratch search over the other Lambda-transitive blocks of
`SL_3(F_2[e])` finds further admissible splitting blocks, of sizes 42, 56
and 84, with smallest ratio `1/16`. The 28-point block is the smallest.

## What is killed, and why the exact case survives

**Killed:** every proof of (MUI-O) at Gamma-exact lifts that uses the sofic
data only through (a) Theorem C on functions of `Y_n` and (b) Theorem 4.1
on permutations commuting with `s_n(Gamma)`, followed by per-block finite
analysis. Parts (1)--(3) extract exactly what (a) and (b) say about a
single block: leak zero, admissible. The antiflag block satisfies all of
it and still splits a double coset. Nothing in (1)--(3) excludes a
Gamma-exact lift in which a fixed fraction of `Y_n` consists of Gamma-orbits
`A ≅ phi_t^*(C)` (the antiflags, with `Gamma` acting through evaluation
at `0`) mapped by `s_n(t)` onto antiflag blocks `C`. On such a lift, the
orbital measure uniform on the Gamma-orbits of `A x A` of size 84 pushes
to a measure that is `1/8`-concentrated inside a Gamma-orbit of pairs.

**Why the exact case survives.** Such blocks never occur in a finite
`G`-set. There, Theorem C applied to the finite `G`-set `Y x Y` makes
Gamma-orbits of pairs `G`-invariant, so Lambda_t-orbits of pairs equal
Gamma-orbits of pairs. The antiflag block fails exactly this. What
excludes it in the finite case is Theorem C **for the pair space**. In the
sofic case that is the pair-level statement itself (the obstruction of
`mui-pair-measures-orbital-reduction`: pair orbits carry no uniform mass).
So the reduction (1)--(4) goes as far as the one-point theorems can take
it. The residue is genuinely about pairs.

## Status of the wave step

(MUI-O) is not decided, and the block-local class of proofs is dead. The
question is now a realizability problem:

> **(REAL)** Is there a sofic `sigma` of `G` with a Gamma-exact lift
> `s_n` in which a fixed fraction of `u_n`-mass lies in Gamma-orbits `A`
> that `s_n(t)` maps (off `o(1)`) onto the Lambda_t-orbit of an antiflag
> block of `SL_3(F_2[x_2]/(x_2^2))`?

A yes is expected to refute (MUI-O), hence (MUI-J) and (MUI-C), at that
`sigma`, by part (4)'s computation run backwards. The one unproved step is
that the orbital measures on the 84-element orbits occur inside an MUI
Hecke mixture. A no has to come from the global
`G`-structure. The obvious constraint is that `s_n(t^-1)` and the other
compressors must also map the antiflag blocks into blocks with zero leak.
Next step: build `s_n` from the antiflag data by the Hamming-local
constructions used for the planted lifts
(`planted-lifts-defeat-hilbert-level-gaussian-soficity`), or show that
every Gamma-exact sofic lift has Lambda_t-orbits of pairs filling the
Gamma-orbits of pairs on antiflag-type blocks.

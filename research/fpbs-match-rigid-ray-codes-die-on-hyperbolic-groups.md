---
rg: 2
id: fpbs-match-rigid-ray-codes-die-on-hyperbolic-groups
kind: claim
title: On any torsion-free hyperbolic group (in particular a cocompact Sp(n,1) lattice), every boundary class carried by the rays of a Borel ray code with pointwise match rigidity has totally dissipative diagonal, with no free or quasiconvex subgroup carrying the rays; so a symmetric odometer code transplanted to a lattice can give a BB certificate only if match rigidity fails
distinct_from:
  fpbs-rotation-support-rigidity-kills-type-iii-classes: its Theorem C transfers support rigidity to hyperbolic groups only for rays inside the limit set of a quasiconvex free subgroup with (M'). Such classes fail the quasiconvex-null filter from the start. This claim needs no carrying subgroup; its only input is match rigidity of the ray set.
  fpbs-zero-entropy-ray-codes-are-support-rigid: that works in F_2 with the stationary two-letter code and reads rigidity off the exponents (two-sided injectivity). This works in any torsion-free hyperbolic group with arbitrary Borel letters, including unboundedly long ones, and uses only the boundary-level statement "g zeta(x) = zeta(x') forces x' in x + Z".
  fpbs-odometer-killing-class-dies-by-support-rigidity: that proves match rigidity for the F_2 odometer code. This shows that match rigidity alone kills the class on every torsion-free hyperbolic group, so it is the only property a lattice transplant has to avoid or to prove.
---

**ESTABLISHED (written proof: `research/fpbs-match-rigid-ray-codes-die-on-hyperbolic-groups-proof.md`).** The
proof uses only the Gromov compactification of a hyperbolic group, the recurrence theorem for nonsingular actions and
Fubini. It needs no measure on the base and no quasiconvex subgroup.

**Why this matters for the flagship.** The Bevilacqua--Bowen (BB) route to fixed price one for a cocompact `Sp(n,1)`
lattice `Gamma` needs an amenable, ergodic, PDR imp action. Its boundary class must pass every filter. On `F_2`, the
odometer class of `fpbs-quasiconvex-null-small-classes-exist-on-free-boundary` passes the Dini, shadow and
quasiconvex-null filters. It dies by pointwise match rigidity
(`fpbs-odometer-killing-class-dies-by-support-rigidity`). The next step in that line was to transplant the code to
`Gamma` through a symmetric odometer code in Cannon's automaton. Such a code has to escape every quasiconvex limit set,
so it cannot live in a free subgroup, and the existing hyperbolic transfer (Theorem C of
`fpbs-rotation-support-rigidity-kills-type-iii-classes`) does not apply to it.

This claim settles the transfer half in general. On `Gamma`, match rigidity of the ray set is enough to kill every
class it carries. So the transplant question comes down to one property, and it cuts both ways:
- a transplanted code **with** match rigidity is dead on arrival;
- a lattice BB candidate built from a ray code must come from a code **without** match rigidity: one where some
  `g zeta(x) = zeta(x')` holds off the orbit relation, on a set of positive measure.

## Setting

Let `Gamma` be torsion-free, nonelementary and hyperbolic, with Gromov boundary `dGamma`. Let `(X_0, T)` be an
aperiodic Borel automorphism of a standard Borel space, and let `F : X_0 -> Gamma` be Borel (the **letters**). Put

`c_k(x) = (F(x+1) ... F(x+k))^{-1}` for `k >= 0`, and `c_k(x) = F(x+k+1) ... F(x)` for `k < 0`,

writing `x + t` for `T^t x`. Then `c_{k+l}(x) = c_l(x+k) c_k(x)`. Assume:
- **(R) rays.** For every `x ∈ X_0`, `c_k(x)^{-1}` converges in `Gamma ∪ dGamma` to a point `zeta(x) ∈ dGamma` as
  `k -> +∞`, and to a point `zeta^-(x) ∈ dGamma` as `k -> -∞`. Also `|c_k(x)| -> ∞` as `|k| -> ∞`.

  So `zeta(x) = F(x+1) F(x+2) ...` is the forward ray, and `zeta^-(x) = F(x)^{-1} F(x-1)^{-1} ...` the backward one.
  Then `zeta(x+k) = c_k(x) zeta(x)`. Uniformly quasi-geodesic concatenations satisfy (R).
- **(MR) match rigidity.** If `x, x' ∈ X_0`, `g ∈ Gamma` and `g zeta(x) = zeta(x')`, then `x' ∈ x + Z`.
- **(MR±) reversed matches.** There is a Borel relation `Rel ⊂ X_0^2` with countable sections such that
  `g rho = rho'`, with `rho ∈ {zeta(x), zeta^-(x)}` and `rho' ∈ {zeta(x'), zeta^-(x')}`, forces `(x, x') ∈ Rel`.

For a **symmetric** code, `F(-y) = F(y)^{-1}` on a group `X_0` with `T x = x + 1`. Then `zeta^-(x) = zeta(-x-1)`,
and (MR) on `X_0 ∩ (-X_0)` gives (MR±) with `Rel = {x' ∈ ±x + Z}`.

## Theorem

**Theorem 1 (match rigidity kills every class on the rays).** Assume (R), (MR) and (MR±). Let `(Z, mu_Z)` be an imp
`Gamma`-space with a measurable equivariant `xi : Z -> dGamma`. Suppose `xi_*(mu_Z|_E)` is nonatomic and carried by
`Gamma zeta(X_0)` for every `E` of finite measure. Then `Gamma` acts totally dissipatively on
`(Z x Z, mu_Z x mu_Z)`. In particular:
- no ergodic such `Z` is PDR;
- for a finite nonatomic measure `rho` on `X_0` with `zeta_* rho` nonatomic, the class
  `nu_rho = sum_g c_g g_* zeta_* rho` dies, together with its Maharam extension and every imp action over it,
  whatever its Krieger type;
- none of these is the boundary class of a BB certificate.

The core is a joint-return count. For a pair of rays off a Fubini-null set, and for every finite `H ⊂ Gamma`, only
finitely many `g` satisfy `g eta, g eta' ∈ H zeta(X_0)`. The mechanism has three steps:
- (MR) and trivial stabilizers turn each return into `g = h c_k(x) h_0^{-1}`;
- infinitely many returns force `c_k(x) = u c_{k'}(x') v` for infinitely many `(k, k')`;
- passing to the boundary, this gives `rho = v^{-1} rho'`, so `(x, x') ∈ Rel ∪ (orbit relation)`, a relation with
  countable sections.

No length count, no bounded cancellation and no carrying subgroup is needed. This is the step where the `F_2` proofs
used the free-group normal form.

## Calibration

- **`F_2` odometer.** `(X_0, T)` is the conull set of `fpbs-odometer-killing-class-dies-by-support-rigidity`
  intersected with its negative, and `F` is the symmetric odometer labelling. Its Corollary 5.1 is (MR). Symmetry gives
  (MR±), and reducedness gives (R). Theorem 1 then reproduces its Corollary 2 directly, without the `Z/2` embedding.
- **Rotation and zero-entropy codes in `F_2`** work the same way. On `X_0 x Z/2`, two-sided injectivity gives (MR)
  and (MR±) by the tail argument in the proof of Corollary 5.1 of the odometer node.
- **Where it must fail.** Take a closed surface group with the Lebesgue class on `S^1`. Its diagonal is conservative
  (Hopf--Tsuji--Sullivan). So, by Theorem 1, no Borel ray code with (R), (MR) and (MR±) carries Lebesgue measure: the
  rays of any Borel code that carries it have off-orbit matches. This is consistent, because the theorem only removes
  match-rigid ray sets.
- **Positive entropy.** For the Bernoulli sign code in `F_2`, every pair of alternating rays has many matches, so (MR)
  fails. The theorem is silent there, as the zero-entropy node predicts.

## What this leaves (named open statement)

**Symmetric odometer code in a lattice with (MR).** Let `Gamma` be a torsion-free cocompact `Sp(n,1)` lattice. Is there
a symmetric odometer code with (R) and (MR) whose class is quasiconvex-null? If yes, it is killed by Theorem 1, and the
odometer line cannot produce a certificate. If every quasiconvex-null odometer code on `Gamma` violates (MR), the
violation is the new object to study: a positive-measure family of off-orbit matches `g zeta(x) = zeta(x')`.

The natural construction takes a malnormal quasiconvex free `F = <a, b>` (Kapovich) as the paperfolding skeleton. It
inserts killing elements `s_j` at the odometer windows, each shortest in its double coset `F s_j F`, so the
junction Gromov products are bounded. The rays are then uniform quasi-geodesics and quasiconvex-null, by the growth
gap of Dahmani--Futer--Wise. The obstacle to (MR) is precise. A long killing element `s_j` contains, with probability
tending to 1, subsegments of any fixed length that fellow-travel a coset of `F`. There an `F`-stretch of one ray can
match a piece of `s_j` in another ray, and the coset-by-coset alignment that would give (MR) breaks. What is needed
is **`F`-transverse killing elements**: for fixed `D`, elements escaping `N_R(g H_i)` for `i <= j` with no subsegment
of length `D` near any coset of `F`.

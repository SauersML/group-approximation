# Siegel spectral rigidity in Deligne sectors, and the approaches it kills

Lane swarm-0917-w2-mf-pull-3 (transplanter, entropy-measure), 2026-09-17.
Target node: `deligne-triple-cover-is-not-mf`.

- New claim: `deligne-sector-siegel-spectrum-is-full-torus`.
- Proof: `deligne-sector-siegel-spectrum-full-torus-proof`.

## 1. What was transplanted

The established SL_d(Z) pair is:

- `sln-z-unipotent-spectrum-finite-or-full-torus`: the column unipotent spectrum is finite (then the representation is congruence) or all of `T^(d-1)`;
- `sl4z-block-sl2-norm-four-unless-unipotent-spectrum-is-full`: in the finite branch, Magee--de la Salle applies.

Together they reduce the SL_4(Z) corona crux to the full-spectrum branch.

**Transplant.** The Deligne sector `A_omega = C*(E_3)/(z - omega)` carries the Siegel radical `U = Sym_2(Z)`.

- `U` lies in the Siegel parabolic. The mod-three multiplier is a circle coboundary there, so `U` acts through an honest representation `V`.
- The Levi `GL_2(Z)` acts on the dual torus through `Sym^2`. This action is not a standard `SL_(d-1)` action, and there are no elementary transvections to sweep with.
- The dual of the unipotent Levi elements acts by quadratic shears `T_k(x,y,z) = (x, y+2kx, z+ky+k^2 x)`.
- The swap `S` exchanges `x` and `z`.

## 2. The three steps

**Step A: irrational points.** Weyl's polynomial equidistribution sweeps `{x} x T^2`. Then `S` together with a density argument gives all of `T^3`.

**Step B: unbounded torsion.** This is the new difficulty.

- The shears are quadratic, so the multiples trick of the SL_d proof fails. For example, points with all coordinates of order `q^2`, or with `y` of order `q`, cannot be swept linearly.
- The van der Corput identity with `K = q^2` terms bounds every Fourier coefficient of the orbit average by `O(|n| q^(-1/2))` or `O(q^(-1))`.
- So orbit averages of points whose first coordinate has order `q -> infinity` converge to `delta_(x_inf) (x) Haar`.

**Step C: the finite branch.**

- Finite torsion spectrum makes `V(n(N Sym_2(Z)))` trivial, so `sigma` is scalar on its lifts.
- Commutators with a Levi element then die exactly, and they are noncentral.
- Margulis NST makes the kernel of finite index, so `z^2` lies in it by the Deligne finite residual. That contradicts `omega^2 != 1`.

**Conclusions.**

- (S1) `Y = T^3` for every unital *-representation of `A_omega`.
- (S2) Every lift of a nonzero Siegel-radical element, hence every long root element, has spectrum `T`.
- (S3) Every trace induces Haar measure on `Y`. This uses `deligne-maslov-sector-traces-are-central-regular`.

## 3. The obstruction, stated as a class kill

**Invariant.** The pair (Siegel joint spectrum `Y`, trace-induced spectral measure on `Y`) of a representation of `A_omega`. By Weyl conjugacy the same holds for the spectrum of any single long-root lift.

**Class.** Any argument that separates representations of `A_omega` from each other by this invariant. This covers:

- `lambda_omega` versus a corona model `A_omega -> prod M_n / sum M_n` coming from a putative MF approximation of `E_3`;
- an ultraproduct tracial model versus the central-regular trace;
- a corona representation versus a Hilbert space representation.

Typical members are:

1. the Magee--de la Salle congruence route: non-full unipotent spectrum gives a congruence quotient, then finite-group spectral input;
2. torsion or quasi-unipotent eigenvalue bounds on matrix models of long root elements. This is the norm version of D5 in `deligne-bounded-rank-rung-anatomy-2026-09-17`;
3. invariant-measure rigidity on the dual torus used to force atomic or algebraic measures (Benoist--Quint and solenoid-rigidity style), where the contradiction is meant to come from a non-Haar measure;
4. entropy or equidistribution comparisons of spectral measures of long-root lifts under tracial states.

**Where every member dies.** At the step "the model under consideration has non-full, atomic, torsion, or non-Haar Siegel data".

- By (S1) and (S3) that step is false for every representation and every trace of `A_omega`: exact, corona, ultraproduct, regular.
- The invariant takes one value on the whole sector, so it cannot separate anything.
- A norm MF model of `E_3` necessarily has long-root matrices whose spectra are asymptotically dense in `T`. Its tracial spectral measures converge to Haar on every Siegel radical (the latter along the trace, since traces on the sector are central-regular).

**Consequence for the SL_4 transplant.** The Deligne-sector analogue of `sl4z-block-sl2-norm-four-unless-unipotent-spectrum-is-full` is vacuous. The whole analogue of `sl4z-corona-representations-have-block-sl2-norm-four` lives in the full-spectrum branch, where Magee--de la Salle supplies nothing. There is no reduction to harvest.

## 4. Boundary: what is NOT killed

**Vector-level atoms survive.** The Z/3 extension splits over `P_S(Z)`. The induced representation `Ind_(s(NU) x <z>)^(E_3) (1 x omega)` has the nonzero `s(NU)`-invariant vector `delta_e`, so vector-state spectral measures can have atoms at torsion points.

Therefore these are not refuted by (S1)–(S3):

- invariant-vector mechanisms, such as relative property (T) for `Sym^2(Z) x| SL_2(Z)` or Kazhdan corner projections;
- multiplicity counts of atoms;
- non-tracial states.

A surviving separation must use vector or state data, or the matrix origin of the model, not the spectrum or the trace.

**Rank and trace overlap counting dies in addition.** Every trace kills the spectral projection of any Haar-null set, in particular of any torsion atom. So no "`tau(p) >= c`" count can come from Siegel atoms.

## 5. Model tests

- `lambda_omega`: `V|_U` is a multiple of the regular representation of `Z^3`. `Y = T^3` with Haar measure, which is consistent.
- The untwisted fibre (`omega = 1`): the trivial representation has `Y = {0}`. This is Lemma C's branch, nonempty because `z` is not forced to act nontrivially. The hypothesis `omega != 1` is used exactly once, in the last line of Lemma C.
- Induced representation above: `Y = T^3` as a set with atoms in its vector measures, which is consistent with Section 4.

## 6. Status

- The claim is proposed ESTABLISHED (unreviewed). Its route requires four ESTABLISHED nodes, and it uses two textbook facts proved inline or classical: the van der Corput identity and Weyl polynomial equidistribution.
- `deligne-triple-cover-is-not-mf` stays OPEN. The contribution is a precise obstruction, not a separation.

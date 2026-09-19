---
rg: 2
id: fpbs-finite-measure-ray-codes-die-on-rank-one-lattices
kind: claim
title: On a cocompact lattice in a rank-one simple Lie group (in particular Sp(n,1)), every Gamma-invariant Radon current on the space of boundary pairs splits by geodesic-flow entropy into a zero-entropy part carried by the graph of an equivariant a.e. bijection and a positive-entropy part whose forward class has positive dimension, so tail collapse with separated pasts never occurs at zero entropy and every uniformly quasi-geodesic ray code with a finite invariant measure dies
distinct_from:
  fpbs-zero-entropy-accumulation-needs-tail-collapse: that reduces zero-entropy essential accumulation to tail collapse with separated pasts, and leaves open whether such codes exist. This proves they do not exist (Theorem 1), by a geodesic-flow argument that sees the current and not the S-words, and it closes the positive-entropy side too (Theorem 2).
  fpbs-ray-code-deaths-depend-only-on-the-current: that shows a surviving code needs an essentially accumulating current and a Dini-singular class (its Corollary 5). This shows the two conditions are incompatible: accumulation forces positive flow entropy, and positive flow entropy forces positive dimension.
  fpbs-dini-boundary-class-diagonal-dissipative: that kills classes of positive dimension. This uses it as the positive-entropy half and adds the zero-entropy half, which that filter cannot see (every zero-entropy code class has dimension zero, `fpbs-backward-locally-finite-ray-codes-die` Proposition 4).
---

**ESTABLISHED (written proof: `research/fpbs-finite-measure-ray-codes-die-on-rank-one-lattices-proof.md`).** The
proof uses a thin-boundary partition (Mane's device) with a Borel--Cantelli estimate, Poincare recurrence, the
Ledrappier--Young dimension formula for unstable conditionals of a C^2 diffeomorphism, Theorem C and Theorem B of
`fpbs-dini-boundary-class-diagonal-dissipative`, and Theorem 1 of `fpbs-ray-code-deaths-depend-only-on-the-current`.

**Why this matters for the flagship.** For a cocompact `Sp(n,1)` lattice (property (T), fixed price open), the
Bevilacqua--Bowen (BB) route needs an amenable ergodic PDR imp action whose boundary class passes the Dini, shadow
and quasiconvex-null filters. The ray-code line (w8--w16) built candidate classes from uniformly quasi-geodesic
(UQ) ray codes, and it ended with one named statement: a zero-entropy code with **tail collapse with separated
pasts**, for example cell flips driven by an odometer that also drive the past. This node proves that no such code
exists, on any cocompact rank-one lattice, and closes the whole finite-invariant-measure branch of the line.

**The object changes.** The earlier steps worked with S-words, tails and spellings. Here the only object is the
`Gamma`-invariant Radon current `mu` on `d^2 Gamma = dGamma^2 \ Delta`, read as a finite invariant measure `m_mu` of
the geodesic flow of the compact locally symmetric orbifold. The invariant that decides is the **entropy of the
geodesic flow for `m_mu`**, not the entropy of the code. Zero flow entropy forces the stable leafwise measures of
`m_mu` to be Dirac. Positive flow entropy forces the unstable ones to have positive dimension.

## Setting

`G` is a connected simple Lie group of real rank one (`SO(n,1)`, `SU(n,1)`, `Sp(n,1)`, `F_4^{(-20)}`), `X = G/K`
its symmetric space, and `Gamma < G` a cocompact lattice. So `dGamma = dX` and `d^2 Gamma = d^2 X`. `T^1 X` is the
unit tangent bundle, `phi_t` the geodesic flow, and `(theta, eta, t)` Hopf coordinates (backward endpoint, forward
endpoint, Busemann height `beta_eta(o, .)`).

- A **current** is a `Gamma`-invariant Radon measure `mu` on `d^2 X`. Its **flow measure** `m_mu` is the image of
  `mu x dt` on `Gamma \ T^1 X`. Since `Gamma \ T^1 X` is compact, `m_mu` is finite for every current.
- `h(mu)` is the entropy of `phi_1` for `m_mu` (normalized), computed on `Gamma' \ T^1 X` for a torsion-free finite-
  index `Gamma' < Gamma` (Selberg). It does not depend on `Gamma'`.
- Disintegrate `mu` over the forward endpoint, `mu = ∫ mu^eta d nu_1(eta)`, and over the backward endpoint,
  `mu = ∫ mu_theta d nu^-_1(theta)`. The **forward class** `nu[mu]` is the class of `nu_1`.
- The flow space splits into invariant Borel sets `F_0`, `F_+` where the ergodic components of `m_mu` have zero or
  positive entropy. `mu = mu_0 + mu_+` is the matching splitting of the current.

For a (UQ) ray code with a finite invariant measure `rho^#` (setting of `fpbs-ray-code-deaths-depend-only-on-the-
current`), `mu_R` is its current and `nu = nu[mu_R]` its forward code class.

## Results

**Theorem 1 (zero flow entropy: the current is a graph).** If `h(mu) = 0`, then for `nu_1`-a.e. `eta` the measure
`mu^eta` is a single atom, and for `nu^-_1`-a.e. `theta` the measure `mu_theta` is a single atom. So `mu` is carried by
the graph of a `Gamma`-equivariant Borel map `f : dX -> dX`, defined and injective off a `nu`-null set, with
`f_* nu = nu^-`. In general this holds for `mu_0`.

**Theorem 2 (positive flow entropy: positive dimension).** If every ergodic component of `m_mu` has positive entropy,
then every set `E ⊂ dX` with `nu[mu](E) > 0` has positive Hausdorff dimension for a visual metric, and every measure
`C` with `C << nu[mu]` has positive lower local dimension on a set of positive `C`-measure. More precisely an ergodic
component of entropy `h` has unstable conditionals of dimension at least `h / chi_max` for the Riemannian leaf metric,
where `chi_max` is the top Lyapunov exponent (`2` for `SU`, `Sp`, `F_4` with curvature pinched in `[-4, -1]`, and `1`
for `SO(n,1)`).

**Theorem 3 (every finite-measure ray code dies).** Let `Gamma` be a cocompact lattice in a rank-one simple Lie
group, for instance in `Sp(n,1)`, and take any (UQ) ray code on `Gamma` with a finite invariant measure `rho^#`, of
any entropy and spelling multiplicity. Let `(Z, mu_Z)` be an ergodic imp `Gamma`-space with a measurable equivariant
`xi : Z -> dGamma` whose class `C = [xi_* mu_Z]` is nonatomic and satisfies `C << nu`. Then `Gamma` acts totally
dissipatively on the crossing part of `(Z x Z, mu_Z x mu_Z)`, and `Z` is not PDR. So no ray code with a finite
invariant measure carries the boundary class of a BB certificate.

**Corollary 4 (the named mechanism is impossible).** A code with `h(rho^#) = 0` has `h(mu_R) = 0` (the flow measure
is a time-changed factor of the suspension of `rho^#`). By Theorem 1 its current satisfies (LF_mu) with **one** atom
per endpoint. So tail collapse with separated pasts (Theorem 3 of `fpbs-zero-entropy-accumulation-needs-tail-
collapse`) never occurs, and zero-entropy essential accumulation is impossible. In particular every odometer-driven
cell-flip code, on a surface group or on an `Sp(n,1)` lattice, dies at the step "pasts separate": whatever the flip
pattern, a.e. forward endpoint has a single past endpoint.

**Corollary 5 (product classes carry no invariant current).** Let `C` be an ergodic nonatomic quasi-invariant class
on `dGamma` for a cocompact rank-one lattice. If some current `mu` is equivalent to `(C x C)` on `d^2 Gamma`, then
`h(mu_0) = 0` forces `mu_0 = 0`, because a graph is `C x C`-null. So all components have positive entropy, `C` has
positive dimension and is dominated by a Dini measure (Theorem C of the Dini node), and every imp action over `C` has
a dissipative crossing diagonal. So a BB boundary class `C` must have a product class `C x C` that carries **no**
equivalent `Gamma`-invariant Radon measure.

## Calibration

- **Periodic-orbit currents** (the `Gamma`-orbit of the axis of one loxodromic): zero entropy, one past per future.
  Theorem 1 agrees.
- **Liouville and Bowen--Margulis currents**: positive entropy, forward class Lebesgue or Patterson--Sullivan,
  positive dimension. Theorem 2 agrees, and they die by the Dini filter, as `fpbs-ray-code-deaths-depend-only-on-
  the-current` Theorem 3 found for the Markov code.
- **Lattice odometer codes and Toeplitz respellings** (`fpbs-backward-locally-finite-ray-codes-die`): zero entropy,
  code relation (LF). Theorem 1 gives the sharper one-atom form.
- **Surface and free groups.** A surface group is a cocompact lattice in `PSL_2(R)`, so the theorem applies. A free
  group is convex cocompact in `PSL_2(R)`, and the proof runs on its compact non-wandering set. Their cost is `> 1`,
  so nothing may survive, and nothing does.
- **The proof cannot kill too much.** It uses no property (T) and no rank-one rigidity beyond hyperbolic dynamics.
  It says nothing about quasi-invariant classes that carry no invariant current, which is exactly where Corollary 5
  leaves a BB certificate room.

## What this leaves (named open statement)

**Radon-free crossing classes.** On a cocompact `Sp(n,1)` lattice, is there an ergodic nonatomic `Gamma`-quasi-
invariant class `C` on `dGamma`, singular to every Dini measure, such that the crossing diagonal of some imp action
over `C` is conservative, while `C x C` carries no equivalent `Gamma`-invariant Radon measure (so the geodesic flow
has no finite invariant measure in the class)? Ray codes can only reach such a `C` through codes with no finite
invariant measure (nonsingular type III position spaces). The first test: whether a conservative crossing diagonal
over `C` forces a `sigma`-finite invariant measure on `d^2 Gamma` in the class of `C x C`, and whether such a measure
must be Radon on the flow space.

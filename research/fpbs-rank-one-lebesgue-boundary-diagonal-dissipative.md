---
rg: 2
id: fpbs-rank-one-lebesgue-boundary-diagonal-dissipative
kind: claim
title: For a discrete subgroup of a real rank-one simple Lie group, an imp action with a boundary map of Lebesgue-absolutely-continuous class has totally dissipative diagonal, so a Bevilacqua--Bowen certificate for a cocompact Sp(n,1) lattice needs a boundary class singular to Lebesgue
distinct_from:
  fpbs-rank-one-homogeneous-bb-certificates-fail: that kills the homogeneous spaces G/H (and actions factoring onto them) through a classification of unimodular amenable subgroups; this kills every imp action whose boundary measure class is absolutely continuous, homogeneous or not, including restrictions of arbitrary amenable G-spaces, by a measure-scaling height in the fibre of the induced G-space.
  fpbs-hyperbolic-bb-criterion-obstruction: that works coarsely in the Cayley graph and leaves the deep spreading case open for every measure class; this closes that case for all absolutely continuous boundary classes of rank-one lattices, with no ergodicity, amenability or (P)-type hypothesis on a Radon--Nikodym cocycle.
---

**ESTABLISHED (written proof; see `research/fpbs-rank-one-lebesgue-boundary-diagonal-dissipative-proof.md`).**

**Why this matters for the flagship.** For a cocompact lattice of `Sp(n,1)` (Kazhdan, cost one by Hutchcroft--Pete,
fixed price open) the only criterion that proves fixed price one without commensurated amenable structure is
Bevilacqua--Bowen (arXiv:2510.05459, Theorem 8.1): an amenable, partially doubly recurrent (PDR) imp action with
infinite non-atomic components. `fpbs-rank-one-homogeneous-bb-certificates-fail` removed homogeneous certificates,
and `fpbs-hyperbolic-bb-criterion-obstruction` showed a certificate must be "deep and spreading". This claim removes a
much larger family at once, and says which measure-theoretic feature any surviving certificate must have.

**Setting.** `G` is a connected simple Lie group of real rank one with finite centre, `X = G/K` its symmetric space,
`dX = G/P` its boundary, `Leb` the `K`-invariant (visual) measure class on `dX`. `Gamma <= G` is a discrete subgroup,
`(Z, mu)` a standard sigma-finite measure space with a measure-preserving `Gamma`-action, and `xi : Z -> dX` a
measurable `Gamma`-equivariant map.

**Theorem.** If `xi_* mu` is absolutely continuous with respect to `Leb`, then there is a measurable, exactly
`Gamma`-equivariant map `f : Z x Z -> X`, defined on a conull invariant set. Hence the diagonal action
`Gamma ↷ (Z x Z, mu x mu)` is **totally dissipative**.

Neither amenability, ergodicity nor finiteness of anything is assumed. The same proof gives a `G`-equivariant map
`W x W -> X` for every imp `G`-space `W` with a `G`-map to `dX`.

**The new mechanism (where the proof lives).**
1. **Induce and smooth.** `Zhat = G x_Gamma Z` is an imp `G`-space with a `G`-map to `dX`. Its boundary class is
   `G`-quasi-invariant, hence Lebesgue. So on the big Bruhat cell `Zhat = N^- x Y`, with `Y` the fibre over the base
   point, and the invariant measure is `Haar(N^-) x nu`.
2. **The fibre measure scales.** `A` conjugates `N^-` with nontrivial Jacobian, so `nu(a_s E) = e^{-cs} nu(E)` with
   `c > 0`. A measure-scaling flow has finite one-sided occupation times. That gives a measurable **height**
   `h : Y -> R` with `h(a_s y) = h(y) + s`, made `M`-invariant by a median over `M`. It is not `N`-invariant, so it is
   not a horosphere, and it is not excluded by the earlier theorems.
3. **Midpoint on the line.** For `(zhat, zhat')` over distinct boundary points, move the pair to the standard line and
   take the point at the mean of the two heights (the second read through the Weyl element, which inverts `A`). This
   point is independent of the `MA`-ambiguity and is `G`-equivariant.
4. **Descend without loss.** `z ↦ [e,z]` is exactly `Gamma`-equivariant. The one measure-theoretic issue is that the
   fibre points reached from `Z` form a `nu`-null slice. It is resolved because the height's domain can be taken
   `MA`-invariant and its complement is null along `Haar(N)`-almost every `N`-orbit, while absolute continuity of
   `xi_* mu` makes the needed `N`-coordinate `Haar(N)`-distributed. **This is the only place absolute continuity is
   used.**
5. `Gamma` acts properly on `X`, so the finite equivariant sets `{gamma : d(gamma o, f(z,z')) <= d(f(z,z'), Gamma o)+1}`
   feed Lemma 0 of `fpbs-hyperbolic-bb-criterion-obstruction-proof`.

**Corollaries (classes killed).** For every lattice `Gamma` in `SO(n,1)`, `SU(n,1)`, `Sp(n,1)`, `F_4^(-20)`:
- **Restrictions of `G`-spaces.** For every amenable imp `G`-space `W` with its boundary map, `W|_Gamma` and every
  finite-measure extension of it are not PDR. This contains all of Mellick's homogeneous `G/H` (already known here) and
  every non-homogeneous `G x_P Y` built from an arbitrary nonsingular `P`-space `Y`.
- **Absolutely continuous Maharam extensions.** The Maharam extension `dX x R` of any quasi-invariant class
  `<< Leb` (any Radon--Nikodym cocycle, not only those with property (P)) is not PDR.
- **Reduction for certificates.** Let `Gamma` be a cocompact `Sp(n,1)` (or `F_4^(-20)`) lattice. If an amenable PDR imp
  action exists, then on an invariant set of positive measure the Zimmer boundary map is a Dirac mass `delta_{xi(z)}`
  (item 4 of `fpbs-hyperbolic-bb-criterion-obstruction`), and `xi_* mu` is **singular** to Lebesgue measure. On an
  ergodic component the class is either equivalent to `Leb` (killed here) or singular. Thus every
  Bevilacqua--Bowen certificate for such a lattice lives over a `Gamma`-quasi-invariant singular measure class on the
  sphere, such as a harmonic or Patterson--Sullivan class of a non-Riemannian metric.

**Calibration.**
- **Higher rank must fail, and does.** In `SL(3,R)` the stabilizer of a pair of opposite chambers is `MA` with
  `dim A = 2`. The modular character kills a one-parameter subgroup of `A`, so the height only fixes a codimension-one
  slice of a flat, and no proper map arises. Mellick's certificate `SL(3,R)/A` survives, as it must.
- **Trees and surface groups.** Free and surface groups have cost > 1, so killing certificates for them is harmless.
- **Horospherical check.** For `W = G/MN` the height is the horosphere coordinate and the map is the midpoint of
  Theorem B of `fpbs-rank-one-homogeneous-bb-certificates-fail`, recovered as a special case.
- **Singular classes are genuinely outside the proof.** Step 4 needs the `N`-coordinates of partner points to be
  `Haar(N)`-distributed; for a singular `xi_* mu` they concentrate on a Haar-null set, where the height may be undefined.

**Next step (named).** For a cocompact `Sp(n,1)` lattice, decide whether some imp action with a boundary map of
singular class is PDR. The test objects are Maharam extensions of singular quasi-invariant classes whose cocycle
fails property (P) of `fpbs-hyperbolic-bb-criterion-obstruction-proof`, Step 7.

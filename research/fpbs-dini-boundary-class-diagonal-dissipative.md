---
rg: 2
id: fpbs-dini-boundary-class-diagonal-dissipative
kind: claim
title: For a nonelementary hyperbolic group, an imp action whose boundary class is dominated by a measure with Dini modulus of continuity (every Patterson--Sullivan, harmonic or positive-dimensional class) has dissipative crossing diagonal, so a Bevilacqua--Bowen certificate needs a boundary class singular to every Dini measure
distinct_from:
  fpbs-hyperbolic-bb-criterion-obstruction: that kills Maharam extensions only when the Radon--Nikodym cocycle is coarsely monotone along geodesics (property (P), Step 7), a geometric condition on the cocycle; this uses no property of the cocycle at all, only the size of the boundary class (a shadow-product sum), and applies to every imp action with a boundary map, Maharam or not.
  fpbs-rank-one-lebesgue-boundary-diagonal-dissipative: that treats Lebesgue-absolutely-continuous classes for discrete subgroups of rank-one Lie groups, by a scaling height in the induced G-space, and stops at singular classes; this treats singular classes (Patterson--Sullivan, harmonic, Gibbs, any positive-dimensional class) for every hyperbolic group, by a Borel--Cantelli count of diagonal returns.
---

**ESTABLISHED (written proof; see `research/fpbs-dini-boundary-class-diagonal-dissipative-proof.md`).**

**Why this matters for the flagship.** For a cocompact `Sp(n,1)` lattice, the Bevilacqua--Bowen criterion
(arXiv:2510.05459, Theorem 8.1) is the only known route to fixed price one without commensurated amenable
structure: an amenable, ergodic, partially doubly recurrent (PDR) imp action with infinite non-atomic components.
`fpbs-hyperbolic-bb-criterion-obstruction` (item 4) forces such an action to carry a boundary map `xi : Z -> dGamma`.
`fpbs-rank-one-lebesgue-boundary-diagonal-dissipative` then forces the class of `xi_* mu` to be singular to Lebesgue
measure, and it named the next test objects: Maharam extensions of singular classes, such as Patterson--Sullivan
classes. This claim treats every such class at once, and every other class of positive dimension. What is left is a
class of "size zero", made precise below.

**The heretical point.** Earlier obstructions all used the *geometry* of the Radon--Nikodym cocycle: property (P),
horofunctions and scaling heights. That assumption is not needed. The only input is the *size* of the boundary
class, and the proof is a Borel--Cantelli count.

**Setting.**
- `Gamma` is a nonelementary hyperbolic group with a `delta`-hyperbolic Cayley graph and base point `o = e`.
- `(x|y)_o` is the Gromov product. The thin shadow is
  `O_s(x) = {zeta in dGamma : (x|zeta)_o >= |x| - s - 2 delta}`.
- `d_eps` is a visual metric on `dGamma`.
- `(Z, mu)` is an imp `Gamma`-space. `xi : Z -> dGamma` is measurable and `Gamma`-equivariant.
- `nu_B = xi_*(mu|_B)` for `B` of finite measure.

**Definitions.**
- A finite measure `lambda` on `dGamma` is **shadow-summable** if
  `S_s(lambda) = sum_{g in Gamma} lambda(O_s(g)) lambda(O_s(g^{-1})) < infinity` for every `s >= 0`.
- `lambda` is **Dini** if its modulus `omega(r) = sup_zeta lambda(B(zeta,r))` satisfies
  `int_0^1 omega(r) dr/r < infinity`.

**Theorem A (shadow-product criterion).** Suppose `Z` is covered, up to a null set, by countably many sets `B` of
finite measure such that any two lie in a third, and `nu_B` is shadow-summable for each. Then `Gamma` acts totally
dissipatively on the crossing part `{(z,z') : xi(z) != xi(z')}` of `(Z x Z, mu x mu)`. If `Z` is ergodic, it is not PDR.

**Theorem B (Dini classes).**
1. Every Dini measure is shadow-summable.
2. If `xi_*(mu|_B)` is absolutely continuous with respect to one finite Dini measure `lambda` for every `B` of finite
   measure, then the hypothesis of Theorem A holds. The sets `B` are cut out by bounds on the density against
   `lambda`.
3. Consequently, the crossing diagonal is totally dissipative, and an ergodic `Z` is not PDR.

**Theorem C (ergodic dichotomy).** Let `C` be a `Gamma`-quasi-invariant ergodic measure class on `dGamma`. Then
either:
- `C` is absolutely continuous with respect to a single finite Dini measure, or
- `C` is singular to **every** finite Dini measure.

If some measure in `C` has positive lower local dimension (for `d_eps`) on a set of positive measure, the first case
holds.

**Corollary (what a certificate must look like).** Let `Gamma` be a nonelementary hyperbolic group, for instance a
cocompact lattice in `Sp(n,1)` or `F_4^(-20)`, or a closed hyperbolic 3-manifold group. Suppose `Gamma` has an
amenable ergodic PDR imp action with `Con` conull. Then its Zimmer boundary class is singular to every Dini measure on
`dGamma`. In particular every measure in that class has lower local dimension `0` almost everywhere. The following are
all killed, together with their finite-measure extensions and every imp action with a boundary map into their class:
- Maharam extensions of Patterson--Sullivan measures of every `Gamma`-invariant hyperbolic metric quasi-isometric to
  the word metric, including the Riemannian metric. This covers the Lebesgue class, recovered by a new proof.
- Maharam extensions of harmonic measures of random walks with finite first moment and finite entropy, which have
  positive dimension (imported, see the proof).
- Maharam extensions of Gibbs and quasi-conformal measures of Hölder cocycles.
- Maharam extensions of any class with one positive-dimensional measure, whatever its Radon--Nikodym cocycle does
  along geodesics. So this includes classes that fail property (P), which were the named survivors.

**Calibration.**
- *Free and surface groups.* Their cost is greater than 1, so nothing may pass. The theorem agrees, and it only
  removes candidates.
- *`Gamma = Z` fails, as it must.* The thin shadows of `n` and `-n` are the two fixed points, for every `n`. So the
  shadow sum of a measure with both atoms diverges, and no conclusion is drawn.
- *Shadow-summability is sufficient, not necessary.* An atomic class on the orbit of a loxodromic fixed point has a
  divergent shadow sum. Its crossing diagonal is still dissipative away from the pairs `{eta, eta*}` of loxodromic
  fixed points, because the other pair stabilizers are finite, and PDR still fails (proof, Step 7). So failure of the
  hypothesis does not produce a certificate.
- *Consistency with pair maps.* The Bowen--Margulis current action on `d^2 Gamma` has a boundary map with a
  Patterson--Sullivan class. Theorem A makes its crossing diagonal dissipative, consistent with item 1 of
  `fpbs-hyperbolic-bb-criterion-obstruction`.

**Reduction left (named, open).** The Bevilacqua--Bowen route to fixed price one for a cocompact `Sp(n,1)` lattice
requires an ergodic, nonatomic, `Gamma`-quasi-invariant measure class on `S^{4n-1}` that is singular to every Dini
measure. Its sharper Borel--Cantelli sum must also diverge: for a Maharam extension, this is the sum over `g` of
`a_g(U) a_g(V)`, where `a_g(W) = nu{eta in W ∩ g^{-1}W : |log D_g(eta)| <= R}` (proof, Remark 3). If every
nonatomic quasi-invariant ergodic class of a hyperbolic group dominates a Dini measure, then Bevilacqua--Bowen
certificates do not exist for any hyperbolic group. Atomic classes are excluded separately (proof, Step 7). The
first question is whether "Dini-singular" quasi-invariant ergodic classes exist at all for a cocompact lattice.

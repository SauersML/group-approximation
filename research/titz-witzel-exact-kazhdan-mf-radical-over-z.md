---
rg: 2
id: titz-witzel-exact-kazhdan-mf-radical-over-z
kind: claim
title: A finitely presented torsion-free group has an exact proper Kazhdan MF radical and quotient Z
distinct_from:
  torsion-free-sofic-exact-mf-radical-over-z: That target additionally requires the total group to be sofic; every other clause is proved here, and its remaining soficity is the explicit three-permutation gate.
  titz-witzel-mapping-tori-are-virtually-products: That classifies every automorphism mapping torus of each of the five candidate kernels; this extracts the strongest unconditional existence theorem in direct-product form.
artifacts:
  - research/artifacts/titz-witzel-sofic-structure-audit-2026-08-26.md
---

**Correction (2026-09-13, lane ex-fp-kazhdan-titz-witzel). OPEN, not established.**
- The proof route `titz-witzel-exact-kazhdan-mf-radical-over-z-proof` requires
  `simple-kazhdan-groups-have-full-mf-radical`. That claim is refuted by
  `simple-kazhdan-lef-group-from-minimal-subshift`. Its step "MF implies weakly quasidiagonal"
  fails for groups (`operator-mf-group-not-weakly-quasidiagonal-exists`).
- So the MF clause below is unproved, and so are "`G` is non-MF" and `(TWE2)`.

What survives, for `G = K x Z` with `K` a Titz Mite--Witzel residual:
- `G` is finitely presented and torsion-free, and `K` is finitely presented, infinite, simple
  and Kazhdan (`titz-witzel-simple-kazhdan-cat0-lattices-exist`).
- `Rad_MF(G) <= K x {0}`, because `G -> Z` has an MF target.

Moreover the open clause is equivalent to non-MF-ness of `K`:
- If `K` is not MF, then every homomorphism from `K` to an MF group has kernel `K` (simplicity).
  So `Rad_MF(G) = K`.
- If `K` is MF, then `(k,m) |-> diag(u(k), v(m))`, for embeddings `u` of `K` and `v` of `Z` into
  norm-corona unitary groups, embeds `G` in the unitary group of the norm corona of the block
  sizes. So `G` is MF and `Rad_MF(G) = 1`.

So `(TWE1)` holds exactly when `K` is not MF. Whether any finitely presented infinite simple
Kazhdan group is MF is open. By `kazhdan-mf-hyperlinear-fragment`, a simple Kazhdan MF group is
hyperlinear, so the failure of this claim would make `K` hyperlinear.

The original statement follows.

There exist a group `G` and a nontrivial normal subgroup
`K normal G` such that

```text
G is finitely presented and torsion-free,
K is finitely presented, infinite, simple and has property (T),
Rad_MF(G)=K,                  G/K ~= Z.                 (TWE1)
```

The subgroup `K` is normally generated in `G` by every one of its nonidentity
elements.  The group `G` is non-MF, and for every countable MF group `M`,
precomposition with `G->Z` is a bijection

```text
Hom(Z,M) ~= Hom(G,M).                                  (TWE2)
```

Thus the requested torsion-free exact-radical theorem is unconditional in
every clause except soficity (and hence the requested route to
hyperlinearity).  For this witness, `G` is sofic exactly when `K` is sofic.
That single unresolved assertion is equivalent to the explicit
three-permutation, twelve-relator gate in
`titz-witzel-soficity-is-one-finite-csp`.

**2026-09-13.** The paragraph above predates the correction: the MF clause is open as well.

DERIVATION
titz-witzel-exact-kazhdan-mf-radical-over-z-proof

## Attempts

- **Compression-defect mechanisms (2026-09-17, swarm-0917-w4-tf-titz-radical). Dead, for every
  member of the class.** `abelian-extensions-kill-kcf-compression-defects` proves: if `K` is a
  Titz Mite--Witzel residual, `G` contains `K` normally with `G/K` torsion-free abelian (`K x Z`,
  every mapping torus `K semidirectProduct_phi Z` with `phi` of any outer order, `K x| Z^d`), and
  `L <= G` is Kazhdan, then `D_G(L) = 1`.
  - *Invariant.* Centralizers in `K` of nontrivial Kazhdan subgroups are trivial
    (`kazhdan-subgroups-of-cat0-cd-two-have-trivial-centralizers`).
  - *Step where every member dies.* For a compressor `s` and `z in C_G(L)`, the commutator
    `[s,z]` lies in `K` (abelian quotient) and centralizes `s L s^-1`, so it is `1`. Hence every
    defect generator `[g z g^-1, l]` with `g in G_comp(L)` is trivial.
  - *Consequences.* `normal-kazhdan-defect-non-mf`, `split-cyclic-kazhdan-defect-exact-mf-radical`
    and `compression-defect-dies-in-mf-under-mark-stability` are all vacuous on these `G`. The
    finite-normal and finite-order central-mark branches are vacuous in torsion-free groups.
    Stability of the simple kernel at a point `w != 1` is equivalent to "`K` is not MF", so it is
    a restatement.
  - So the open clause "`K` is not MF" is not reachable by any non-MF mechanism now established
    in the graph. A proof needs a mechanism that does not pass through a compression-centralizer
    commutator, a finite normal subgroup, or a finite-order central mark.

- **Perturbative mechanisms (2026-09-17, swarm-0917-w5-tf-titz-radical). Dead for the whole class; the
  open clause is reframed.** This starts where wave 4 stopped and does not reuse compression defects.
  - *Result.* `simple-kazhdan-mf-lives-in-gap-near-representations` (ESTABLISHED):
    - (A) every finitely presented group with `H_1(K;Q) = 0` has dimension-free operator-norm linear
      rigidity `D(u) <= C d(u)` on `D(u) <= eps_0`, with constants read off the inverse of the
      exponent-sum matrix;
    - (B) for the residual `K` and `0 < t < kappa`, "`K` not MF" is equivalent to
      `inf_k delta_t(k) > 0`, where `delta_t(k)` is the least relator defect of a tuple in `U(k)^S`
      with `Delta(u) >= t`. It is also equivalent to the global linear inequality (GAP);
    - (C) "`K` is MF" is a `Pi_2` sentence whose matrix is decidable by Tarski--Seidenberg.
  - *Invariant.* `inf_k delta_t(k)`. The deciding models are compressions of an MF model to the complement
    of the lifted Kazhdan projection. They satisfy `D >= sqrt(t/|S|)`.
  - *Step where every member dies.* A perturbative method corrects a near-representation towards a
    genuine one. The only genuine finite-dimensional representation of `K` is trivial (simple and
    non-residually-finite, plus Malcev). So the method works in a neighbourhood of the trivial tuple, where
    its output is (A). (A) holds for the MF group `SL_3(Z)` and says nothing about gap tuples. Padding with
    trivial blocks leaves operator-norm `D` and `d` unchanged, so the Hilbert--Schmidt local-to-global
    trick is unavailable. This class includes:
    - linearization and adjoint-module cohomology at genuine representations;
    - defect-diminishing started near a genuine representation;
    - local rigidity near the trivial tuple.
  - *What remains.* Lower-bound `delta_t(k)` uniformly in `k` for tuples with a uniform Laplacian gap: a
    non-perturbative estimate. It must be operator-norm specific, because on this route `K` is also
    required to be sofic, and simple Kazhdan MF groups are hyperlinear.

- **Non-residually-finite core of `K` (2026-09-17, swarm-0917 d-tfs-twex, calibration). Dead for the
  whole subgroup-and-mark class.** The natural certificate for "`K` is not MF" is the Radu
  product-of-trees core `π_1(S_R) ⊆ K`: it carries the non-residual finiteness of `K` and the mark
  `(xz)^4`.
  - *Result.* `radu-bmw-lattice-is-mf` (ESTABLISHED) proves that `Γ_R ⊇ π_1(S_R)` is MF. It uses the
    new general theorem `free-generalized-wreath-over-residually-finite-group-is-mf` (ESTABLISHED):
    `Z ≀^*_X Q` is MF for every countable residually finite `Q` and countable `Q`-set `X`, so every
    free-kernel tree extension of a residually finite group is MF. The proof uses slow unitary bumps
    along Schreier graphs of finite quotients.
  - *Invariant.* A faithful norm-corona model of `Γ_R`. In it the relators are exact, `δ^4 != 1`, and
    `[y δ^2 y, δ] != 1`.
  - *Step where every member dies.*
    - An argument that finds a non-MF subgroup, or a mark forced into `Rad_MF`, inside the core fails
      at the core, which is MF.
    - A robust transfer of Titz Mite--Witzel Prop. 3.4(4) with Lemma 3.5 ("commutator dies ⇒ mark
      dies") dies at the collapse of `[y δ^2 y, δ]`, which is false in operator norm (item 3). By
      `radu-mark-is-controlled-by-one-commutator`, every other step of that chain is quantitative in
      any bi-invariant metric.
    - Combined with wave 4 (no compression defects) and wave 5 (no perturbative mechanisms), the
      open clause needs input from the building outside `π_1(S_R)`, or from property (T) of `K`
      used non-perturbatively.
  - *What survives.* The Hamming form `radu-commutator-collapse` is untouched: the corona models
    separate at a vanishing fraction of the coordinates. The claim stays OPEN.

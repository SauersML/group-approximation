---
rg: 2
id: hnn-form-of-gkmp-attempt
kind: claim
title: Attempt at a stable-letter (HNN) form of the GKMP free-independence argument, with each step marked
distinct_from:
  gkmp-amalgam-product-mf-permanence: that is the established amalgam theorem; this is an explicit, honestly-graded attempt to extend its selflessness proof to the HNN edge, isolating precisely which step is conjectural.
  fp-forces-hnn-edge-into-free-entropy-obstruction: that states the obstruction abstractly; this carries out the construction to the point of the obstruction and identifies the single lemma that would remove it.
---

OPEN.  This node is an *attempt*, not a theorem.  Each step is tagged
`[PROVED]`, `[STANDARD]`, or `[GAP]`.  The goal statement:

> **Target.**  `G` MF and exact, `H = L <= G` separable, `C` residually
> finite MF, `phi : L -> C` a homomorphism.  Then
> `R = < G x C, s | s(l,1)s^-1 = (l,phi(l)), l in L >` is MF.

Notation: `Q = prod_U M_{d_n}` a matrix ultraproduct with trace `tau`,
`rho : C*_r(G x C) -> Q` a trace-preserving embedding (exists since `G x C`
is MF: `G` MF, `C` MF, one exact ⇒ direct product MF `[STANDARD]`,
Gao-Kunnawalkam-Manzoor-Patchell Lemma 2.4 / Collins-type).

## Step 1 — the two edge models `[PROVED]`

Restricting `rho` to `L` in two ways gives unital `*`-homomorphisms
`pi_0, pi_1 : C*_r(L) -> Q`,
`pi_0(l) = rho(l,1)`, `pi_1(l) = rho(l,phi(l))`.
Both are trace-preserving for the regular character of `L`:
`tau(pi_0(l)) = tau(pi_1(l)) = delta_{l,1}`, since `(l,1)` and `(l,phi(l))`
are nonidentity in `G x C` exactly when `l != 1`.  So `pi_0, pi_1` have the
same `*`-distribution.

`R` is MF iff `rho` extends to a trace-preserving embedding of `C*_r(R)`,
which by the reduced-HNN normal form holds iff there is a unitary `S in Q`
with `S pi_0(l) S^* = pi_1(l)` for all `l` AND `S` is *free enough* from
`rho(G x C)` to reproduce the reduced HNN norms (Britton).  `[STANDARD]`
(Ueda's reduced-HNN description + strong-convergence bookkeeping).

## Step 2 — separability gives a compatible finite-index tower `[PROVED]`

`L = intersection_i H_i`, `H_i < G` finite index, decreasing.  For each `i`,
`G` acts on `G/H_i` (finite); let `sigma_i : G -> U(l^2(G/H_i))` be the
quasi-regular representation.  Since `G` is MF and exact, a diagonal of the
`sigma_i` together with a matricial model of `G` gives an embedding
`rho_G : C*_r(G) -> Q` under which the projection `p_i` onto the
`H_i`-invariant vectors is a well-defined projection in `Q` with `tau(p_i) =
1/[G:H_i]`, and `intersection_i` (the algebras cut by `p_i`) sees exactly
`L`.  `[STANDARD]` (this is the GKMP use of separability: the edge `H` is
approximated by finite-index data, giving a decreasing sequence of corners
adapted to `L`).

## Step 3 — the amalgam model (GKMP) `[PROVED, imported]`

By [[gkmp-amalgam-product-mf-permanence]] the amalgam `G *_L (L x C)` is MF,
witnessed by an embedding `Theta : C*_r(G *_L (L x C)) -> Q` extending `rho_G`
on `G` and a chosen model of `C` on the `L x C` side, such that the copy of
`C` is `*`-free from `G` amalgamated over `L` -- this is the selflessness /
Ozawa free-independence output.  Concretely `Theta` provides, inside `Q`,
mutually `L`-free copies of `G` and of `L x C`.

## Step 4 — building `S` `[GAP]`

We want `S` with `S rho(l,1) S^* = rho(l, phi(l))`.  Equivalently, writing
`rho(l,1) = rho_G(l)` and `rho(l,phi(l)) = rho_G(l) rho_C(phi(l))` with
`rho_C(phi(l))` in the (commuting) `C`-copy, we need
`S rho_G(l) S^* = rho_G(l) rho_C(phi(l))`.

*Sub-attempt 4a (shift model, after GKMP's `G *_H (H x Z) ≅ (*_H G) rtimes
Z`).*  In the infinite amalgamated double `D = *_L G` (copies `G^{(k)}`,
`k in Z`, all sharing `L`), the shift `T` (a unitary in a model of `D rtimes
Z`) satisfies `T rho_G^{(k)}(g) T^* = rho_G^{(k+1)}(g)`, and restricted to
`L` (shared) `T` fixes `rho_G(l)`.  This gives an `S = T`-type unitary that
**fixes** `L`, i.e. implements `phi = trivial`.  It does not produce the
`rho_C(phi(l))` factor.  `[GAP]`: the shift centralizes the shared `L`,
whereas we need it to *shear* `L` by `phi`.

*Sub-attempt 4b (cocycle shear).*  Seek `S = W . T` where `T` fixes `L` (as
in 4a) and `W` is a unitary with `W rho_G(l) W^* = rho_G(l) rho_C(phi(l))`.
Since `rho_C(phi(l))` commutes with `rho_G(L)` and lies in the free `C`-copy,
`W` must conjugate `rho_G(l)` to `rho_G(l) v(l)` with `v(l) = rho_C(phi(l))`
a unitary representation of `L` in the relative commutant of `rho_G(L)`.
Such a `W` exists iff the representation `l -> rho_G(l)` is unitarily
equivalent to its shear `l -> rho_G(l) v(l)` inside `Q`.  `[GAP -- this is
the crux]`.

## Step 5 — the crux, stated exactly `[GAP]`

The obstruction is a single lemma:

> **Shear Lemma (wanted).**  Let `pi : L -> Q` be the regular model of `L`
> (`L` free of finite rank) and let `v : L -> Q cap pi(L)'` be a unitary
> representation of `L` into the relative commutant with `tau(v(l)) =
> delta_{l,1}`.  Then `pi` and `pi . v` are unitarily equivalent in `Q`.

* For `rank(L) = 1` this is TRUE
  ([[hnn-over-infinite-cyclic-subgroups-preserves-mf]], spectral
  equidistribution: `pi(l) = z^l`, `pi(l)v(l) = (zv)^l`, `z` and `zv` both
  Haar unitaries, conjugate).  `[PROVED for rank 1]`
* For `rank(L) >= 2` the Shear Lemma is **false in general** by Voiculescu
  free entropy (two free-Haar tuples with the same distribution are not
  approximately unitarily equivalent).  `[REFUTED in general]`

So Step 5 cannot hold for arbitrary `v`.  The only remaining hope is that the
**specific** `v` from the compiler -- `v(l) = rho_C(phi(l))` with `phi` the
Higman evaluation map and `C` residually finite -- is special enough.

## Step 6 — the specific `v` `[GAP, and the honest end of the attempt]`

`phi : L -> C` is the evaluation homomorphism of the Higman rope; its image
`phi(L)` generates `C` (that is how `C` is encoded), and `C = B2(1)` is
residually finite on `INF`.  The question is whether `v = rho_C . phi` is a
*coboundary shear*, i.e. whether some `W` in the free `C`-copy's normalizer
implements `pi ~ pi.v`.  Two honest observations, neither conclusive:

* **Against.**  `v` is a faithful (its image generates `C`, infinite) unitary
  representation of the free `L` into the commutant, exactly the data the
  free-entropy obstruction forbids from being a coboundary in general.  There
  is no evident reason the Higman `phi` avoids maximal free-entropy
  dimension.
* **For.**  `v` factors through `C`, which is residually finite, so `v` is
  a limit of finite-dimensional representations; and `pi` is the regular
  model.  A regular model sheared by a *finite-dimensional* `v` IS conjugate
  to `pi` (induction/Fell absorption: `pi (x) 1 ~ pi (x) v_fin` when `v_fin`
  is finite-dim, because `lambda (x) any finite-dim ~ lambda (x) 1` for the
  regular representation `lambda` of a free group -- Fell's absorption
  principle).  `[PROVED for finite-dimensional v]`.  The gap is the passage
  from finite-dimensional `v` (each finite quotient of `C`) to the limit `v`
  (all of `C`): Fell absorption gives conjugacy at each finite level with a
  conjugator `W_i` whose norm-control across `i` is not established.

## Verdict

The attempt reduces the Target to the **uniformity of the Fell-absorption
conjugators** `W_i` as the finite quotients of `C` exhaust it: each finite
level is conjugate (Fell), but a single ultraproduct unitary `S` requires the
`W_i` to converge.  That uniformity is precisely a strong-convergence /
selflessness statement of the GKMP type, now for the *sheared regular*
representation rather than the amalgam -- and it is the one genuinely open
lemma.  This is strictly sharper than "adapt GKMP Sections 3--6": it is Fell
absorption made uniform along a residual chain, against a free-entropy
non-uniformity that Step 5 shows is real for generic shears.

## Attempts

Recorded above inline (Steps 4a, 4b, 5, 6).  The rank-1 case and the
finite-dimensional-`v` case are proved; the open point is the uniform limit.

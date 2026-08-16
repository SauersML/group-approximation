# Reconstruction of the circulated action-form collapse criterion

**Date:** 2026-08-16
**Status of this document:** SECOND-HAND. The circulated PDF is still not in
this repository. What follows is a structured account relayed to the project
on 2026-08-16, carrying internal anchors (theorem/lemma numbers and one line
range) that a later reader can check against the primary once it is obtained.
Nothing here is treated as a proof of a mathematical statement on its own; the
one mathematical step worth keeping is reproved independently in
`matricial-mautner-fixed-subspace` and in section 33 of
`multi-mover-hnn-dossier-2026-08-15.md`.

---

## 1. What the source proves

For a countable group, MF is defined there as admitting an injective
homomorphism into the unitary group of a norm matrix corona `Q_d`. The target
is a group

    W = (direct sum over X of C2) semidirect G,      X = G/Gamma,

with an order-two lamp `a_x` at every site, lamps at distinct sites
commuting, and `G` permuting the sites. The conclusion is that one *named*
element is killed by every corona representation, hence no such
representation is injective.

## 2. Theorem 4.1 and its three hypotheses

Data: `Gamma <= G` with property (T), and `t in G` with

    H := t Gamma t^-1  <  Gamma      (proper),
    Gamma = <H, gamma>               for a single gamma in Gamma \ H.

The third condition is the one the 2026-08-15 email proposes to delete.

## 3. The basepoint and the named defect

The witness site is

    x_0 = t Gamma,

for which `h x_0 = x_0` iff `t^-1 h t in Gamma` iff `h in t Gamma t^-1 = H`.
So `Stab_Gamma(x_0) = H` exactly, and `gamma x_0 != x_0` because
`gamma not in H`. The named defect is

    b = a_{gamma x_0} a_{x_0}  !=  1.

This matches the witness-site identification proved in-repo as
`Sofic/AscendingHNNStabilizer.smul_tSite_eq_iff`.

## 4. The proof skeleton relayed

1. Assume some corona representation `pi` has `pi(b) != 1`.
2. Each lamp image `v_x = pi(a_x)` is an involution; set `e_x = (1 - v_x)/2`,
   a projection. The `e_x` commute.
3. (Lemma 3.2 of the source) A countable commuting family of projections in
   the corona admits coordinatewise projection lifts that commute *exactly*
   at every finite stage.
4. Define the rank distance `d_n(x,y) = rank(e_{x,n} - e_{y,n})`: for
   commuting projections this counts the coordinates on which the two lamps
   disagree.
5. Operator-norm asymptotic covariance plus the fact that projections at
   operator distance `< 1` have equal rank makes `d_n` exactly translation
   invariant at late stages.
6. Normalize by `k_n = d_n(x_0, gamma x_0) >= 1`.
7. **Condition (iii) is used in exactly one place** — relayed as lines
   509--526 of the source — to write an arbitrary `g in Gamma` as a word in
   `H` and `gamma^{+-1}`, whose `H`-letters cost zero displacement and whose
   `gamma`-letters cost `k_n`, giving `delta_n(g) <= C_g k_n`.
8. Rescale the Frobenius norm by `k_n`. For commuting projections
   `Tr((e_x - e_y)^2) = rank(e_x - e_y)`, so rank distance becomes squared
   Hilbert distance, which is the geometry property (T) acts on.
9. In the ultraproduct, `c(g) = e_{g x_0} - e_{x_0}` is a genuine 1-cocycle,
   bounded by step 7, with `c(h) = 0` for `h in H` and `c(gamma) != 0`.
10. Property (T) makes `c` a coboundary, producing a vector fixed by `H` but
    not by `Gamma`.
11. (Lemma 2.1 / Corollary 2.2, the "matricial Mautner lemma") In the corona
    that vector cannot exist, because stable finiteness forces the `H`-fixed
    and `Gamma`-fixed subspaces to coincide when `H` is a *conjugate* of
    `Gamma` contained in `Gamma`. Contradiction.

## 5. The concrete instance (section 5 of the source)

    R = F_2[x,y],   Gamma = EL_3(R),

which has property (T) by Ershov--Jaikin-Zapirain. The self-embedding is
induced by the ring map `x |-> x`, `y |-> xy`, giving

    H = EL_3(F_2[x, xy]) < Gamma,

proper because `y` is not in `F_2[x,xy]`. Condition (iii) is then discharged
by an explicit lemma (Lemma 5.1 of the source): `Gamma = <H, e_12(y)>`.

## 6. What this changes for the project

- The engine is **stable finiteness of the matrix corona**, applied to the
  Kazhdan projections of `Gamma` and of its conjugate copy `H`. That is the
  same resource the in-repo compression proof uses as *equal-rank reversal*
  at each finite stage; the two are the finite and corona-level phrasings of
  one fact. See `matricial-mautner-fixed-subspace`.
- Condition (iii) is confined to the word estimate, exactly as the email
  claims. The estimate survives the multi-mover replacement; what does not
  survive unrepaired is the passage from a subsequence to the corona
  (section 6 of the dossier), which finite block amplification fixes.
- The source's concrete instance is an `EL_3` over a polynomial ring; the
  in-repo concrete instance is an affine matrix group with an index-eight
  doubling. They are independent realizations of the same structural input:
  a property-(T) group that is not co-Hopfian.

## 7. Trust surface

Every numbered anchor above (Theorem 4.1, Lemma 2.1, Corollary 2.2,
Lemma 3.2, Lemma 5.1, lines 509--526) is reported, not read here. Anything
this project asserts as established must therefore either be reproved in the
dossier or be Lean-checked in-repo; this file is provenance, not warrant.

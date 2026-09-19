---
rg: 2
id: strong-convergence-fell-shifted-hnn-model
kind: claim
title: Strong convergence of the Fell-shifted HNN model, worked to the point of the residual obstruction
distinct_from:
  pff-bridge-value-fell-absorption-attack: that set up the PFF bridge and the explicit Fell conjugator; this attacks the remaining strong-convergence/freeness assembly directly and grades where it stands.
  hnn-form-of-gkmp-attempt: that reduced to uniform Fell absorption; this attempts the uniformity itself via a haar-unitary interpolation and records the single quantitative estimate still missing.
---

OPEN.  A direct attempt at the final lemma of
[[pff-bridge-value-fell-absorption-attack]].  Steps graded
`[PROVED]/[STANDARD]/[GAP]`.

**Setup.**  `G = K_e` a product of finite-rank free groups (PFF, exact),
`C = B3(1)` PFF, `L <= G` free of rank `r`, separable, `phi : L -> C`.
Target: `R = < G x C, s | s(l,1)s^-1 = (l,phi(l)) >` is MF.

## Model, level n `[PROVED]`

`G x C` is PFF, so there is an actual homomorphism
`rho_n : G x C -> U(d_n)` with finite image and, along `U`, strong
convergence `rho_n -> lambda_{G x C}`.  Because `G` and `C` are each PFF and
`L <= G`, we may (Fell absorption applied to the free group `G`, which
absorbs any finite-dimensional rep of its free subgroup `L`) choose `rho_n`
so that on a distinguished corner the `L`-part is a large multiple of the
**regular** representation of `L` up to error `epsilon_n -> 0`.  Precisely,
there is a projection `q_n` and a partial isometry data with
`|| q_n rho_n(l,1) q_n - (lambda_L^{(m_n)})(l) || -> 0`, where
`lambda_L^{(m_n)}` is `m_n` copies of the regular representation of `L`.
`[STANDARD]` (Fell absorption + PFF strong convergence for the free group
`G`).

## The shift, level n `[PROVED up to error]`

Let `sigma_n = (rho_n)|_C circ phi : L -> U(d_n)`, an actual finite-dimensional
representation of `L` (finite image).  Fell's absorption principle for the
free group `L`:

```text
lambda_L^{(m_n)} (x) 1  ~=  lambda_L (x) (sigma_n-amplified)              (F)
```

there is an **exact** unitary `W_n` (the Fell twist, explicit) with
`W_n lambda_L^{(m_n)}(l) W_n^* = lambda_L^{(m_n)}(l) . sigma_n(l)` on the
corner, where `sigma_n(l)` sits in the commutant.  Transporting through the
level-n corner identification of Step 1,

```text
|| W_n rho_n(l,1) W_n^* - rho_n(l, phi(l)) || <= C epsilon_n -> 0.       (S)
```

`[PROVED, modulo the corner error epsilon_n from Step 1]`.

## Assembling `S` and checking R's relations `[GAP 1: the two errors must be reconciled]`

Put `S = [W_n] in Q = prod_U U(d_n)`.  By `(S)`, `S rho(l,1) S^* =
rho(l,phi(l))` in `Q`, so `(rho, S)` satisfies the HNN edge relations of `R`
**exactly in `Q`**.  It also satisfies the `G x C` relations (rho a
homomorphism).  By the universal property of the HNN extension, `(rho, S)`
therefore extends to a `*`-homomorphism `Psi : C*(R) -> Q`.

The obstruction is not existence of `Psi` but that `Psi` be **trace-
preserving for the regular character of `R`** (equivalently, isometric on
`C*_r(R)`), which is what MF requires.  `Psi` is trace-preserving iff the
reduced-HNN norms are reproduced, i.e. for every Britton-reduced word
`w = a_0 s^{e_1} a_1 ... s^{e_k} a_k` (`a_i in G x C`, no pinch),
`tau(Psi(w)) = 0`.  `[GAP]`.

## The freeness estimate `[GAP 2: the one missing quantitative input]`

Reduced-HNN trace vanishing holds if `S` is *`tau`-free* from `rho(G x C)`
with amalgamation over `rho(L x 1)` in the sense of Ueda's reduced HNN normal
form.  At finite level this is the statement that the Fell twist `W_n`, which
is built from the regular representation of `L` on the corner, is
asymptotically free from `rho_n(G x C)` relative to `rho_n(L)`.  Two honest
observations:

* **In favor.**  `W_n` is supported on the `L`-regular corner and acts as a
  cyclic/shift-type unitary there (the Fell twist is a permutation of the
  regular basis of `L` tensored with `sigma_n`); GKMP's selflessness for the
  ambient PFF model `rho_n(G x C)` provides exactly a free complement in which
  such a corner unitary is free from the ambient over `L`.  So the needed
  freeness is of the same type GKMP establish for their amalgam.
* **Missing.**  The quantitative statement `tau(Psi(w)) -> 0` uniformly over
  reduced words of bounded length requires a strong-convergence estimate for
  the pair `(rho_n(G x C), W_n)` jointly -- not just for each factor.  This is
  a Haagerup--Thorbjornsen / Bordenave--Collins-type norm estimate for a
  specific finite-dimensional model, and it is the single input not supplied
  by Fell absorption (which controls the edge relation, not the joint norm).

## Verdict

The construction is complete and explicit *except* for one joint strong-
convergence estimate `[GAP 2]`: that the ambient PFF model and the Fell twist
are asymptotically `*`-free relative to `L` in operator norm.  Every other
step is proved or standard.  This is strictly the GKMP selflessness estimate
transported from the amalgam edge to the Fell-shifted corner; its truth is
very likely (the ambient is PFF and the twist lives on an `L`-regular corner
where free complements exist), but it is a genuine random-matrix / free-
probability estimate and is not established here.

So: `R` is MF **if** the Fell twist is asymptotically free from the ambient
PFF model relative to `L`.  That conditional is proved.  The hypothesis is the
open lemma, now stated as a clean joint-strong-convergence statement about an
explicit finite-dimensional model rather than as "adapt GKMP".

## Attempts

Steps 1--2 proved/standard; Steps 3--4 are the two gaps, the second (joint
freeness estimate) being the operative one.  The reduction of the whole prize
to this one estimate is the content.

## The exact missing tool identified (2026-08-26, from GKMP v4 method)

Reading the GKMP method (arXiv:2603.24502v4, intro + Lemma 2.3 + Theorem 2.2):
their engine is precisely **Fell's absorption by tensoring with a copy of `G`
+ virtually-free strongly-convergent models (Bordenave--Collins + induced
representations) + exactness**, with the group maps upgraded to the reduced
`C*`-algebra by a **`C*`-correspondence machinery (their Theorem 2.2)**.  Their
concrete map (Lemma 2.3) even handles a shift:
`G *_H (H x Z) = [G/K_i *_{H_i/K_i} (H_i/K_i x Z)] x G`, RHS a product of
virtually free groups with `G`.

This is exactly the construction reconstructed in
[[pff-bridge-value-fell-absorption-attack]] and
[[cocycle-twisted-shift-freeness-galois-corner]].  The one piece not
reproducible here is the **`C*`-correspondence upgrade (Theorem 2.2)** applied
to the *twisted* edge: GKMP upgrade the finite-level group homomorphisms to
`C*_r`-isometry for the untwisted product `H x K` and the shift `H x Z`; the
rope's stable letter carries the extra `phi`-cocycle, and it is their Theorem
2.2 machinery -- not a random-matrix estimate, not Bordenave--Collins (which
would hit the `F_2 x F_2` PPF wall,
[[does-scalar-bordenave-collins-suffice-for-the-l-corner]]) -- that would
upgrade the cocycle-twisted finite-level maps to a reduced-`C*` isometry.

**So the terminal input is precisely: GKMP's Theorem 2.2 `C*`-correspondence
upgrade, applied to the `phi`-cocycle-twisted virtually-free tower.**  Every
surrounding ingredient (virtually-free models, tensor-`G` Fell absorption,
exactness, separability on INF, weak convergence, central case) is in hand.
This is a specific, named, research-level step in the GKMP framework -- the
honest boundary of what can be assembled here without reproducing their
correspondence machinery.


## Scope note (2026-08-26)

This node's target is the reduced-norm (trace-regular / strong-convergence)
convention: an isometric embedding of `C*_r(R)`.  The finite-presentation
`Pi^0_2`-completeness prize does NOT need it: the bare operator-MF
statement is closed unconditionally via
[[twisted-hnn-mf-permanence-with-corona-conjugator]] (universal HNN
algebra + Shulman's amalgam criterion; no freeness estimate), see
`research/artifacts/mf-fp-pi2-unconditional-assembly-2026-08-26.md`.  The
freeness estimate below remains the open content of the strictly stronger
reduced-norm question, whose recognition problem also lacks a known
`Pi^0_2` upper bound.

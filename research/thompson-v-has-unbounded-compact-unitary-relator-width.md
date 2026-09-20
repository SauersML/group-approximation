---
rg: 2
id: thompson-v-has-unbounded-compact-unitary-relator-width
kind: claim
title: Thompson's group V has unbounded compact unitary relator width, so it embeds in a quotient of an algebraic ultraproduct of unitary groups
refuted_by: [thompson-v-has-bounded-compact-unitary-relator-width]
distinct_from:
  thompson-v-hyperlinear: that asks for approximations in normalized Hilbert--Schmidt distance; this asks only that no single constant bounds the relator width of one element in every dimension, which hyperlinearity implies, and which amounts to a homomorphism into an abstract quotient of an algebraic ultraproduct with no metric.
  kl-holds-over-thompson-v: that is injectivity of every nonsingular coefficient map over V; this is a sufficient condition for it that mentions no equation.
  thompson-v-has-no-nontrivial-fd-unitary-representation: that excludes exact representations; this asks for approximate models that escape every bounded conjugacy-class cover of the relator images.
  simple-group-classical-width-finite-field-linear-soficity: that is relator width in finite classical groups; this is width in the compact groups U(d) with U(d)-conjugators.
---

**OPEN.** Let `V = <S | R>` be a finite presentation of Thompson's group `V`, and let `a in F(S)`
represent a nontrivial element. Then for every finite `R_0 <= R` and every `K >= 0` there are some `d` and some
`U in U(d)^S` such that `a(U)` is not a product of at most `K` `U(d)`-conjugates of the elements
`r(U)^(+-1)`, `r in R_0`.

Equivalently, `Rad_cw(V) = 1` in the notation of
`kl-kernel-lies-in-the-compact-unitary-width-radical`. By part (B) of that claim and simplicity of `V`
(`thompson-v-finitely-presented-infinite-simple`), this is also equivalent to each of the following:

- the displayed condition holds for **one** nontrivial `a`;
- `V` embeds in `(prod_i U(d_i))/N` for some normal `N` containing `N_omega`, for some ultrafilter `omega`.

The statement does not depend on the presentation or on `a`.

## Consequences

- **Kervaire--Laudenbach over V.** See `kl-holds-over-thompson-v-via-unbounded-unitary-width`.
- **Where it sits among known properties.** Part (C) of `kl-kernel-lies-in-the-compact-unitary-width-radical` gives the implications
  - hyperlinear => this (`thompson-v-unbounded-unitary-width-from-hyperlinearity`);
  - MF => this;
  - unitary rank or Schatten-`p` approximation => this.

  Radicals shrink on subgroups, so `Rad_cw = 1` for the binary Leavitt unit group, which contains `V`, would also give this.
- **A concrete witness format.** By (C) it suffices to find one conjugation-invariant, symmetric, subadditive length `l` on the
  groups `U(d)` and tuples `U_m` with

  ```text
  max_(r in R) l(r(U_m)) / l(a(U_m)) -> 0.
  ```

  Neither defect has to be bounded below or normalized, so any unnormalized ratio model is enough. Such a model is necessarily
  approximate, because `V` has no nontrivial finite-dimensional unitary representation.

## Attempts

1. **Abelian targets.** Dead as witnesses. `V` is perfect, so `a in [F, F] <<R>>` in `F(S)`. In `U(1)` every commutator
   evaluates to `1`, so `a(U)` is a fixed product of the `r(U)^(+-1)`, with the number of factors independent of `U`. A
   witness therefore needs noncommutative tuples.
2. **Cantor-action truncations and covariant compressions.** Not decided by the existing no-gos.
   - `thompson-v-hyperlinear-via-cantor-action-truncation` and `thompson-v-hyperlinear-via-covariant-compressions` are Dead for
     normalized Hilbert--Schmidt models, through `thompson-v-cantor-orbits-have-no-folner-sets` and
     `thompson-v-covariant-cantor-representations-are-not-amenable`.
   - Those arguments bound the boundary or repair mass below by a fixed fraction of the model size.
   - They do not address models in which the defect of `a` is itself a vanishing fraction but still dominates the relator defect,
     which is the unnormalized ratio format above.
   - No model of that type has been built or refuted.
3. **Permutation ratio models.** These reduce to soficity.
   - Take a permutation tuple on `X` with Hamming defect fraction `delta` for `a` and `epsilon delta` for every relator, where `epsilon -> 0`.
   - The `k`-fold diagonal tensor power acts on `X^k`. A point of `X^k` is fixed exactly when every coordinate is fixed, so `a` moves a
     fraction `1 - (1 - delta)^k`, while each relator moves at most `k epsilon delta`.
   - With `k ~ 1/delta`, `a` stays bounded below and the relators go to `0`. That gives a sofic model separating `a`, and by simplicity it
     makes `V` sofic.
   - So permutation witnesses are no easier than `thompson-v-is-sofic`.
   - The same amplification is not available for unitary rank or Hilbert--Schmidt ratio models, because eigenvalue products can cancel in
     tensor powers. Those formats are the ones not already reduced to an open approximation question.
4. **Unitary rank, Hilbert--Schmidt and operator-norm ratio models** (2026-09-17, swarm-0917-w11). Dead as a route
   independent of approximation. This corrects the last bullet of Attempt 3.
   - `classical-unitary-ratio-witnesses-amplify-to-metric-models` (ESTABLISHED) amplifies every such witness to a
     constant-separation metric model, with the relator defect growing by at most a factor `5`.
   - The invariant is the eigenvalue measure of `a(U)`, which convolves under tensor powers.
     - **Rank.** Cancellation returns mass to the eigenvalue `1` only in alternate steps (`p_j + p_(j+1) <= 1`), so
       `U^(tensor ceil(pi/delta))` fixes at most `3/4`.
     - **HS.** The trace either has modulus at most `1 - s/8`, and the balanced replica `U tensor conj U` crushes it, or it
       has argument at least `sqrt(3s)/2`, and a power of order `1/sqrt s` rotates it into the left half-plane.
     - **Operator norm.** One eigenvalue is rotated by a power of order `1/t`.
   - For simple `V`: a ratio witness in `l_2` is equivalent to `thompson-v-hyperlinear`, one in `l_op` to `V` being MF, and
     one in normalized rank to an embedding in a unitary rank ultraproduct, which makes `V` linear sofic over `C`.
   - What survives: Schatten `p`-lengths with `p` not in `{2, infinity}`, which are not covered, model-dependent lengths, and
     non-metric arguments.
5. **Schatten-`p` ratio models through tensor replicas** (2026-09-19, swarm-0917-w16-w16-ptl-pull, calibration). Dead as a
   class for `p` not in `{2, infinity}`, at the level of eigenvalue measures.
   - `schatten-p-ratio-data-defeat-tensor-replica-amplification` (ESTABLISHED) gives explicit conjugation-invariant eigenvalue
     data for `a(U)` and for every relator. The data satisfy the normalized Schatten-`p` ratio condition.
   - On these data every tensor replica fails:
     - separation `c` of `a` forces relator `p`-length at least `c/5`;
     - the op, HS and rank ratios all stay at least `1/4`.
   - **Invariant.** Convolution of the eigenvalue measures, as in Attempt 4.
   - **Death step.** Atoms spread by count, at degree `~ L_p^(-p)`. Small-angle spreads spread by variance, at degree
     `~ L_p^(-2)`. For `p > 2` an atomic `a` loses to spread relators; for `p < 2` a spread `a` loses to rare relator atoms.
   - So Schatten-`p` witnesses are not reducible to MF, hyperlinearity or rank approximability by the method of Attempt 4.
   - What survives:
     - arguments that use the joint structure of the words, since realizability of the data by words of `V` is not claimed;
     - Schur-functor replicas (`Lambda^k`, `Sym^k`) and compressions;
     - model-dependent lengths.
6. **Unitarily invariant norms through exterior-power replicas** (2026-09-19, swarm-0917-w19-w19-nh-last1,
   operator-algebras). Dead as a class whenever the relator Ky Fan mass vanishes; the node stays OPEN.
   - `exterior-replica-converts-kyfan-witnesses-to-opnorm` (ESTABLISHED) proves two reductions.
     - A ratio witness in any unitarily invariant norm of `g - I` yields a Ky Fan-`k` ratio witness, with loss `|R_0|`, by
       Abel summation of the dual vector. The norm may depend on the dimension and the witness, and includes every
       Schatten norm.
     - The exterior replica `Lambda^1 (+) ... (+) Lambda^j` then turns it into an operator-norm ratio witness with ratio
       `<= pi rho / min(A, 1)`. Here `rho` is the relator Ky Fan mass and `A` the Ky Fan length of `a(U)`.
   - So "Schur-functor replicas" from Attempt 5 do strictly more than tensor powers. They convert Ky Fan data that no
     classical length sees at the identity (worked data: op, HS, rank ratios `k^(1/2)`, `sqrt 2`, `k^2`) into MF data.
   - **Invariant.** The relator Ky Fan mass `rho = max_r KF_k(r(U))`.
   - **Death step.** One exterior replica, then the op amplification of Attempt 4. For `V`, "mass-ratio -> 0" is equivalent
     to `V` MF.
   - What survives: witnesses with relator Ky Fan mass bounded below at every usable index. These force
     `KF_k(a(U)) -> infinity`, and they include all finite realizations of the Schatten-`p` data of Attempt 5, whose
     relators have an eigenvalue `-1`. Non-norm lengths also survive, as do joint word structure and higher Schur functors
     with non-exterior weights.
6. **Every unitarily invariant norm length, through the involution's far mass** (2026-09-20,
   swarm-0917-w22-w22-nh-pull, reframing). Dead as a route independent of `thompson-v-hyperlinear`. This settles the
   first surviving item of Attempt 5.
   - `invariant-norm-ratio-witnesses-localize-hyperlinear` (ESTABLISHED) shows the following. A ratio
     witness in `l(x) = N_d(x - I)`, for **any** unitarily invariant norms `N_d`, makes `V` hyperlinear. This covers every
     Schatten `p`, normalized or not, and Ky Fan norms. For normalized Schatten `p < infinity` the witness is equivalent to
     hyperlinearity.
   - It uses the joint structure of the words, and no amplification.
     - `sigma^2` is a product of relators, so the involution `0w <-> 1w` has spectrum at `+-1` up to `o(eta)`.
     - Normal generation bounds every generator's far mass by `N eta` at every threshold.
     - Cutting each generator down to its far spectral part on their span `E`, with `dim E <= K eta d`, gives a
       normalized Hilbert--Schmidt model.
   - **Invariant.** The far mass `eta` of the involution.
   - **Death step.** The localization to `E` (Step 4 of the proof route). There the relator far mass `o(eta d)` becomes a
     vanishing fraction of `dim E`, while `sigma` keeps `l_2^2 >= 1/K`.
   - The Schatten data (S>) and (S<) of Attempt 5 are therefore realized by words of `V` only in models that already
     yield a hyperlinear model of `V`.
   - What survives: lengths not of the form `N(x - I)`, such as model-dependent lengths, and non-metric certificates of
     `Rad_cw(V) = 1`.

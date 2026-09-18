---
rg: 2
id: cantor-central-gaussian-scale-mixture-witnesses-die
kind: claim
title: "Class-kill for central non-rigidity of C(C,Z) ⋊ V: no sequence of wrapped Gaussian laws, with any covariance, any deterministic mean and any independent random scale, is V-almost invariant, tends to δ_0 and keeps χ(1_C) ≠ 1"
distinct_from:
  cantor-integer-maps-central-direction-has-relative-t: that is the full relative (T) statement; this kills one explicit class of witness laws (Gaussian scale mixtures of one covariance shape), with no restriction on the correlation structure
  cantor-central-witnesses-have-long-range-dependence: that kills witness laws with a nearly independent pair of cone phases and leaves long-range coupled laws and random scales open; this kills Gaussian laws of every correlation structure, including log-correlated and scale-free ones, and random scales shifted by V, which that node names as not ruled out
  cantor-integer-maps-central-growth-criterion: that reduces central growth to almost-invariant laws with χ(1_C) ≠ 1; this excludes the Gaussian ones among them
  extractable-character-spectra-carry-no-almost-invariant-vectors: that kills laws on characters with an equivariant extraction to Prob(C); Gaussian characters are typically scale-incoherent and have no such extraction, and this kills them by their covariance instead
---

**Setting.** `C = {0,1}^N`, `A = C(C,Z)`, `G = A ⋊ V`, `T = R/Z`, `e(x) = e^{2πix}`, and
`Â = Hom(A,T)`. `V` acts on `A` by `(g·f)(x) = f(g^{-1}x)` and on `Â` by
`(g·χ)(f) = χ(g^{-1}·f)`, so `(g·χ)(1_U) = χ(1_{g^{-1}U})`. TV distance is
`d(μ,ν) = sup_B |μ(B) − ν(B)|`.

**The class 𝒢.** A law `ν` on `Â` is in `𝒢` if it is the law of `e∘X` with
`X = m + √s·Y`, where:
- `m ∈ Hom(A,R)` is deterministic;
- `Y` is a centred Gaussian random homomorphism `A → R`, i.e. `(Y(f))_{f∈A}` is jointly
  centred Gaussian and `Y(f + f') = Y(f) + Y(f')` a.s., with covariance form
  `Q(f,f') = E Y(f)Y(f')`;
- `s` is a random scale, independent of `Y`, with `s > 0` a.s. and arbitrary law.

`s ≡ 1` gives all wrapped Gaussian characters of fixed covariance: white noise mod 1, Gaussian
halving trees, log-correlated (free-field type) charges. Random `s` gives the random scale that
`V` may shift.

**Theorem.** There is no sequence `ν_k ∈ 𝒢` with
1. `d(g_*ν_k, ν_k) → 0` for every `g ∈ V`,
2. `ν_k → δ_0` weak* on `Â`, and
3. `ν_k({χ : χ(1_C) = 1}) = 0` for every `k`.

Condition 1 is used only for finitely many `g`, fixed in the proof. If
`cantor-integer-maps-central-direction-has-relative-t` fails, Theorem B of
`cantor-integer-maps-central-growth-criterion` gives a sequence with 1–3: the `A`-spectral laws of
the almost invariant vectors. So the spectral laws of any witness leave `𝒢` eventually, and no
Gaussian scale-mixture design disproves that claim.

**Invariant, and where every member dies.** The invariant is the quadratic inclusion–exclusion
identity of the covariance: for disjoint `U_1, U_2, U_3`,
`Q(1_{U_1⊔U_2⊔U_3}) = Σ_{i<j} Q(1_{U_i⊔U_j}) − Σ_i Q(1_{U_i})`. The angular (scale-free) law of
each pair `(X(1_W), X(1_{W'}))` is a Gaussian angular law. Almost invariance transported along `V`
forces it to be asymptotically the same for every ordered pair of disjoint clopens with proper
union. That forces covariance ratios `1` and correlation `−1/2`. Every member dies at the pair
`(U_1⊔U_2⊔U_3, U_4)`, where the variance ratio must tend to `1`, but inclusion–exclusion
computes `3 − 6·(1/2) = 0`. If the Gaussian part degenerates, the mean alone must be a
`V`-invariant character on finitely many cones, and additivity forces `χ(1_C) = 1`.

**Scope.** This is the sequence (approximate) form of the artifact §3(e), which is exact: `V`
admits no nonzero invariant positive semidefinite form on `A`. It makes rigorous the heuristic kill
"Gaussian white noise mod 1" in `cantor-integer-maps-by-v-have-haagerup-property`. It is not
covered by `cantor-central-witnesses-have-long-range-dependence`, because Gaussian designs can
have correlations of order one between all cones.

**Not ruled out.**
- Mixtures of Gaussians over a random covariance *shape* (for example a random level that `V`
  shifts). Their angular laws are mixtures, which are not identifiable in general.
- Location mixtures (random `m`).
- Non-Gaussian infinitely divisible laws, e.g. compound Poisson laws `exp(−t ψ)`. These are the
  canonical witnesses from a cnd `ψ`, whose Gaussian part on `A` vanishes by the artifact §3(e).

## Status

ESTABLISHED via `cantor-central-gaussian-scale-mixture-witnesses-die-proof`.

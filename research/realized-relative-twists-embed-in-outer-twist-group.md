---
rg: 2
id: realized-relative-twists-embed-in-outer-twist-group
kind: claim
title: Sofic realizations of relatively centralizing elements are classified by one global outer twist group, compatibly with compressors
distinct_from:
  relative-defect-iff-surjective-compressor-endomorphisms: that works inside one sofic host with the quotient Z/(M.C_H(Gamma)); this embeds the ultraproduct quotient N_rel(sigma)/(sigma(M).C(sigma(Gamma))) into the outer twist group of the pair, so every realized twist is one global class and the compressor action is an algebraic endomorphism of that group.
  relative-defect-normalization-dichotomy: that is the equivalence RDD <=> RNORM; this computes the quotient that RNORM is about and identifies which of its elements a given sigma realizes.
artifacts:
  - research/artifacts/hyperbolic-leavitt-cover-relative-defect-2026-09-12.md
---

**ESTABLISHED.** Let `Gamma <= G` be a rigid pair (`Gamma`, `G` Kazhdan,
`Gamma` infranormal in `G`), let `M <= Gamma` be normal in `G`, and let
`sigma : G -> S_U` be a homomorphism into the universal sofic group. Write
`Gamma_s = sigma(Gamma)`, `M_s = sigma(M)`, `C_s = C_{S_U}(Gamma_s)`, and

```text
Aut_M(Gamma_s) = { phi in Aut(Gamma_s) : phi(g) g^-1 in M_s for all g in Gamma_s },
Out_M(Gamma_s) = Aut_M(Gamma_s) / Ad(M_s),
Q_s            = N_rel(sigma) / (M_s . C_s),
```

with `N_rel(sigma)` as in `relative-defect-normalization-dichotomy`.

1. **Twists are global.** `x -> Ad(x)|_{Gamma_s}` is a homomorphism
   `N_rel(sigma) -> Aut_M(Gamma_s)` with kernel `C_s`. The preimage of
   `Ad(M_s)` is `M_s . C_s`, which is normal in `N_rel(sigma)`. So `Q_s` embeds
   in `Out_M(Gamma_s)`: every realized relative element carries one
   automorphism of `Gamma_s`, the same on every component of the model.
2. **Compressors act algebraically.** For a compressor `t`
   (`t Gamma t^-1 <= Gamma`), the formula
   `eps_t(phi) = Ad(sigma(t)^-1) . phi . Ad(sigma(t))`, restricted to `Gamma_s`,
   defines an endomorphism of `Aut_M(Gamma_s)` that maps `Ad(M_s)` into
   itself. The induced endomorphism of `Out_M(Gamma_s)` restricts on `Q_s` to
   `[x] -> [sigma(t)^-1 x sigma(t)]`, and it is **injective** on `Q_s`.
3. **Realized twists are a stabilizer.** A class `[phi]` lies in `Q_s` iff the
   inclusion `iota : Gamma_s -> S_U` and `iota . phi` are conjugate by an
   element of `S_U`. So `Q_s` is the stabilizer, inside the outer twist group,
   of the `S_U`-conjugacy class of the representation `sigma|_Gamma`.
4. **RNORM for sigma.** `sigma(G)` normalizes `N_rel(sigma)` iff
   `eps_t(Q_s) = Q_s` for every compressor `t`.
5. **Hosts.** If `H >= G`, `M` is normal in `H` and `sigma : H -> S_U` is
   injective, then `Out_M(Gamma_s)` is canonically `Out_M(Gamma)`, and
   `z -> sigma(z)` embeds `Q = Z/(M . C_H(Gamma))` of
   `relative-defect-iff-surjective-compressor-endomorphisms` into `Q_s`,
   compatibly with the endomorphisms.

Property (T) enters only in item 2, through the absolute normalization
`sigma(G)` normalizes `C_s`. Property (T) of `M` is not used. Derivation:
`realized-twists-outer-embedding-proof`.

## Consequences

- **What RNORM is about.** `RNORM` asks which subgroups of the single countable
  group `Out_M(Gamma)` arise as stabilizers of `S_U`-conjugacy classes of
  sofic representations of `Gamma`, and whether the algebraic endomorphism
  `eps_t` can map such a stabilizer strictly into itself. The model enters
  only through the conjugacy class of `sigma|_Gamma`.
- **No point-dependent twist data.** A size that assigns numbers to
  (component, realized twist) pairs is constant across components on the
  realized part. The Kun--Thom pigeonhole, a measure-preserving point map with
  a one-sided monotone point function, has no twist-valued point function to
  run on. `conjugation-invariant-sizes-miss-relative-defect` records the
  resulting no-go.
- **The Leavitt cover.** For `hyperbolic-kazhdan-cover-of-leavitt-unit-group`,
  with `M = N` and `Gamma_hat = pi^-1(EL_alpha(R))`, any sofic representation
  of a host containing the cover has `Q = C_(R^x)(EL_alpha(R))` inside
  `Q_s <= Out_N(Gamma_hat)`, and `eps_u_hat(Q_s)` is a proper subgroup of
  `Q_s`. A nonsoficity proof has to show that no stabilizer of a conjugacy
  class of sofic representations of `Gamma_hat` is strictly compressed this
  way.

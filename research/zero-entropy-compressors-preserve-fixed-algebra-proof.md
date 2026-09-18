---
rg: 2
id: zero-entropy-compressors-preserve-fixed-algebra-proof
kind: route
title: A one-sided sigma-algebra gives every past-conditioned term the same entropy floor, and compressors push the fixed algebra inward
target: zero-entropy-compressors-preserve-fixed-algebra
requires:
  - kun-thom-nonsofic-wreath
  - coset-lamp-seed-radical-is-ce-fixed-algebra-rigidity
  - kun-thom-wreath-sofic-radical-is-fibre-parity-kernel
---

All partitions are finite measurable partitions of `(Z, kappa)`, and everything is taken mod null. Put `phi(x) = -x log x - (1-x) log(1-x)` on `[0,1]`. It is continuous, strictly concave, and `phi >= 0` with equality exactly at `x in {0,1}`.

Only finite-partition entropy is used:

- `H(P) = sum_(A in P) -kappa(A) log kappa(A)`;
- `H(P | Q) = H(P vee Q) - H(Q)`;
- `h(T, P) = lim_n (1/n) H(vee_(k<n) T^-k P)`.

The limit exists by subadditivity, and only a lower bound on the averages is used below. `T^-1 P` denotes `{T^-1 A : A in P}`.

Only two elementary identities enter. Both are finite computations.

- **(i) Chain rule.** `H(P vee Q) = H(Q) + H(P | Q)`. This is the definition.
- **(ii) Invariance.** `H(T^-j P | T^-j Q) = H(P | Q)`, because `T` preserves `kappa`.

## Step 1: the monotone entropy lemma (ZE1)

Let `T` be invertible and p.m.p., and let `F` be a complete sub-sigma-algebra with `T^-1 F <= F`. Put `B = T^-1 F`.

**Past partitions lie in `B`.** By induction, `T^-k F <= T^-1 F` for every `k >= 1`: `T^-k F = T^-1 (T^-(k-1) F)`, and `T^-(k-1) F <= F`. So for a partition `P <= F` and any `m >= 1`, the partition `Q_m = T^-1 P vee ... vee T^-m P` consists of `B`-measurable sets. Put `Q_0` = the trivial partition.

**Floor for conditioning on finite partitions of `B`.** Let `E in F`, `P = {E, E^c}`, and `f = E(1_E | B)`. For a partition `Q <= B`,

```text
H(P | Q) = sum_(A in Q) kappa(A) phi( kappa(E cap A) / kappa(A) )
         = integral phi( E(1_E | Q) ) d kappa.
```

Since `Q <= B`, `E(1_E | Q) = E(f | Q)`. The function `phi` is concave, so conditional Jensen gives `phi(E(f | Q)) >= E(phi(f) | Q)` pointwise. Integrating,

```text
H(P | Q) >= delta := integral phi(f) d kappa.                    (1)
```

**`delta > 0` when `E` is not `B`-measurable.** If `delta = 0`, then `phi(f) = 0` a.e., so `f = 1_A` for some `A in B`. Then `kappa(E cap A^c) = integral 1_E 1_(A^c) = integral f 1_(A^c) = 0`, so `E <= A` mod null. Also `kappa(E) = integral f = kappa(A)`, so `E = A` mod null, and `E` is `B`-measurable.

**Chain over the past.** Put `P_j = T^-j P` and `R_j = P_j vee ... vee P_(n-1)`. By (i),

```text
H(R_0) = H(P_(n-1)) + sum_(j=0)^(n-2) H(P_j | R_(j+1)).
```

By (ii), `H(P_j | R_(j+1)) = H(P | Q_(n-1-j))` and `H(P_(n-1)) = H(P | Q_0)`. Every `Q_m` lies in `B`, so (1) bounds each of the `n` terms below by `delta`. Hence `H(vee_(k<n) T^-k P) >= n delta` and

```text
h(T, {E, E^c}) >= delta = integral phi( E(1_E | T^-1 F) ) d kappa.
```

This proves (ZE1).

**Pinsker form.** Suppose `h(T, {E, E^c}) = 0` for every `E in F`. Then every `E in F` is `T^-1 F`-measurable, so `F <= T^-1 F`, and hence `T^-1 F = F`. The hypothesis holds when `h_kappa(T) = 0`, because `h(T, P) <= h_kappa(T)`.

## Step 2: compressors move fixed algebras inward (ZE2)

Let `s Gamma s^-1 <= Gamma`.

- If `E in F_Gamma` and `gamma in Gamma`, then `(s gamma s^-1)(sE) = s(gamma E) = sE` mod null. So `s F_Gamma <= F_(s Gamma s^-1)`.
- Conversely, if `E' in F_(s Gamma s^-1)`, then `gamma (s^-1 E') = s^-1 (s gamma s^-1) E' = s^-1 E'`. So `s^-1 E' in F_Gamma`.

Hence `s F_Gamma = F_(s Gamma s^-1)`. A smaller group has a larger fixed algebra, so `s Gamma s^-1 <= Gamma` gives `F_Gamma <= s F_Gamma`. Applying `s^-1`, we get `s^-1 F_Gamma <= F_Gamma`.

## Step 3: the theorem (ZE3)

Take `T = s in S` (the automorphism `z -> sz`, so `T^-1 E = s^-1 E`) and `F = F_Gamma`. Step 2 gives `T^-1 F <= F`. The hypothesis is that `h(s, {E, E^c}) = 0` for all `E in F_Gamma`. The Pinsker form of Step 1 then gives `s^-1 F_Gamma = F_Gamma`, hence `s F_Gamma = F_Gamma`.

Each `gamma in Gamma` fixes every set of `F_Gamma`. The set of `g in G` with `g F_Gamma = F_Gamma` is a subgroup. So `F_Gamma` is invariant under `H = <Gamma, S>`.

If `E in F_Gamma` and `h in H`, then `h^-1 E in F_Gamma`. So `(h gamma h^-1) E = h gamma (h^-1 E) = E`. Thus `E` is invariant under every `H`-conjugate of `Gamma`, hence under `<<Gamma>>_H`. This gives `F_Gamma <= F_(<<Gamma>>_H) <= F_Gamma`.

The quantitative form is (ZE1) with `T^-1 F_Gamma = s^-1 F_Gamma = F_(s^-1 Gamma s)`, using Step 2 for `s^-1`.

No property of `G` (such as (T)), no freeness and no ergodicity was used.

## Step 4: the Kun--Thom Theorem E pair (ZE4)

`kun-thom-nonsofic-wreath` records verbatim: "Let `q` be a prime power and let `r,d>=3`. Put `R_+=F_q[x_1,...,x_d]` and `R=F_q[x_1^(±1),...,x_d^(±1)]`, and let `SL_d(Z)` act on `R` by monomial substitutions. Then `Gamma=EL_r(R_+)` and `G=EL_r(R) semidirect SL_d(Z)` are residually finite Kazhdan groups, `Gamma` is infranormal but not normal in `G`."

**Exponent representation.** A monomial substitution action is `g . lambda x^v = lambda x^(rho(g) v)` for a homomorphism `rho : SL_d(Z) -> GL_d(Z)`. For the standard conventions (`rho(g) = g`, or `rho(g) = g^(-T)`), `rho` is an automorphism of `SL_d(Z)`, and the argument below does not depend on which one is used. Put `s_ij = rho^-1(e_ij(1))` for `i != j`.

**Compression.** `e_ij(1)` has nonnegative entries, so it maps `N^d` into `N^d`. Hence `s_ij . R_+ <= R_+`. In `G`, conjugation by `s in SL_d(Z)` applies the substitution entrywise, so `s e_kl(p) s^-1 = e_kl(s . p)`. `Gamma` is generated by the `e_kl(p)` with `p in R_+`, so `s_ij Gamma s_ij^-1 = EL_r(s_ij . R_+) <= Gamma`.

**Generation.** Let `S = {s_ij}`. The elementary matrices `e_ij(1)` generate `SL_d(Z)`, so `S` generates `SL_d(Z)`.

- Let `v in Z^d - {0}`. Write `v = c u` with `c >= 1` and `u` primitive. `SL_d(Z)` is transitive on primitive vectors, so `u = rho(g) e_1` for some `g`. Then `g e_kl(lambda x_1^c) g^-1 = e_kl(lambda x^v)`, and `e_kl(lambda x_1^c) in Gamma`.
- `e_kl(p + p') = e_kl(p) e_kl(p')`, and the monomials span `R`, so `EL_r(R) <= <Gamma, S>`.

Hence `<Gamma, S> = G`. This recovers infranormality.

**Normal closure.** `N = EL_r(R)` is normal in `G` and contains `Gamma`. The previous paragraph shows that the normal closure of `Gamma` already contains every `e_kl(lambda x^v)`, so `<<Gamma>>_G = N`.

**Conclusion.** Step 3 with `H = G` gives `F_Gamma = F_N`, which is `G`-invariant, whenever every `s_ij` has `F_Gamma` inside its Pinsker algebra. If `h_kappa(s_0) = 0` for `s_0 = s_12`, then every `s_ij` also has zero entropy:

- For `d >= 3`, `e_ij(1) = D e_12(1) D^-1`, where `D in SL_d(Z)` is a signed permutation matrix sending coordinates `1, 2` to `i, j`. The sign is placed on a third coordinate so that `det D = 1` and the conjugate is `e_ij(+1)`.
- Hence `s_ij = rho^-1(D) s_0 rho^-1(D)^-1`.
- Kolmogorov--Sinai entropy is invariant under conjugation by the p.m.p. automorphism `rho^-1(D)`, so `h_kappa(s_ij) = 0`.

## Step 5: the coset-lamp consequence (ZE5)

**Seeds are fibre-even.** Let `a in N - Gamma`. The cosets `Gamma` and `a Gamma` both lie in the fibre `N/Gamma` of `G/Gamma -> G/N`. So `m_a` meets that fibre in two cosets, and `m_a in K_even = Rad_sof(W)` (`kun-thom-wreath-sofic-radical-is-fibre-parity-kernel`).

**The C2 witness.** `G` is residually finite (Theorem E above), hence sofic, hence hyperlinear. Suppose `m_a notin Rad_hyp(W)`. Clause (C2) of `coset-lamp-seed-radical-is-ce-fixed-algebra-rigidity` records verbatim: "If `A` is hyperlinear and `m_a notin Rad_hyp(L rtimes A)`, such an action exists. One may take the shift on `F_2^X` with an invariant measure and `E = {f : f(x_0) = 1}`." Here "such an action" is the (C1) data: the crossed product is Connes embeddable, and `E` satisfies `kappa(cE triangle E) = 0` for `c in C` and `kappa(aE triangle E) > 0`.

**Positive entropy.** Take `C = Gamma` and `A = G`. Then `E in F_Gamma` but `a in N` moves `E`, so `F_Gamma != F_N`. By Step 4, some `s_ij` fails the Pinsker hypothesis on `F_Gamma`, so `h_mu(s_ij) > 0`. By conjugacy, `h_mu(s_0) > 0`.

## Sanity checks

- **Bernoulli measure.** Take the Bernoulli measure on `F_2^(G/Gamma)`.
  - `F_Gamma` is not `G`-invariant. `{x_Gamma = 1}` is `Gamma`-invariant, and `a` moves it to `{x_(a Gamma) = 1}`, which is a different set.
  - The theorem therefore forces a compressor to have positive entropy, and it does. If `s_0^n g Gamma = g Gamma`, then `g^-1 s_0^n g in Gamma <= N`. But its image in `SL_d(Z) = G/N` is conjugate to `s_0^n`, which is nontrivial for `n != 0`.
  - So `s_0` acts freely on `G/Gamma`. The Bernoulli shift over a free `Z`-set is a product of Bernoulli `Z`-shifts, with entropy `h(s_0) = infinity`.
- **Profinite actions.** Profinite actions have discrete spectrum, hence zero entropy for every element. For compressor-generated pairs the theorem therefore reproves `profinite-action-fixed-algebra-invariant`.
- **Normal `Gamma`.** If `Gamma` is normal in `G`, compressors normalize, `s^-1 F_Gamma = F_Gamma` automatically, and the lemma is vacuous, as it must be.

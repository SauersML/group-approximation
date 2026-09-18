---
rg: 2
id: bi-index-core-makes-normals-core-class-unions-proof
kind: route
title: A product n' = a n b with n, n' in N forces ab in N cap S = 1, so double cosets see only core classes
target: bi-index-core-makes-normals-core-class-unions
requires: [proper-normal-subgroups-miss-the-normally-generating-core, fp-quotient-iff-kernel-finitely-normally-generated]
artifacts:
  - research/artifacts/finite-bi-index-normal-lattice-collapse-2026-09-17.md
---

Hypotheses and notation as in the target: `S` nontrivial simple,
`S <= Gamma`, `Gamma = <<s>>_Gamma` with `1 != s in S`,
`r = |S \ Gamma / S|`, and `N` a proper normal subgroup of `Gamma`.

**0. The imported step.** By
`proper-normal-subgroups-miss-the-normally-generating-core`,
`N ∩ S = 1`. This is the only place simplicity of `S` and the normal
generator are used.

**1. One class per double coset.** Let `n, n' in N ∩ SgS`. Both lie in the
same double coset, so `n' = a n b` for some `a, b in S`. Rewrite

    n' = (a n a^-1) (a b).

Here `a n a^-1 in N` because `N` is normal, and `n' in N`, so
`a b = (a n a^-1)^-1 n' in N`. Also `ab in S`. Hence `ab in N ∩ S = 1`,
so `b = a^-1` and `n' = a n a^-1`. Conversely every `S`-conjugate
`a n a^-1 = a n (a^-1)` of `n` lies in `N ∩ SnS`. So `N ∩ SgS` is empty or
exactly one `S`-conjugacy class.

**2. Class count and normal generation.** By step 1 the map sending an
`S`-class `C ⊆ N` to the double coset containing it is injective. So `N`
has at most `r` classes. The class of `1` is `{1}`, and it is the whole of
`N ∩ S`. Choose representatives `n_1, ..., n_k` of the nontrivial classes,
`k <= r - 1`. Then

    N = {1} ∪ ⋃_i {a n_i a^-1 : a in S}  ⊆  <<n_1, ..., n_k>>_Gamma  ⊆  N,

the last inclusion because `N` is normal. So `N = <<n_1, ..., n_k>>_Gamma`.

**3. Centralized part.** If `c in N ∩ C_Gamma(S)` then its `S`-class is
`{c}`. Distinct such `c` are distinct classes, so by step 2 there are at most
`r` of them. `Z(Gamma)` is normal and centralizes `S`. When `S` is
nonabelian, `Z(Gamma) ∩ S <= Z(S) = 1` and `S != 1`, so `Z(Gamma)` is
proper and `|Z(Gamma)| <= r`. (When `S` is cyclic of prime order the
"in particular" can fail: `Gamma = S` has `r = 1` and `|Z(Gamma)| = |S|`.)

**4. Max-n (r finite).** Let `N_1 <= N_2 <= ...` be normal in `Gamma`. If some
`N_j = Gamma` the chain is constant from `j` on. Otherwise every `N_j` is
proper and omits `s` (a normal subgroup containing `s` is `Gamma`). Then
`N = ⋃ N_j` is normal and omits `s`, so it is proper. By step 2,
`N = <<n_1, ..., n_k>>_Gamma` with finitely many `n_i`. Each `n_i` lies in
some `N_{j_i}`, so `N ⊆ N_J` for `J = max j_i`, and the chain stabilizes at
`J`.

*Ring chains.* Suppose `pi: Gamma ->> EL_n(U) <= GL_n(U)`, `n >= 2`, and
`J_1 ⊊ J_2 ⊊ ...` are proper two-sided ideals of `U`. Let
`rho_J: GL_n(U) -> GL_n(U/J)` reduce entries and
`N_J = pi^-1(ker rho_J)`. Each `N_J` is normal. It is proper, because
`rho_J(e_12(1)) = e_12(1 + J) != I` as `U/J != 0`. The kernels increase
with `J`. The inclusion `N_{J_i} ⊊ N_{J_{i+1}}` is strict: pick
`x in J_{i+1} \ J_i`; any preimage of `e_12(x)` lies in `N_{J_{i+1}}` but
not in `N_{J_i}`. So `Gamma` fails Max-n, and by the previous paragraph no
normally generating simple core of `Gamma` has finite bi-index.

**5. Quotients.** Let `q: Gamma -> Gamma/N`. It maps `s` to a normal
generator of `Gamma/N`. Since `N ∩ S = 1`, `q` restricts to an isomorphism
`S -> SN/N`. It carries each double coset `SgS` onto `q(S) q(g) q(S)`, so it
maps `S \ Gamma / S` onto the double cosets of `q(S)` and the count is at
most `r`. If `Gamma` is finitely presented, step 2 and
`fp-quotient-iff-kernel-finitely-normally-generated` make `Gamma/N`
finitely presented.

Property (T) passes to `Gamma/N`, by the standard one-line argument. Let
`(K, epsilon)` be a Kazhdan pair for `Gamma`, and let `pi` be a unitary
representation of `Gamma/N` with a `(q(K), epsilon)`-invariant unit
vector. Then `pi ∘ q` is a unitary representation of `Gamma` with a
`(K, epsilon)`-invariant unit vector. So it has a nonzero invariant vector,
and that vector is `Gamma/N`-invariant because `q` is onto. Hence
`(q(K), epsilon)` is a Kazhdan pair for `Gamma/N`.

**6. Simple quotient.** Among normal subgroups omitting `s`, every chain has
its union omitting `s`, so Zorn (or step 4 when `r < infinity`) gives a
maximal proper normal subgroup `M`. By the correspondence theorem `Gamma/M`
is simple. Step 5 applies to `N = M`.

∎

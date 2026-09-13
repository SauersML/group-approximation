---
rg: 2
id: hensel-covering-of-nilpotent-kernels-by-commutators
kind: claim
title: A nilpotent normal subgroup is a product of s commutator sets [g_i, K] when no layer of a central series has a functional fixed by all g_i
distinct_from:
  perfect-group-relator-width-over-nilpotent-groups: that corrects lower central layers with conjugates of relators, using the exponent-sum lattice of a perfect group; this covers a kernel with commutators against a few elements of the ambient group, using only the fixed-point-free action on each layer.
  simple-group-width-over-congruence-targets: that is the width theorem over SL_n(R); this is the kernel step behind it, stated for any finite group.
---

**ESTABLISHED (unreviewed, 2026-09-13, lane `ex2-weak-sofic-affine-targets`).**

**Lemma.** Let `Q` be a finite group, with normal subgroups
`K = K_1 ⊇ K_2 ⊇ ... ⊇ K_m = 1` of `Q` such that `[K, K_j] <= K_(j+1)` and every layer `M_j = K_j/K_(j+1)` is
elementary abelian. `Q` acts on `M_j` by conjugation, through `Q/K`. Let `g_1, ..., g_s in Q` and
suppose, for every `j`:

(F) no nonzero linear functional on `M_j` is fixed by all of `g_1, ..., g_s`.

Then every `kappa in K` equals `[g_1, beta_1] ... [g_s, beta_s]` for some `beta_i in K`.

**Covering form.** Let `S <= Q` be a normal subset, and suppose `g_i = z_i P_i` with `z_i in C_Q(K)` and
`P_i in Cons_m(S)`. Then `K <= Cons_(2sm)(S)`.

**Why (F) is the right condition.** The annihilator of `sum_i (g_i - 1) M_j` in the dual space is the
set of functionals fixed by every `g_i`. So (F) says exactly that the linearized commutator map
`M_j^s -> M_j` is onto. Successive approximation then lifts it through all `m` layers, with no loss in
the number of commutators.

**Instances.**
- **Congruence kernels.** `K = ker(SL_n(R) -> SL_n(q))` for a finite chain ring `R`, with `s = 2` and a
  Singer pair (part 1 of `simple-group-width-over-congruence-targets`, Lemma 2.2). One Singer element
  fails (F) on the adjoint layer, whose Singer-fixed space has dimension `n - 1` modulo the scalars.
- **One seed.** If a single `g` has no eigenvalue `1` on any dual layer, then `K = [g, K]`. For example,
  a Singer element of `SL_n(q)` acting on layers that are sums of copies of `F_q^n`, its dual, or
  `Lambda^k F_q^n` with `1 <= k < n`.
- **Cross characteristic.** The layers may have any primes. `K` is nilpotent by the series.

**Model test.**
- *Trivial model.* If every `g_i` acts trivially on the top layer `M_1 != 0`, then (F) fails, and so does
  the conclusion: every `[g_i, beta]` lies in `K_2`, so no element outside `K_2` is reached. On deeper
  layers (F) is sufficient but not necessary, since second-order terms can contribute there.
- *Real object.* Brute force confirms the congruence instance in `SL_3(Z/4)`, `SL_2(Z/9)`, `SL_2(Z/27)`
  and `SL_2(Z/25)` (`research/artifacts/congruence-singer-model-test-2026-09-13.md`).

**What (F) excludes, and where relator width stays open.**
- *Top layer.* If `K/K_2` has a trivial quotient module, commutators with elements of `Q` never reach it,
  since their images lie in the augmentation submodule.
- *Deeper layers.* Coinvariant layers can be reached only at second order, and no bound is on record.
- *For relator width.* Over `K x| T` with a large simple top `T`, no classification-free proof covers
  kernels with such layers at unbounded depth. `relator-width-bounded-by-almost-simple-quotients`
  (unreviewed, via Nikolov--Segal and the classification) reduces relator width to the quotient by the
  intersection of the kernels of the almost simple quotients. That quotient does not see nilpotent
  kernels at all. So these kernels matter for explicit, classification-free bounds, not for whether
  a bound exists.

Derivation: `hensel-covering-of-nilpotent-kernels-by-commutators-proof`. Credit: the successive
approximation is the standard Hensel-type argument for filtered groups; no literature search was run
for this exact statement.

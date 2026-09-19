---
rg: 2
id: chain-configurations-need-unboundedly-many-dilation-eigenvalues
kind: claim
title: In a Baumslag-Solitar chain configuration the middle element dilates the conjugates a^n c a^-n by 2^(2^n), so no group that is abelian over a directed union of finitely generated metabelian groups with boundedly many associated primes contains one; this covers ascending HNN extensions of finitely generated metabelian groups and ascending towers of height three over Z
distinct_from:
  higman-chain-group-pbh-iff-chain-configuration: that reduces BH for the chain group to finding a chain configuration and excludes metabelian and linear groups by direct arguments; this gives the spectral reason behind the metabelian exclusion and extends it to a class of groups of derived length three.
  zoom-tower-germ-groups-give-f-infinity-germ-extensions: that certifies germ extensions whose germ groups are ascending towers; this shows such towers cannot hold a chain configuration below height four.
---

**ESTABLISHED** (lane proof, elementary commutative algebra; not reviewed; no priority claimed).

A **chain configuration** in a group `H` is a triple `(a, b, c)` with `a^-1 b a = b^2`, `b^-1 c b = c^2`
and `c` of infinite order.

## Statement

1. **Super-exponential spectrum.** Put `c_n = a^n c a^-n` for `n >= 0`. Then `b^-1 c_n b = c_n^(2^(2^n))`,
   and every `c_n` has infinite order.
2. **Obstruction.** Let `L ⊴ H` with `H/L` abelian. Suppose `L` is a directed union of finitely generated
   metabelian subgroups `F_i`, and that `|Ass(F_i' ⊗ Q)|` is bounded. Here `Ass` is taken over
   `Q[F_i^ab]`, which is finite by Hall's theorem that `F_i'` is a finitely generated `Z[F_i^ab]`-module.
   Then `H` contains no chain configuration.
3. **Cases.**
   - (a) `L = H` finitely generated metabelian. This recovers the metabelian case of
     `higman-chain-group-pbh-iff-chain-configuration`.
   - (b) `H` an ascending HNN extension of a finitely generated metabelian group `F`. Take `L` to be the
     directed union of the conjugates `t^-k F t^k`, all isomorphic to `F`, so the bound is `|Ass(F' ⊗ Q)|`.
   - (c) Ascending towers `Z = H_0 < H_1 < H_2 < H_3` (each an ascending HNN extension of the previous
     one), provided `H_1 = BS(1,m)` with `m ≠ -1`. Then `H_2` is finitely generated metabelian, so (b)
     applies to `H_2` and to `H_3`.
     - For `m = 1`, `H_1 = Z^2`, and `H_2` is abelian-by-cyclic.
     - For `|m| >= 2`, let `ψ` be the endomorphism. It preserves `Z[1/m]`, the kernel of the map to the
       torsion-free abelianization, and it induces the identity on `H_1/Z[1/m] ≅ Z`, because
       `m^d = m` forces `d = 1`. So `W = ⋃_k t^-k Z[1/m] t^k` is abelian and normal, and
       `H_2/W ≅ Z^2`.

## Proof

- **Item 1.** `a^-1 b a = b^2` gives `a^-n b a^n = b^(2^n)`, and `b^-1 c b = c^2` gives
  `b^-k c b^k = c^(2^k)`. So `b^-1 c_n b = a^n (a^-n b^-1 a^n) c (a^-n b a^n) a^-n
  = a^n b^(-2^n) c b^(2^n) a^-n = c_n^(2^(2^n))`.
- **Where the elements sit.** `b = b^-1 a^-1 b a = [b, a]` and `c = c^-1 b^-1 c b = [c, b]` are
  commutators, so `b, c ∈ H' ⊆ L`. Then `c ∈ ⟨b, c⟩' ⊆ L'`, and every `c_n ∈ L'`, since `L'` is normal in
  `H`.
- **One finite stage.** Fix `N`. Since `L' = ⋃ F_i'` is directed, some `F = F_i` contains `b` and has
  `c_0, …, c_N ∈ F'`.
- **Counting eigenvalues.** Let `M = F' ⊗ Q` and `R = Q[F^ab]`, a Noetherian ring. `b` acts on `M` through
  its image `β ∈ F^ab`. The images `v_n` of the `c_n` are nonzero, since `c_n` has infinite order, and
  `β^-1 v_n = λ_n v_n` with `λ_n = 2^(2^n)`. The annihilator of `v_n` contains `β - λ_n^-1`, so some
  associated prime `P_n ∈ Ass(M)` contains it. If `P_n = P_m` with `n ≠ m`, then `P_n` contains the unit
  `λ_n^-1 - λ_m^-1`, which is impossible. So `N + 1 <= |Ass(M)|`.
- **Conclusion.** `N` is arbitrary and `|Ass|` is bounded, a contradiction. ∎

## What this says about hosts

- **The canonical candidate is non-Noetherian on purpose.** In
  `M_1 = (⊕_(A/⟨b⟩) Z[1/2]) ⋊ BS(1,2)` of the source node, the lamps at the cosets `a^n ⟨b⟩` carry the
  eigenvalues `2^(2^n)` of `b`. The lamp module is induced from `⟨b⟩` and is not Noetherian over
  `Z[BS(1,2)]`.
- **Germ towers.** Ascending germ towers of height at most three
  (`zoom-tower-germ-groups-give-f-infinity-germ-extensions`) cannot hold a chain configuration.
- **Open.** Can an iterated ascending HNN tower over `Z`, of any height, contain a chain configuration?
  Height four is the first case not excluded here.

## Lesson for general BH

A chain configuration is a **spectral** object. One element must dilate infinitely many independent
directions, with eigenvalues `2^(2^n)`, which grow super-exponentially. Any host in which the relevant
abelian section is a Noetherian module has only finitely many dilation rates per element, and so is
excluded. This is why metabelian, linear and poly-ascending hosts fail at once, and why the candidate
`M_1` has a non-Noetherian lamp module. The positive search for hosts of `G_1`, `H4` and `BG` should
target groups whose abelian sections are induced modules over non-polycyclic groups. Examples are coset
lamplighters with twisted lamps, and germ groups with sparse defects, which is exactly the
non-faithful PL germ group of `scale-periodic-bs-chain-germ-representations-are-not-faithful`.

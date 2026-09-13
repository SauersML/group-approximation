---
rg: 2
id: edge-twist-extensions-of-triangle-colimits-moment-test
kind: claim
title: Edge-twisted central extensions of a triangle colimit split virtually exactly when a first-moment identity holds on the 2-cycles of some finite cover
distinct_from:
  persistent-degree-two-class-on-hyperbolic-group: that is the open existence target for an arbitrary persistent class on a residually finite hyperbolic group, and its Attempts record that the graph has no technique to control H^2 along the finite-index subgroup lattice; this supplies such a technique for one explicit family of classes on triangle colimits, and decides nothing by itself
  finite-central-extension-rf-iff-virtually-splits: that is the general virtual-splitting criterion; this makes the splitting test finite, linear and explicit for edge twists of triangles of finite groups
  simple-vertex-triangles-are-universal-for-triangle-vtf: that transfers finite quotients between a triangle and its simple-vertex amalgam; this studies central extensions of one triangle colimit by a cyclic group of prime order
---

**Setting.** `T` is a nonpositively curved triangle of finite groups with vertex groups
`A_1, A_2, A_3`, edge groups `E_12, E_13, E_23` and trivial face group. `Λ` is its
colimit, `p` is a prime and `C = F_p`. For a twist `c = (c_e)` with `c_e in Hom(E_e, C)`,
let `T_c` be the triangle with:
- vertex groups `A_v × C`;
- edge groups `E_e × C`, embedded into `A_i × C` by `(x,z) ↦ (x,z)` and into `A_j × C`
  (`i < j`) by `(x,z) ↦ (x, z + c_e(x))`;
- face group `C`.
Its colimit is `Λ_c`.

For a torsion-free finite-index normal subgroup `N` of `Λ`, put `Q = Λ/N` and
`M = F_p^Q`, with `Λ` acting through `Q` by left translation. The relevant space is

```text
Z_N = { λ in F_p[Q] : Σ_{q in E_e q_0} λ(q) = 0 for every right coset E_e q_0, all e }.
```

This is the space of cellular 2-cycles of the finite complex `N\X` with `F_p`
coefficients, after `q ↦ q^{-1}`. For `E_e = <x_e>` cyclic of order `p`, the moment
along edge type `e` is

```text
μ_e(λ) = Σ_{right cosets E_e q_0}  Σ_{k=0}^{p-1}  k · λ(x_e^k q_0)   in F_p.
```

It does not depend on the base points, because `λ` sums to zero on each coset.

**THEOREM (established; unreviewed).**

```text
(M1) Λ_c is an infinite hyperbolic central extension 1 -> C -> Λ_c -> Λ -> 1 when T is
     hyperbolic (T_c has the same links as T, so it is developable).
(M2) Moment test. Λ_c has a finite quotient that is injective on C and factors through
     C^Q ⋊ Q over Λ -> Q  iff
         c_12 μ_12(λ) + c_23 μ_23(λ)  =  c_13 μ_13(λ)     for all λ in Z_N.
(M3) If Λ is virtually torsion-free, Λ_c has a finite quotient injective on C iff (M2)
     holds for some torsion-free finite-index normal N.
(M4) Monotonicity. For N' <= N, the map pushing λ' forward along Q' -> Q sends Z_{N'}
     into Z_N and preserves every μ_e. So I_N = μ(Z_N) <= F_p^3 decreases, and stabilizes
     at some I_∞. The twist c splits virtually iff c is orthogonal to I_∞ under
     <c, m> = c_12 m_12 + c_23 m_23 - c_13 m_13.
(M5) Only p-covers matter. If [N : N'] is prime to p, then I_{N'} = I_N, by transfer.
(M6) If I_∞ != 0 for one hyperbolic virtually torsion-free triangle colimit Λ, then some
     hyperbolic group is not residually finite: either Λ is not, or Λ_c is not, for any
     c not orthogonal to I_∞ (`finite-central-extension-rf-iff-virtually-splits`).
```

**What it gives.**
- The persistent-class route to Gromov's question
  (`persistent-degree-two-class-on-hyperbolic-group`) becomes, for triangle colimits, a
  sequence of sparse linear-algebra problems over `F_p`, of size `|Q| × 3|Q|/p`, along the
  `p`-covers of one finite quotient.
- Vanishing of a twist class is certified by one finite computation.
- Persistence needs control over all `p`-covers, which is where theory has to enter.

**Remark (when all of `H^2` is twists).** Suppose every `A_v` has
`H^1(A_v;F_p) = H^2(A_v;F_p) = 0`, for instance a perfect group with Schur multiplier of
order prime to `p`, as for `A_7`, `A_8` and `p = 7`. Then the equivariant spectral
sequence of `Λ` acting on the development gives `H^2(Λ;F_p) ≅ ⊕_e Hom(E_e, F_p)`. So
every central extension of `Λ` by `F_p` is an edge twist, and the moment test covers the
whole of `H^2(Λ;F_p)`. The spectral-sequence identification is not re-derived in the
proof route and is not used by (M1)–(M6).

**Calibration.** For a tree of finite groups (no 2-cells) `Z_N = 0`, so every twist
splits virtually. That is consistent with virtually free groups being good.

Proof: `edge-twist-extensions-of-triangle-colimits-moment-test-proof`. Elementary; no
novelty is claimed for the lifting formalism.

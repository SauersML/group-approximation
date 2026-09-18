---
rg: 2
id: kazhdan-rational-relation-cover-reduction
kind: claim
title: A Kazhdan cover of a quotientless Kazhdan group gives a torsion-free quotientless Kazhdan group exactly when root powers stay non-torsion in the relation module
distinct_from:
  free-abelianized-cover-is-torsion-free: that cover is built over a free group, so it is automatically torsion-free but never Kazhdan; this builds the cover over a Kazhdan group, so it is Kazhdan, and torsion-freeness becomes the criterion (RLT), which can fail.
  abelianized-cover-commutator-is-finitely-generated-perfect: that commutator core comes from a free cover and has no property (T); here the core is Kazhdan and has no nontrivial finite quotient at all.
  steinberg-images-die-in-torsion-free-groups: that forbids Steinberg images as subgroups or quotients of torsion-free groups; here the elementary group is only a quotient of the torsion-free group, which is allowed, and (RE) is the corresponding obstruction for covers.
  lef-kazhdan-group-without-finite-quotients-exists: that group has torsion; this is the machine that turns such a group into torsion-free candidates, and it states the exact obstruction.
  torsion-free-sofic-extrinsic-kazhdan-defect-kernel: that is the full kernel problem with the compression condition (EK1); this handles only the necessary intrinsic clauses (torsion-free, Kazhdan, no finite quotient, sofic).
artifacts:
  - research/kazhdan-rational-relation-cover-reduction-proof.md
  - research/relation-cover-rational-lifting-over-quotientless-kazhdan.md
---

**ESTABLISHED.**

## Setting

- `Q` is a nontrivial Kazhdan group with no nontrivial finite quotient.
- `P` is a finitely generated Kazhdan group.
- `pi: P ->> Q` is a surjection with kernel `R`.

Set

```text
R_sat = preimage in R of tors(R^ab),   K = P/R_sat,   A = R/R_sat,
M = ZQ (x)_{ZP} I_P,                   V = M (x)_Z Q.              (RC1)
```

Here `I_P` is the augmentation ideal. `R_sat` is characteristic in `R`, hence
normal in `P`. So `1 -> A -> K -> Q -> 1` is exact, and `A` is a torsion-free
abelian `ZQ`-module.

## Statement

1. **Torsion criterion.** `K` is torsion-free if and only if

   ```text
   for every f in P such that pi(f) has prime order l:  f^l is not in R_sat.   (RLT)
   ```

   Equivalently, for every such `f`, with `C = <pi(f)>`, the class of `f^l`
   in the Tate group `H^0_hat(C; A) = A^C / N_C A` is nonzero. Every torsion
   element of `K` has the same order as its image in `Q`.

2. **Universality.** (RLT) holds if and only if `P` has some torsion-free
   quotient `P/N` with `N <= R` and `R/N` abelian. Every such quotient is a
   quotient of `K`.

3. **Quotientless Kazhdan core.**
   - `K` is Kazhdan.
   - Every finite quotient of `K` is abelian, and `K^ab` is finite.
   - `D = [K,K]` is a finite-index, finitely generated Kazhdan subgroup with no
     nontrivial finite quotient.
   - `D` maps onto `Q`, with abelian kernel `A cap D`; in particular `D` is
     nontrivial, because `Q` is perfect.
   - Under (RLT), `D` is torsion-free.

4. **Linear envelope.** `p -> (1 (x) (p-1), pi(p))` induces injective
   homomorphisms

   ```text
   P/[R,R]  ->  M semidirect Q,          K  ->  V semidirect Q.          (RC2)
   ```

   If `V` embeds as a `QQ`-module into a free module `QQ^m` (or into any
   module `(+)_Q W` induced from the trivial subgroup, with `W` countable),
   and `Q` is sofic, then `K` and `D` are sofic.

5. **Free covers are sofic.** If `P = F` is free of rank `n`, then `M = ZQ^n`.
   So the free abelianized cover `F/[R,R]` embeds in `Z^n wr Q`. It is sofic
   whenever `Q` is sofic, for every group `Q`.

6. **Root-element obstruction (RE).** Let `S` be a unital ring, `n >= 3`,
   `P <= EL_n(S)`, and `pi: P -> Q` with kernel `R`. Suppose there are pairwise
   distinct indices `i,j,k`, elements `u,a,b in S`, a prime `l` and an integer
   `m >= 1` such that:
   - `e_ij(u) in P`, and `pi(e_ij(u))` has order `l`;
   - `e_ik(a)` and `e_kj(b)` lie in `R`;
   - `ab = m l u`.

   Then (RLT) fails at `f = e_ij(u)`.

   **Corollary.** Let `S ->> T` be a ring surjection, with `T` infinite of prime
   characteristic `p`. Let `P` have finite index in `EL_n(S)`, `n >= 3`, and let
   `pi` be the restriction of `EL_n(S) -> EL_n(T)`. Then `K` has `p`-torsion.
   In particular, fix any ring surjection
   `Z<x_1,...,x_r> ->> LC(X,F_q) semidirect Z`. Then no finite-index subgroup
   of `EL_3(Z<x_1,...,x_r>)` satisfies (RLT) over
   `EL_3(LC(X,F_q) semidirect Z)` along the induced map.

## Consequence for the torsion-free kernel hole

Take `Q = EL_3(LC(X,F_q) semidirect Z)`
(`lef-kazhdan-group-without-finite-quotients-exists`: LEF, hence sofic,
Kazhdan, with no finite quotient). Suppose some finitely generated Kazhdan
cover `P ->> Q` satisfies (RLT), and `V` embeds in an induced module. Then `D`
is a nontrivial torsion-free, sofic, Kazhdan group with no nontrivial finite
quotient.

Such a group is required as the kernel in
`torsion-free-sofic-extrinsic-kazhdan-defect-kernel`, before (EK1) is
addressed. No such group is presently known. Titz--Witzel lattices are
torsion-free, simple and Kazhdan, but their soficity is open. So the intrinsic
half of the hole splits into two prerequisites that can each fail on their own:
(RLT) for some Kazhdan cover, and soficity of `K`. These are recorded as
`relation-cover-rational-lifting-over-quotientless-kazhdan`. The statement
(RE) kills the natural linear covers, and item 2 shows nothing is lost by
passing to the canonical `K`.

This claim says nothing about (EK1) or about MF radicals.

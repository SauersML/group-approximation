---
rg: 2
id: elementary-amenable-finite-hirsch-length-bvc-groups-are-vc-proof
kind: route
title: Bounded finite subgroups kill the locally finite radical, leaving a virtually solvable group
target: elementary-amenable-finite-hirsch-length-bvc-groups-are-vc
requires:
  - hillman-linnell-finite-hirsch-length-theorem
  - bvc-groups-have-bounded-finite-subgroups
  - virtually-solvable-bvc-groups-are-virtually-cyclic
---

Let `G` be elementary amenable of finite Hirsch length, with property BVC.

1. By `hillman-linnell-finite-hirsch-length-theorem`, `G` has a locally finite normal subgroup
   `N` with `G/N` virtually solvable.
2. By `bvc-groups-have-bounded-finite-subgroups`, every finite subgroup of `G` has order at
   most some `c`.
3. **N is finite.** Choose a finite subgroup `F <= N` of maximal order (orders are bounded by
   `c`). For `x in N`, the finitely generated subgroup `<F, x>` of the locally finite group `N`
   is finite. It contains `F`, so by maximality `<F, x> = F` and `x in F`. Hence `N = F`.
4. **G is virtually solvable.** Let `S <= G` contain `N` with `[G:S]` finite and `S/N`
   solvable. The centralizer `C = C_S(N)` has index at most `|Aut(N)|` in `S`, so finite index
   in `G`. `C ∩ N <= Z(N)` is abelian, and `C/(C ∩ N) ≅ CN/N <= S/N` is solvable. So `C` is
   solvable.
5. By `virtually-solvable-bvc-groups-are-virtually-cyclic`, `G` is virtually cyclic.

Model tests:

- Houghton's groups `H_n` (`n >= 3`) are elementary amenable of Hirsch length `n - 1`, with the
  infinite locally finite normal subgroup `FSym(N)`; step 3 rules out BVC, consistent with
  `H_1(H_n)` having rank `n - 1 >= 2` (1607.03790, Corollary 1.15).
- A virtually cyclic group passes every step.

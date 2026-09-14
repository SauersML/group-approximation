---
rg: 2
id: recursive-residually-finite-non-exact-groups-exist-proof
kind: route
title: Osajda's residually finite non-exact construction is effective on a recursive labelled input
target: recursive-residually-finite-non-exact-groups-exist
requires: [residually-finite-non-exact-groups-exist]
artifacts:
  - research/artifacts/sk-free-1-exactness-2026-09-13-part2.md
---

Derivation; verbatim sources in the artifact §2.
1. **Recursive input.** Osajda, arXiv:1406.5015, Remark r:recurs (l.695–705): the labellings of §s:LLL and §s:mLLL extend step by step by brute force. So for a recursive graph sequence (finite linear-group expanders) the small cancellation labelling and presentation are recursive. This supplies the D-regular input with the stronger small cancellation property required by arXiv:1703.03791 l.313–315.
2. **Effective inductive step** (1703.03791 l.346–412), each a terminating search:
   - H_i from cycle words of the finite graph Θ_{i+1};
   - K_i as the intersection of kernels of finitely many maps to finite groups;
   - a finite normal cover Θ̄_{i+1} whose cycle words map trivially to each F_j (decidable check; it exists by the paper);
   - the Z_2-homology cover Θ̂_{i+1};
   - φ_{i+1}, found by searching finite groups F and maps S → F that satisfy the finitely many relators of G_{i+1} and are nontrivial on the (i+1)-ball. The ball is computable by McKinsey's algorithm, since G_{i+1} is finitely presented and residually finite (Wise–Agol, as quoted at l.395–396). The search halts because the map exists.

   Conditions (A_{i+1}) and (B_{i+1}) are proved in the paper and involve no choice.
3. **Conclusion.** i ↦ Θ̂_i is recursive, so the relators of G = ⟨S | Θ̂_1, Θ̂_2, …⟩ form a recursively enumerable set. The paper's proof (l.420–437) shows G is residually finite and non-exact.

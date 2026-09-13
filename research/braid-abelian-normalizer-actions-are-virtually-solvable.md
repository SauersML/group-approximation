---
rg: 2
id: braid-abelian-normalizer-actions-are-virtually-solvable
kind: claim
title: In a braid group, normalizers act on free abelian subgroups through virtually solvable groups
invalidates:
  - braid-no-haagerup-via-burger-pair
artifacts:
  - research/artifacts/zp-braid-haagerup-fences-2026-09-13-part2.md
---

Let `A ≤ B_n` be free abelian of finite rank `k`, and let `Γ ≤ B_n` normalize `A`. The conjugation action
`Γ → GL(A) ≅ GL_k(Z)` has virtually solvable image.

In particular, no subgroup `A Γ ≤ B_n` with `A ≅ Z^2` normal has `Γ` acting on `A` through a non-amenable
subgroup of `SL_2(Z)`. So the Burger-pair obstruction to the Haagerup property (relative property (T) for
`(Z^2 ⋊ Γ, Z^2)`) cannot occur in braid groups. This kills the route `braid-no-haagerup-via-burger-pair`.

Proposition E of `research/artifacts/zp-braid-haagerup-fences-2026-09-13-part2.md`:

- `P_n` is bi-orderable (Kim–Rolfsen, via the Magnus order and pure braid automorphisms);
- a group order on `Z^k` preserved by a group `Λ` forces `Λ` to preserve the flag of convex subgroups and to
  act abelianly on each archimedean piece (Hölder), so the image is solvable;
- pass to `Γ ∩ P_n` and `A ∩ P_n`.

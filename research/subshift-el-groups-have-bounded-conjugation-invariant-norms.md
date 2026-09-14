---
rg: 2
id: subshift-el-groups-have-bounded-conjugation-invariant-norms
kind: claim
title: Open - is every conjugation-invariant norm on EL_3(LC(X,F_2)⋊Z) bounded, i.e. does each nontrivial element normally generate the group in boundedly many steps?
artifacts:
  - research/artifacts/sk-free-6-normal-generation-2026-09-13-part1.md
---

**OPEN.** Let `X` be an infinite minimal subshift and `G = EL_3(LC(X,F_2) ⋊ Z)`. Is `G` bounded in the sense of Burago–Ivanov–Polterovich? Equivalently (by `subshift-el-root-elements-boundedly-normally-generated`): is the conjugation-invariant root length `λ^c` bounded on `G`, or is `cw(g) < ∞` for every `g ≠ e`?

The lower bound `cw(e_12(χ_V)) ≥ 1/inf_μ μ(V)` (`subshift-el-rank-lengths-force-non-uniform-simplicity`) shows that uniform simplicity fails. So a positive answer is the strongest possible normal generation statement.

## Attempts
- **Cut lemma (part 1, §4; sketch).** Take `h` of propagation `w` and Kakutani–Rokhlin cuts with heights `≫ w`.
  - Every element of `G` has index 0: root elements are unipotent modulo finite rank, over `F_2`.
  - So the kernel and cokernel of each block compression are localized at the block ends, with index 0 at each end.
  - End-by-end corrections give `H_1 ∈ GL_3(A_Y) = EL_3(A_Y)` over the locally matricial orbit-breaking subalgebra. By block Gauss reduction and Thompson's commutator theorem, `H_1` is a product of at most 28 root elements.
  - Then `h = H_1(I+Y)(I+pXp)`, where `I+Y` is a Peirce transvection (at most 18 root elements, using `[e_ik(y), e_ki(p)] = I + yE_ii`), and `p = χ_W` for the band `W` around the cuts.
- **Where it dies.** The remainder `I + pXp` is a degree-≤1 element over the induced system on `W`, because inverses of corrected compressions wrap around blocks.
  - Example: `diag(u,u^{-1})` leaves `diag(u_W,u_W^{-1})`, which is 6 root elements. In general, bounded root length for degree-1 remainders is unproved.
  - Iterating the cut lemma does not terminate.
- **Via stable rank one.** If `sr(R) = 1`, `GL_3(R) = (≤ 10 root elements)·diag(1,1,GL_1(R))`, and the question reduces to bounded root length of `diag(1,1,v)` for units `v` of index 0.
  - `sr(R) = 1` is open (`minimal-cantor-crossed-product-has-stable-rank-at-most-two`). For the exchange ring `R` it is equivalent to internal cancellation (Yu 1995, recalled), which would follow from `V(R) ≅ K^0(X,T)^+`.
- **Bounded cohomology** (`subshift-el-groups-vanishing-l2-betti-and-bounded-cohomology`) covers mixing coefficients only. Boundedness would force all homogeneous quasimorphisms to vanish, which property (T) alone does not give.

---
rg: 2
id: sl3z-contains-cd2-euler-positive-fibered-subgroup
kind: claim
title: SL_3(Z) contains a two-dimensional subgroup with nonzero Euler characteristic fibring over Z with finitely generated kernel
---

There is a subgroup `G <= SL_3(Z)` of type FP with `cd G = 2`,
`chi(G) = sum_k (-1)^k dim_Q H_k(G; Q) != 0`, and an epimorphism
`phi: G -> Z` whose kernel is finitely generated.

By `sl3z-incoherent-via-euler-fibered-subgroup` its kernel is then finitely
generated and not finitely presented.

**Necessary conditions on any such `G`** (from the established region):

- `ker phi` is a finitely generated, not finitely presented subgroup, so it is
  Zariski dense (`non-zariski-dense-subgroups-of-sl3z-are-coherent`). Hence `G` is
  Zariski dense.
- `G` has infinite index. Finite-index subgroups of `SL_3(Z)` have property
  (T) (Kazhdan), so they have finite abelianization and no epimorphism onto
  `Z`.
- `G` contains no `Z x F_2` (`sl3z-products-of-infinite-subgroups-are-polycyclic`).
- `G` has no infinite normal solvable subgroup. Its Zariski closure would be
  a normal solvable subgroup of `SL_3`, hence finite.
- The centralizer of the Zariski-dense kernel `N` is central in `SL_3`, so it
  is trivial in `SL_3(Z)`. So `G` acts faithfully on `N` by conjugation,
  `G/N` embeds in `Out(N)`, and the monodromy has infinite order in `Out(N)`.

## Attempts

- 2026-09-13 (z3-04-sl3z-incoherent): free-by-free thin subgroups
  `F_n x| F_m` with `n, m >= 2` have `cd = 2` and `chi = (n-1)(m-1) > 0`.
  - They need a character nonzero on the fibre with finitely generated
    kernel. Kropholler–Walsh study such fibrations of free-by-free groups; the
    exact statements were not re-verified.
  - Inside `SL_3(Z)` the normal `F_n` must be Zariski dense, and `F_m` must
    embed in the stabilizer in `Out(F_n)` of the conjugacy class of the
    inclusion `F_n -> SL_3(C)`. That forces the inclusion out of every region
    of the character variety where `Out(F_n)` acts properly. Lead to test:
    properness of the `Out(F_n)` action on projective Anosov representations,
    not re-verified.
- 2026-09-17 (c-sl3z, compute-scout): the Long–Reid family as a source of
  `G`. Setting: D. D. Long and A. W. Reid, *Small Subgroups of SL(3, Z)*, Exp.
  Math. 20(4) (2011) 412–425. It gives `ρ_k: Γ -> SL_3(Z)` on the figure-eight
  knot group `Γ = <x, y, z | zxz^-1 = xy, zyz^-1 = yxy>`, with fibre
  `F = <x, y>`. Put `G = ρ_k(Γ)` and `N = ρ_k(F)`. `G/N` is cyclic, generated
  by the image of `Z_k`. The claim stays OPEN.
  - **Decomposition** (fixed `k`; argued here, not a node). The route succeeds
    iff all four hold:
    - (R2) no power of `Z_k` lies in `N`. Then `G/N ≅ Z`, `N` is finitely
      generated, and `K = ker ρ_k ⊂ F`. R2 implies thinness (R1): finite index
      would give property (T), hence finite abelianization, forcing
      `Z_k^n ∈ N`. This is Long–Reid Question 4.3.
    - (R2') `ρ_k|F` is not injective. Otherwise `K ⊂ F` and `K ∩ F = 1` give
      `K = 1`, so `G ≅ Γ`, which has `chi = 0`. So any proof of thinness via
      ping-pong or freeness of `N` kills the route rather than helping it.
    - (R3) `G` is of type FP with `cd 2`.
    - (R4) `chi(G) = b_2(G) = dim_Q (K/[K, Γ]) ⊗ Q >= 1`. This uses `b_1(G) = 1`,
      `H_2(Γ; Q) = 0` and the Hopf five-term sequence for `1 -> K -> Γ -> G -> 1`.
  - **Congruence quotients cannot certify R2** (argued via strong
    approximation, Weisfeiler / Matthews–Vaserstein–Weisfeiler; not cited
    verbatim). `N` is Zariski dense (Long–Reid Thm 1.3), so its closure in
    `SL_3(Ẑ)` is open. So some fixed power `Z_k^n` lies in every congruence
    image of `N`. Every finite-quotient test of R2 is inconclusive; R2 needs an
    infinite-index certificate.
  - **Reduction of the parameter** (new established claim
    `long-reid-specializations-k-and-minus-one-minus-k-are-conjugate`).
    `ρ_{-1-k}` and `ρ_k` have `SL_3(Z)`-conjugate images, fibre to fibre, and
    the conjugation twists `F` by an automorphism. So R1, R2, R2', R3 and R4
    are shared by `k` and `-1-k`. Combined with Long–Reid Thm 4.1 (finite
    index for `k = 0, 2, 3, 4, 5`), the only integer candidates are `k = 1`
    and `k >= 6`. Long–Reid Remark 4.2 suggests `ρ_1(Γ)` is virtually free,
    which would contradict R3.
  - **Census for finite-index certificates at `k >= 6`** (negative results;
    exact integer arithmetic via mod `2^61-1` hashing, so no true hit is
    missed). All files are in `experiments/sl3z-long-reid-census-2026-09-17/`.
    - Directional meet-in-the-middle (`mitm_tv.c`, `run_dirs.py`):
      - For each primitive direction `v` with `max |v_i| <= 3` (145 directions
        up to sign), it finds every reduced word of length `<= 28` in
        `X_k, Y_k` equal to `I + v u^T`.
      - Transvections found: 2 of 145 directions for `k = 4` and 4 of 145 for
        `k = 5`, with explicit words `a b^-1` in `dirs_k4_m14_R3.out` and
        `dirs_k5_m14_R3.out`. For `k = 5`, `XYxYXXYxYX` (length 10) is a
        transvection in direction `(1, 3, 1)`.
      - For `k = 6, 7`: none in any of the 145 directions, and no relation of
        length `<= 28` (`dirs_k6_m14_R3.out`, `dirs_k7_m14_R3.out`).
    - Palindromic census (`census.c`, `run_pal.sh`, `pal_half18_k6-16.out`):
      words `a φ(a)` with `|a| = 18` and 7 twists `φ`, for `k = 6..16`. It found
      no relation, torsion, eigenvalue `-1` element or unipotent element. The
      calibration run `pal_calib_k0-5.out` (`|a| = 13`) finds hits for `k = 5`
      (12 transvections, 92 eigenvalue `-1` elements) but none for `k = 4`.
    - These nulls are weak evidence of thinness only. At the same bounds even
      finite-index `k = 4` has transvections in just 2 of 145 directions, and
      Long–Reid report the `k >= 6` index question as very difficult.
  - **Where it stands.**
    - No certificate of R2 is known for any `k`, and none can be congruence.
    - R2' and R4 are statements about `ker ρ_k`, which the search above sees
      only through relations; none of length `<= 28` exist for `k = 6, 7`.
    - Next test: decide R2 for `k = 6` by an infinite-index invariant that
      separates `<Z_k>` from `N`. Certificates that go through freeness of `N`
      (ping-pong on `X_k, Y_k`) would prove the opposite of R2', so they must
      be avoided.
- No candidate is known to exist; no obstruction to existence is known.

---
rg: 2
id: malcev-root-steps-put-commutator-root-one-relators-in-h-proof
kind: route
title: Taking k-th roots of commutators in the Mal'cev completion of a free nilpotent group of Fibonacci class keeps every edge element of a commutator-root segment alive, so the edge-injective lemma climbs it; when the middle letter is the root instead, torsion-freeness and abelian layers kill every interior letter
target: malcev-root-steps-put-commutator-root-one-relators-in-h
requires:
  - edge-injective-quotients-give-hughes-free-division-rings
  - vertex-injective-quotients-give-hughes-free-division-rings
  - magnus-segment-steps-put-one-relator-groups-in-h
---

## Inputs

- **(C)** `𝓗` is closed under subgroups, extensions and directed unions. It contains free groups and every
  locally indicable amenable group, in particular every finitely generated torsion-free nilpotent group and
  every poly-`Z` group. Item 1 of [[vertex-injective-quotients-give-hughes-free-division-rings]].
- **(E)** The edge-injective quotient lemma, item 1 of [[edge-injective-quotients-give-hughes-free-division-rings]]:
  a graph of groups with vertex groups in `𝓗` is in `𝓗` if it has a homomorphism to a group in `𝓗` that is
  injective on every edge group.
- **(M)** Magnus–Moldavanskii, as in [[magnus-segment-steps-put-one-relator-groups-in-h-proof]]:
  - the window `W_{n-1} = <a_n, a_{n+1}>` is free of rank 2 in `S_[0,n-1]`;
  - `S_[0,n] = S_[0,n-1] *_{W_{n-1}} B_n` with `B_n = <a_n, a_{n+1}, a_{n+2} | r'_n>`;
  - `N = ker(G -> Z)` is the directed union of the `S_[p,n] ≅ S_[0,n-p]`, and `G = N ⋊ Z`.
- **(L)** Free Lie algebras over `Q`:
  - Shirshov–Witt: every subalgebra of a free Lie algebra is free. So `[x, y] = 0` only for linearly dependent
    `x, y`. (If `[x, y] = 0`, the subalgebra `<x, y>` is free and abelian, so it has rank at most 1 and is
    one-dimensional.)
  - Mal'cev: for `c ≥ 1` let `L = L(X_0, X_1)`, graded by degree, and `L^{≤c} = L / L_{>c}`. Then `L^{≤c}`
    with the Baker–Campbell–Hausdorff product is a torsion-free, uniquely divisible nilpotent group `𝔑_c`, with
    `log(g^{1/k}) = (1/k) log g`.
  - For a word `u(x, y)` with exponent sums `(p, q)`: `log u(e^x, e^y) = p x + q y + c(u) [x, y] + (Lie words
    of length ≥ 3 in x, y)`. Here `c(u)` is the image of `u` in `γ_2 F / γ_3 F = Z`. When `p = q = 0`, `c(u)`
    is the signed area of the lattice path of `u` (the function `area` of `nilpotent_root_certify.py`),
    up to one global sign.

## Proof of item 1 (commutator-root step)

Write `r' = a_2^k u(a_0, a_1)^{-1}` cyclically, with `|k| ≥ 2`, exponent sums of `u` equal to `(0, 0)`, and
`c := c(u) ≠ 0`. Then `u ≠ 1`, so `u_n := u(a_n, a_{n+1}) ≠ 1` in the free window `W_{n-1}`.

1. **The step is a cyclic amalgam.** `B_n = W_{n-1} *_{u_n = a_{n+2}^k} <a_{n+2}>`. By (M),
   `S_[0,n] = S_[0,n-1] *_{<u_n> = <a_{n+2}^k>} <a_{n+2}>`. The edge group is infinite cyclic and the vertex
   groups are `S_[0,n-1]` and `Z`.
2. **The target.** Fix `n` and let `d_0 = d_1 = 1` and `d_{j+2} = d_j + d_{j+1}`, so the `d_j` are Fibonacci
   numbers. Take `c_n := d_{n+2}` and define `φ: S_[0,n] -> 𝔑_{c_n}` by:
   - `a_0 ↦ e^{X_0}` and `a_1 ↦ e^{X_1}`;
   - recursively, `a_{j+2} ↦ φ(u_j)^{1/k}`, the unique `k`-th root.

   The only relations of `S_[0,n]` are `a_{j+2}^k = u_j` for `0 ≤ j ≤ n`, and they hold by construction.
   The image is a finitely generated subgroup of a torsion-free nilpotent group, so it lies in `𝓗` by (C).
3. **Leading terms.** Put `ℓ_j = log φ(a_j)`. We claim, by induction, that `ℓ_j = L_j + (degree > d_j)`
   with `L_j ∈ L` homogeneous of degree `d_j` and `L_j ≠ 0`.
   - Base: `L_0 = X_0` and `L_1 = X_1`.
   - Step: by (L), with `x = ℓ_j` and `y = ℓ_{j+1}`,
     `log φ(u_j) = c [L_j, L_{j+1}] + (degree > d_j + d_{j+1})`. Terms of length `≥ 3` in `x, y` have degree at
     least `2 min(d_j, d_{j+1}) + max(d_j, d_{j+1}) > d_j + d_{j+1}`. Hence `L_{j+2} = (c/k) [L_j, L_{j+1}]`.
   - This is nonzero: `L_0, L_1` are independent, and for `j ≥ 1` we have `d_j < d_{j+1}`, so `L_j, L_{j+1}` are
     nonzero homogeneous elements of different degrees, hence independent. By Shirshov–Witt their bracket is
     nonzero.
4. **The edge survives.** `log φ(u_n) = c [L_n, L_{n+1}] + …` has a nonzero component in degree
   `d_{n+2} = c_n`, so `φ(u_n) ≠ 1`. Since the target is torsion-free, `φ` is injective on `<u_n>`.
5. **Climb.** By induction `S_[0,n-1] ∈ 𝓗`, starting from the free group `S_[0,-1] = F(a_0, a_1)`. By steps
   1–4 and (E), `S_[0,n] ∈ 𝓗`. So `N ∈ 𝓗` (directed union) and `G ∈ 𝓗` (extension by `Z`). The bottom version
   is the same after reversing the indices. ∎

*Why the landed rules miss it.* Every map `S_[0,n-1] -> Z` kills the commutator `u_n`, so no abelian target and
no retraction onto the edge group exists. That rules out root, root-tower, rule 1 and rule R. The weights in step 3
satisfy `w_{j+2} = w_j + w_{j+1}`, which is consistent: nilpotent targets work, but only with class growing like
Fibonacci numbers. The weight lemma of [[retract-segment-steps-put-perfect-kernel-one-relator-groups-in-h]]
says no bounded-class target exists, and none is needed.

## Proof of item 3 (the frontier: root in the middle)

Hypotheses: `r' ∈ F(a_0, a_1, a_2)` has exponent vector `(0, ε, 0)` with `ε ≠ 0` **(H1)**, and `r'(1, y, z)` and
`r'(x, y, 1)` are conjugate in the free group to nonzero powers of `y` **(H2)**. Let `S = S_[0,n]` with letters
`a_0, …, a_N`, `N = n + 2`, and interior letters `a_1, …, a_{N-1}`. Let `ψ: S -> M` be a homomorphism.

1. **(Propagation)** If `M` is torsion-free and `ψ(a_j) = 1` for some `0 ≤ j ≤ N`, then `ψ` kills every interior
   letter.
   - If `j ≥ 2`, relation `j - 2` involves `a_{j-2}, a_{j-1}, a_j`, and its top letter is trivial. By (H2),
     `ψ(a_{j-1})^m = 1` with `m ≠ 0`, so `ψ(a_{j-1}) = 1`.
   - If `j ≤ N - 2`, relation `j` has trivial bottom letter, so `ψ(a_{j+1}) = 1` in the same way.
   - Iterating in both directions kills `a_1, …, a_{N-1}`.
2. **(Abelian layers)** Suppose `M` has a series `M = M_0 ⊵ … ⊵ M_d = 1` of normal subgroups of `M` with
   torsion-free abelian factors, and `N ≥ 4`. Then `ψ` kills every interior letter. Induction on `d`:
   - Put `A = M_{d-1}`. Then `M/A` has such a series of length `d - 1` and is torsion-free.
   - By induction (trivially when `d = 1`), every interior letter maps into `A`.
   - Relation 1 involves `a_1, a_2, a_3`, all interior because `N ≥ 4`, so all of them lie in the abelian group
     `A`. There, by (H1), relation 1 reads `ε ψ(a_2) = 0`, so `ψ(a_2) = 1`.
   - Step 1 finishes.
3. **(Residual version)** If `M` is residually such a group, apply step 2 in each quotient. This covers
   residually torsion-free nilpotent groups: the upper central series of a torsion-free nilpotent group has
   torsion-free factors. It also covers free groups, free solvable groups, and torsion-free
   abelian-by-(poly-torsion-free-abelian) groups built with normal terms, such as `Z^k ⋊ Z`, Sol lattices and the
   Klein bottle group.
4. **(Consequences for the steps)** The step `S_[0,n] ⊂ S_[0,n+1]` is an HNN extension along a cyclic edge
   group generated by a word in `a_{n+1}, a_{n+2}` (twist (T) of the retract route, the top letter occurring
   twice).
   - For `n ≥ 1` both letters are interior in `S_[0,n+1]`, which has `N = n + 3 ≥ 4`. So by step 3 no
     homomorphism from `S_[0,n+1]` to a residually-𝒮 group is injective on the edge group.
   - The lower-central weight argument gives the RTFN part already for `n ≥ 0` when `N = 3`. As in item 3 of
     the retract route: `ψ(y)^ε ≡ ψ(r'(x, 1, z))^{-1} mod D_{q+1}` and `r'(x, 1, z) ∈ [<<x>>, <<z>>]`. This gives
     `w(a_{j+1}) ≥ w(a_j) + w(a_{j+2})`, and two consecutive relations force infinite weight.
   - Retractions onto the edge group are maps to `Z` with value `±1`. `Hom(S_[0,n], Z)` is the lattice
     `Λ_n = {(0, w)}` on the window (chain `[[1,0],[0,1]] ⊃ [[0,1]]`, printed by `probe.py`), and on it the
     edge functionals take only even values or `0`. So rule R fails, as the census confirms for twists of length
     at most 2.
5. **(Sharpness at the first step)** For `N = 3` step 2 does not apply. In all 18 frontier words the top letter
   occurs exactly twice, so `r' = a_2^{-1} x a_2 y` cyclically. `S_[0,0]` is the HNN extension of `F(a_0, a_1)`
   along `<x_0> -> <y_0^{-1}>`, and `S_[0,1]` is the HNN extension of `S_[0,0]` along `<x_1> -> <y_1^{-1}>`.
   `frontier_check.py` finds, for each word, a map `φ: S_[0,1] -> Z^2 ⋊_B Z` with `φ(x_0), φ(y_0), φ(x_1), φ(y_1)`
   all nontrivial. Here `B = [[3,4],[2,3]]` (a Sol lattice, 8 words) or `B = -I` (10 words), written as pairs
   `(v, n)` with `(v, n)(w, m) = (v + B^n w, n + m)`. Both targets are poly-`Z` and torsion-free, so they lie in
   `𝓗`, and a nontrivial image of a cyclic edge group means the map is injective on it.
   - Example `r' = X0X1X2X1x0X1x2x1`, with `x = X1x0X1` and `y = x1X0X1`. Take `B = [[3,4],[2,3]]`, `a_0 = t^{-1}`,
     `a_3 = t` where `t = (0, 1)`, `a_1 = (v_1, 0)` and `a_2 = (v_2, 0)`.
     - Relation 0 reads `B(2v_1 + v_2) = v_2`, and relation 1 reads `2v_2 = (I - B)v_1`.
     - Since `B + B^{-1} = 6I`, we have `(B^{-1} - I)(I - B) = 4I`, so the second equation implies the first.
       `v_1 = (1,0)` and `v_2 = (-1,-1)` solve both.
     - The edge images: `x_0` and `y_0` have `t`-exponent `∓1`, `φ(x_1) = (v_1 - 2v_2, 0) = ((3,2), 0)` and
       `φ(y_1) = (-v_1, 0)`. All four are nontrivial.
   - By (E) twice, `S_[0,1] ∈ 𝓗` for all 18. So an amenable target that is not residually nilpotent climbs the
     first two steps, and by step 4 no residually-𝒮 target climbs any later one. ∎

---
rg: 2
id: fw-eventually-similar-virtual-embedding-proof
kind: route
title: Cone markings modulo the local groupoid form a commensurated set, and a transfixed copy gives finitely many pieces with coordinates in vertex groups
target: fw-subgroups-of-eventually-similar-groups-virtually-embed
requires: []
artifacts:
  - research/artifacts/bh-rational-similarity-hosts-2026-09-12.md
---

Notation as in the target claim. Every vertex has out-degree at least two, so
two paths give the same cone only if they are equal, `C_(z') ⊆ C_w` with
`C_(z') != C_w` holds only if `z'` extends `w`, and a cone of small diameter
has a long path. The argument follows
`kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf-proof` with the self-similar
group replaced by the groupoid `H`.

## 1. The marking set

An **H-piece map** is an injective map `phi: C_s -> X` with a finite partition
of `C_s` into cones `C_(w_1),...,C_(w_m)` such that `phi(C_(w_j)) = C_(y_j)` and
`m_j = beta_(y_j)^-1 o phi o beta_(w_j)` lies in `H`. Its class is
`[phi] = {phi o n : n in H with codomain C_s}`. Since `H` is a groupoid this is
an equivalence relation, and `im[phi] = phi(C_s)` is well defined.

**Refinement.** For `n: C_(s') -> C_s` in `H`, the map `phi o n` is again an
H-piece map.
- `n` is uniformly continuous, and so is `n^-1`. Choose `E >= D_n` such that for
  `|z| >= E` the cone `n(C_z) = C_(z')` lies strictly inside some `C_(w_j)`, and
  `z' = w_j z''` with `|z''| >= max_j D_(m_j)`.
- Put `n_z = beta_(z')^-1 o n o beta_z`, in `H`. Then
  `phi o n o beta_z = beta_(y_j) o m_j o beta_(z'') o n_z`, and
  `m_j o beta_(z'') = beta_(z''') o m'` with `m'` in `H` because
  `|z''| >= D_(m_j)`.
- So `phi o n o beta_z = beta_(y_j z''') o (m' o n_z)`, and the cones `C_z` with
  `|z| = E` partition `C_(s')`.

**The action.** For `f` in `G` put `f.[phi] = [f o phi]`.
- `f o phi` is an H-piece map. Refine the pieces of `phi` to `C_(w_j z)` with `|z|`
  so large that `phi(C_(w_j z)) = C_(y_j z''')` with `|y_j z'''| >= D_f`, as in
  the refinement step. Then `f o beta_(y_j z''') = beta_v o n_f` with `n_f` in `H`.
- `f o (phi o n) = (f o phi) o n`, so the class is well defined, and
  `(f f').[phi] = f.(f'.[phi])`.
- `im(f.[phi]) = f(im[phi])`.

## 2. The cone markings are commensurated

Let `M = {[beta_u] : u a finite path from a root}`. Distinct paths give distinct
images, so distinct classes.

- If `|u| >= D_f`, then `f o beta_u = beta_v o n` with `n` in `H`, so
  `f.[beta_u] = [beta_v]` lies in `M`.
- There are finitely many paths from the finitely many roots of length below
  `D_f`.

So `f M \ M` is finite, the same holds for `f^-1`, and `M \ f M = f(f^-1 M \ M)` is
finite. Hence `M` is a commensurated subset of the `G`-set `S` of classes, and
of `S` as a `K`-set.

## 3. Property FW transfixes M

By FW there is a `K`-invariant `M' ⊆ S` with `M Δ M'` finite. For property (T),
this is the Delorme--Guichardet step of the source proof: (T) gives (FH), the
cocycle `g -> 1_(gM) - 1_M` in real `l^2(S)` is a coboundary `xi - pi(g) xi`, and
`M' = {s : 1_M(s) + xi(s) > 1/2}` differs from `M` inside the finite set where
`|xi| >= 1/2`.

## 4. A finite invariant cover by marked pieces

Choose `N` with `[beta_u]` in `M'` for every `|u| >= N`. Let `I` be the set of
images of classes in `M'`, and `P` the set of classes in `M'` whose image is
maximal in `I` for inclusion.

- **`K` permutes `P`.** `K` preserves `M'`, carries images to images, and
  preserves inclusion.
- **`P` is finite.**
  - A cone `C_u` with `|u| > N` lies strictly inside its length-`N` prefix cone,
    which is in `I`, so it is not maximal.
  - So a maximal image is `C_u` with `|u| <= N`, or the image of one of the
    finitely many classes of `M' \ M`. Each such set is the image of finitely
    many classes of `M'`: one class `[beta_u]`, plus classes of `M' \ M`.
- **The images of `P` cover `X`.** Each point lies in a cone `C_u` with `|u| = N`,
  and `C_u` is in `I`. The members of `I` containing `C_u` are prefix cones of
  `u` and images of classes of `M' \ M`, finitely many. A maximal one among them
  is maximal in `I`.

## 5. The embedding

Let `K_0` be the kernel of the permutation action of `K` on `P`; it has finite
index. Fix a representative `phi_p: C_(s(p)) -> X` of each class `p` in `P`.

- For `g` in `K_0`, `g.[phi_p] = [phi_p]` means `g o phi_p = phi_p o rho_p(g)` for
  some `rho_p(g)` in `H` with domain and codomain `C_(s(p))`, that is, in the
  vertex group `H_(s(p))`. It is unique because `phi_p` is injective.
- `rho_p` is a homomorphism: `(g g') o phi_p = g o phi_p o rho_p(g') = phi_p o rho_p(g) rho_p(g')`.
- If every `rho_p(g)` is trivial, `g` fixes every `im phi_p` pointwise. These cover
  `X`, so `g = 1`.

Hence `g -> (rho_p(g))_p` embeds `K_0` in the product of the `H_(s(p))`. This is
part 1.

## 6. Parts 2 and 3

- **Part 2.** If `H` is the groupoid of identity maps, each vertex group is
  trivial, so `K_0` is trivial and `K` is finite. This groupoid is eventually
  self-similar: the identity of `C_t` restricted to a cone `C_z` is `beta_z`, with
  restriction the identity of `C_(t(z))`.
- **Part 3.** Let every `n` in `H` send each cone `C_z` onto a cone of the same
  length.
  - An element of `H_s` then permutes the finite set of paths of length `k` from
    `s`, for every `k`. The kernel of this permutation action is normal of finite
    index.
  - An element in every kernel fixes every cone of every length from `s`, hence
    every point of `C_s`. So the kernels intersect trivially and `H_s` is
    residually finite.
  - Finite products and subgroups of residually finite groups are residually
    finite, so `K_0` is. A group with a residually finite subgroup of finite
    index is residually finite: separate elements outside `K_0` through
    `K/core(K_0)`, and elements of `K_0` through the finitely many conjugates of a
    finite-index normal subgroup of `K_0`.

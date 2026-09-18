---
rg: 2
id: type-f-benignness-is-embedding-of-the-double-proof
kind: route
title: "Proof: double the benign witness along Sigma and apply the amalgam normal form; conversely the second copy of K is a witness in any host of the double"
target: type-f-benignness-is-embedding-of-the-double
requires:
  - two-occurrence-realizability-is-type-f-benignness
---

Verification tier: proposed-established. These are elementary paper proofs
using the normal form theorem for amalgamated free products and the finiteness
fact (A) of `two-occurrence-realizability-is-type-f-benignness-proof`. Fact (A)
says that an amalgam of type `F_m` groups over a type `F_m` subgroup is of type `F_m`.

**Normal form.** In `P *_C Q`, a product `g_1 g_2 ... g_l` with `l >= 1` and
entries alternately in `P \ C` and `Q \ C` is not in `C`, and in particular is
not `1`. Every element outside `C` is such a product.

## Step 0. The subgroup lemma

Let `P_0 ≤ P` and `Q_0 ≤ Q` with `P_0 ∩ C = Q_0 ∩ C = C_0`. Then the natural
map `P_0 *_{C_0} Q_0 -> P *_C Q` is injective.

- **Well defined.** The inclusions `P_0 -> P` and `Q_0 -> Q` agree on `C_0 ⊆ C`.
- **Injective.** Let `g ≠ 1` in `P_0 *_{C_0} Q_0`.
  - If `g ∈ C_0`, then its image is `g ≠ 1`.
  - Otherwise `g` is an alternating product with entries in `P_0 \ C_0` and `Q_0 \ C_0`.
  - An entry in `P_0 \ C_0` is not in `C`, since `P_0 ∩ C = C_0`. The same holds on the `Q` side.
  - So the image is an alternating product in `P *_C Q` and is not `1`. ∎

## Step 1. Item 1: benign iff the double embeds

- **(⇒)** Let `(Λ, Σ)` be a witness, so `K ≤ Λ` and `K ∩ Σ = N`.
  - Put `Λ_D = Λ_1 *_Σ Λ_2`, two copies of `Λ` amalgamated along `Σ` by the identity. It is of type `F_m` by (A).
  - Apply Step 0 with `P_0 = K_1`, `Q_0 = K_2` and `C_0 = N`. The hypothesis holds because `K_i ∩ Σ = N` in each copy, and both copies of `N` are identified by the identity of `Σ`.
  - So `D(K, N) = K_1 *_N K_2` embeds in `Λ_D`.
- **(⇐)** Let `ι : D(K, N) -> Λ` be injective with `Λ` of type `F_m`.
  - By the normal form, `K_1 ∩ K_2 = N` in `D(K, N)`. An element of `K_1 \ N` is a product of length 1, so it is not in the amalgamated subgroup, and hence not in `K_2`.
  - Since `ι` is injective, `ι(K_1) ∩ ι(K_2) = ι(N)`.
  - `Σ = ι(K_2) ≅ K` is of type `F_m`, and `Λ ⊇ ι(K_1) ≅ K`.
  - So `(Λ, Σ)` witnesses that `N` is `F_m`-benign in `K`, identified with `ι(K_1)`. ∎

## Step 2. Item 2

Compose (⇒) and (⇐) of Step 1. The witness produced by (⇐) is `Σ = ι(K_2) ≅ K`. ∎

## Step 3. Item 3

- **Torsion-free.** A finite subgroup of an amalgam fixes a vertex of the
  Bass–Serre tree (Serre, *Trees*, I.4.3), so it is conjugate into a factor. The
  factors are free, so every finite subgroup is trivial.
- **Presentation.** `D(F(A), N) = <A_1 ∪ A_2 | w_1 = w_2 (w ∈ N)>`, where `w_i` is `w` spelled in the letters `A_i`.
  - The relator set is r.e. when `N` is r.e.
  - By Craig's trick, a finitely generated group with an r.e. set of relators is recursively presented.
- **Klein bottle.** `F(a)/<<a^2>> = Z/2` and `N = <a^2>`. The double is `<a, b | a^2 = b^2>`, the fundamental group of the Klein bottle, a closed aspherical surface. ∎

## Step 4. Item 4

- **The equivalence.** Chain three facts:
  - By items 1 and 3 of `two-occurrence-realizability-is-type-f-benignness`,
    every finitely generated recursively presented group has a type `F_m`
    triple iff `N_U` is `F_m`-benign in `F(B)`.
  - By item 1 of that claim, a triple gives the reduction `v -> [phi(v), q]` into a type `F_m` group.
  - By Step 1, `N_U` is `F_m`-benign iff `D_U` embeds in a type `F_m` group.
- **`E_m` implies closure.**
  - `D_U` is finitely generated and recursively presented (Step 3). So it embeds in `U` (Higman).
  - `E_m` makes `U`, which is finitely presented, embed in a type `F_m` group, and hence `D_U` too. ∎

## Step 5. Item 5

- **The hypothesis gives a double with no host.**
  - Let `G = F/N_G` be as in item 5. By item 1 of
    `two-occurrence-realizability-is-type-f-benignness`, a type `F_{n+1}` triple
    for `G` would give such a reduction. So `N_G` is not `F_{n+1}`-benign.
  - By Step 1, `D(F, N_G)` embeds in no group of type `F_{n+1}`.
  - `D(F, N_G)` embeds in `U` (Step 3 and Higman). So `U` has no type `F_{n+1}` host, and `E_{n+1}` fails.
- **Part 2 fails.** An `F_∞` host is an `F_{n+1}` host.
- **Part 1 fails.** This uses the equivalence recorded in
  `zaremsky-1-01-type-fn-groups-embed-in-type-fn-plus-1` (Universal forms).
  - If Part 1 held, induction would give `U ≤ K_3 ≤ ... ≤ K_{n+1}` with `K_j` of type `F_j`, contradicting the failure of `E_{n+1}`.
  - So some group of type `F_j`, with `2 <= j <= n`, embeds in no group of type `F_{j+1}`. That is `some-type-fn-group-embeds-in-no-type-fn-plus-1-group`. ∎

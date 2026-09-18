---
rg: 2
id: fsp-q-hf-reduces-to-hyperbolic-kernel-pairs
kind: claim
title: In the coproduct field of an amalgam of Hughes-free rings, every locally elliptic subgroup is Linnell in every characteristic, so FSP's q:HF reduces to Hughes pairs whose kernel contains a hyperbolic element
distinct_from:
  fsp-graph-of-rings-and-linnell-extension-imports: that imports the embedding of k[A *_C B] into U(D_A *_{D_C} D_B); this proves the Linnell condition there for every locally elliptic subgroup, not only the vertex groups, and deduces the Hughes condition for every pair whose kernel is locally elliptic.
  universal-division-rings-do-not-iterate-over-graphs-of-groups: that identifies the Linnell iteration with q:HF; this settles the elliptic half of q:HF for amalgams in every characteristic and isolates the hyperbolic-kernel pairs as the only open case.
  higman-group-algebras-embed-in-division-rings: that embeds k[Higman] in a division ring; this notes that q:HF is vacuous for Higman's group itself, which is perfect, and applies to its locally indicable subgroups instead.
  kaplansky-zero-divisor-conjecture: that is the conjecture; this is a strict reduction of the Hughes-free iteration step used to build division-ring hosts over non-amenable edges.
---

**ESTABLISHED** (reduction) by [[fsp-q-hf-reduces-to-hyperbolic-kernel-pairs-proof]]. Not yet independently re-derived.

**Setting.**
- `k` is any division ring, in any characteristic.
- `G = A *_C B` with `A`, `B` locally indicable, and `C` any common subgroup. The edge `C` may be free, as in
  Higman's group.
- Hughes-free division rings `D_A = D_{kA}` and `D_B = D_{kB}` exist.
- `D_C` is the division closure of `kC` in either ring. The two are identified by Hughes uniqueness.
- `R = D_A *_{D_C} D_B` is Cohn's coproduct. `U = U(R)` is its universal field, and it contains `k[G]`
  (FSP, Cor. locIndGraphDivRing).
- For `K <= G`, `D_K` denotes the division closure of `kK` in `U`.

FSP's question q:HF asks whether `D_G = U` is Hughes-free when `G` is locally indicable. By
`universal-division-rings-do-not-iterate-over-graphs-of-groups`, this is equivalent to `k[G]` having a Linnell
embedding. It is open in positive characteristic.

**Theorem.**
1. **Elliptic Linnell.** If `K <= G` fixes a vertex of the Bass-Serre tree (that is, `K <= gAg^-1` or
   `K <= gBg^-1`), every right transversal of `K` in `G` is left linearly independent over `D_K` in `U`.
2. **Locally elliptic Linnell.** The same holds if every finitely generated subgroup of `K` fixes a vertex.
3. **Hughes condition for elliptic kernels.** Let `H <= G` be finitely generated, `N ⊴ H` with `H/N = <tN> ≅ Z`,
   and `N` locally elliptic. Then the powers `t^n` are left linearly independent over `D_N`. This holds whatever
   `H` is, including when `H` acts on the tree with hyperbolic elements.
4. **Reduction.** Let `L <= G` be locally indicable. `D_L` is Hughes-free for `kL` if and only if the Hughes
   condition holds for the pairs `(H, N)` in `L` where `N` contains an element acting hyperbolically on the tree.
   For such pairs, `N` and `H` have the same minimal subtree. In particular, q:HF for `G` reduces to these
   pairs.

**What is new, and what stays open.**
- FSP prove independence of the vertex-group transversals, which gives injectivity. Items 1–3 extend this to
  every locally elliptic subgroup, and to the Hughes pairs they give, in every characteristic.
- Item 3 covers many pairs with hyperbolic `H`: for example, `H = N ⋊ <t>` with `t` hyperbolic and `N` inside an
  edge group.
- The open case is a kernel `N` that is not locally elliptic. Then `N` acts on the minimal subtree `T_H` with no
  fixed vertex, and `H/N ≅ Z` acts on the quotient graph `N \ T_H`. It is not known that `D_N` is the coproduct
  field of the induced graph of rings of `N`; see the compatibility statement below.
- Positive characteristic one-relator groups of primitivity rank 2 (FSP, Thm LL_HF) are open instances of exactly
  this case.

**Higman's group.** The Higman group `Hig = G1 *_{F(a,c)} G2` is perfect, so it is not locally indicable, and
q:HF says nothing about `Hig` itself. The step "Hughes condition for locally indicable subgroups acting
nontrivially on the Bass-Serre tree" becomes item 4 applied to locally indicable `L <= Hig`:
- The vertex rings are Hughes-free in every characteristic (`higman-bs-amalgam-has-hughes-free-division-rings`).
- Every pair in `L` with a locally elliptic kernel is settled.
- The open pairs are those whose kernel contains a hyperbolic element of `Hig`.

**Obstruction to the brief's route.** The step proposed to use Cohn inner rank on `D_A *_{D_C} D_B`. In the open
case, that inner rank computes ranks over `D_A`, but the needed relations have coefficients in `D_N`, and `D_N` is
not contained in any vertex ring. The normal-form argument needs coefficients from inside one vertex ring (proof,
§5). The missing statement is a compatibility of subgroup fields:

> For `N ⊴ H` as in item 4, the division closure of `kN` in `U` is `k[N]`-isomorphic to the coproduct field of the
> induced graph of rings of `N` on `T_H`, and `H` is generated over it by an element acting by a skew Laurent
> extension.

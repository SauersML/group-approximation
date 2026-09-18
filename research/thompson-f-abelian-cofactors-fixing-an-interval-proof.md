---
rg: 2
id: thompson-f-abelian-cofactors-fixing-an-interval-proof
kind: route
title: "An abelian transitive subgroup has one point stabilizer, which lies in the core of H; the centralizer of K then acts by translations, and a rigid interval subgroup in the centralizer puts its commutant into H"
target: thompson-f-abelian-cofactors-fixing-an-interval-force-f-into-h
requires:
  - nontrivial-normal-subgroups-of-thompson-f-contain-a-copy-of-f
  - thompson-f-rigid-interval-subgroups-facts
---

**Setting.** `F = HK` with `K` abelian, `X = F/H`, and `F` acts on `X` by `g·(fH) = gfH`. Since
`F = F^(-1) = K^(-1) H^(-1) = KH`, every coset has the form `kH` with `k ∈ K`. So `K` acts
transitively on `X`. `F[a,b]` and `F(a,b)` are as in `thompson-f-rigid-interval-subgroups-facts`:
`F[a,b]` fixes `[0,1] ∖ [a,b]` pointwise, and `F(a,b)` consists of the elements of `F[a,b]` that are
the identity near `a` and near `b`.

**Step 1 (one stabilizer).** For `x = kH`, `Stab_K(x) = k (K ∩ H) k^(-1) = K ∩ H`, because `K` is
abelian. Every point of `X` has this form, so `K ∩ H` fixes every point of `X`. Hence
`K ∩ H ⊆ ⋂_(g ∈ F) gHg^(-1) = core_F(H)`, and `core_F(H)` is the kernel of the action on `X`.

**Step 2 (dichotomy).** `core_F(H)` is normal in `F`.
- If it is nontrivial, then by `nontrivial-normal-subgroups-of-thompson-f-contain-a-copy-of-f` it
  contains a subgroup isomorphic to `F`, and so does `H ⊇ core_F(H)`. This is the first alternative.
- Otherwise `core_F(H) = 1`, so `F` acts faithfully on `X`, and `K ∩ H = 1` by Step 1. Then `K` acts
  freely and transitively, and `k ↦ kH` is a bijection `K → X`.

In the rest of the proof, assume `core_F(H) = 1`.

**Step 3 (the centralizer acts by translations).** Let `c ∈ C_F(K)`. Since `cH ∈ X`, there is a unique
`ψ(c) ∈ K` with `cH = ψ(c)H`. For `k ∈ K`,
`c·(kH) = ckH = kcH = kψ(c)H`.
- *Homomorphism.* For `c, c′ ∈ C_F(K)`, `cc′H = c ψ(c′)H = ψ(c′) cH = ψ(c′)ψ(c)H`. By uniqueness,
  and since `K` is abelian, `ψ(cc′) = ψ(c)ψ(c′)`.
- *Kernel.* `ker ψ = {c : cH = H} = C_F(K) ∩ H`.
- *Splitting.* `K ⊆ C_F(K)` because `K` is abelian, and `ψ(k) = k` because `kH = kH`. So
  `C_F(K) = ker ψ ⋊ K`.
- *Commutators.* `ψ` takes values in an abelian group, so `[C_F(K), C_F(K)] ⊆ ker ψ ⊆ H`.

This proves item 1.

**Step 4 (a rigid interval subgroup centralizes `K`).** Suppose `int Fix(K) ≠ ∅`. Choose dyadic
`a < b` with `[a,b] ⊆ int Fix(K)`, and set `L = F[a,b]`. Let `l ∈ L` and `k ∈ K`.
- For `x ∈ [a,b]`: `l` fixes `a` and `b`, so `l(x) ∈ [a,b]`, and `k` fixes both `x` and `l(x)`. Hence
  `kl(x) = l(x) = lk(x)`.
- For `x ∉ [a,b]`: `k` is a bijection fixing `[a,b]` pointwise, so `k(x) ∉ [a,b]`, and `l` fixes both
  `x` and `k(x)`. Hence `lk(x) = k(x) = kl(x)`.

So `L ⊆ C_F(K)`.

**Step 5 (conclusion).** By Step 3, `H ⊇ [L, L]`. By (F2) of
`thompson-f-rigid-interval-subgroups-facts`, verbatim "If $a<b$ are dyadic rationals, then $F[a,b]$ is
isomorphic to $F$. Furthermore, its commutant is exactly the subgroup $F(a,b)$", we get
`[L,L] = F(a,b)`. So `H ⊇ F(a,b)`.
- Choose dyadic `c, d` with `a < c < d < b`. Every element of `F[c,d]` is the identity near `a` and
  near `b`, so `F[c,d] ⊆ F(a,b)`.
- By (F2) again, `F[c,d] ≅ F`.

So `H` contains a subgroup isomorphic to `F`. With Step 2, this proves item 2. ∎

**Remarks.**
- Only abelianness of `K` is used, through Step 1 (one stabilizer) and Step 3 (translations). Neither
  amenability of `H` nor any property of the Schreier graph of `X` enters.
- Where it stops. If the union of the supports of `K` is dense, then `C_F(K)` may contain no copy of `F`.
  For example, for `K = ⟨x_0⟩` one expects `C_F(K)` to be cyclic; this was not checked, and nothing
  here depends on it. Steps 3–5 then give nothing, and the residual problem is recorded in
  `thompson-f-abelian-factorizations-put-f-into-the-cofactor`.

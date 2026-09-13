---
rg: 2
id: digit-affine-hosts-with-abelian-linear-parts-proof
kind: route
title: Sections of translations make N/pN finite, and a finitely generated faithful module over a commutative ring of positive transcendence degree has infinite N/pN
target: digit-affine-hosts-with-abelian-linear-parts-have-finite-rank
requires: []
---

Notation as in the target. Write `t_b` for the translation `v -> v + b`.

1. **`N ∩ pO^n = pN`.**
   - *One step.* Let `b in N ∩ pi O^n`. Then `t_b` maps each first-level coset
     `d + pi O^n` to itself, and `t_b(d + pi w) = d + pi (w + b/pi)`. So its
     section at every first-level vertex is `t_(b/pi)`. By self-similarity
     `b/pi in N`.
   - *Iterate.* If `b in N ∩ pi^e O^n`, apply this `e` times to get
     `b/pi^e = b/p in N`. So `N ∩ pO^n ⊆ pN`, and the reverse inclusion is clear.
   - *Consequences.* `N/pN` embeds in the finite group `O^n/pO^n`. `N` is
     torsion-free, and `∩_k p^k N ⊆ ∩_k p^k O^n = 0`.

2. **`N` is a finitely generated faithful module over a commutative ring.**
   - *The action.* `(A,b) t_c (A,b)^-1 = t_(Ac)`, so `L` preserves `N`. Since `N`
     is abelian, conjugation by `G` on `N` factors through `G/N = L`.
   - *Finite generation.* `L` is finitely generated and virtually abelian, hence
     finitely presented, and `G` is finitely generated. So `N` is the normal
     closure of finitely many elements, that is, a finitely generated
     `Z[L]`-module. Let `L_0 <= L` be an abelian subgroup of finite index. Then
     `Z[L]` is a finitely generated `Z[L_0]`-module, so `N` is a finitely
     generated `Z[L_0]`-module.
   - *The ring.* Let `Λ` be the image of `Z[L_0]` in `End_Z(N)`. It is a finitely
     generated commutative ring, hence Noetherian, and `N` is a faithful finitely
     generated `Λ`-module.

3. **Domain lemma.** Let `D` be a finitely generated commutative domain of
   characteristic zero with `trdeg_Q Frac(D) >= 1`, and let `p` be a nonunit of
   `D`. Then `D/pD` has infinitely many maximal ideals.
   - *Maximal ideals have height `1 + trdeg >= 2`.* For maximal `m`, the field
     `D/m` is a finitely generated `Z`-algebra, hence finite, so `m ∩ Z = lZ` for
     a prime `l`. `Z` is Noetherian and Cohen--Macaulay, hence universally
     catenary (Stacks, Lemma 10.105.9, tag 00NM). The dimension formula (Stacks,
     Lemma 29.53.1, tag 02JU, with equality for universally catenary bases)
     gives `ht m = ht(lZ) + trdeg_Q Frac(D) - trdeg_(F_l) D/m = 1 + trdeg`.
   - *A height-one prime over `p`.* Since `p != 0`, Krull's principal ideal
     theorem gives a prime `q` minimal over `pD` of height one. By the previous
     item `q` is not maximal, so `D/q` is a domain that is not a field.
   - *Infinitely many points.* `D/q` is a finitely generated `Z`-algebra, hence
     Jacobson, so its maximal ideals intersect in `0`. Finitely many nonzero
     ideals of a domain have nonzero product, lying in their intersection. So
     `D/q` has infinitely many maximal ideals, and they all contain `p`.

4. **Every minimal prime of `Λ` has transcendence degree zero.**
   - *Minimal primes are annihilators.* `N` is faithful and finitely generated,
     so `Supp N = V(Ann N) = Spec Λ`. Minimal primes of the support are
     associated primes (Matsumura, *Commutative Ring Theory*, Theorem 6.5). So a
     minimal prime `P` is `Ann(x)` for some `0 != x in N`.
   - *Characteristic zero.* `x` has infinite order, so `P ∩ Z = 0`.
   - *`p` is a nonunit mod `P`.* If `pλ - 1 in P`, then `x = pλx = p^k λ^k x`
     lies in `p^k N` for every `k`, so `x = 0` by Step 1.
   - *The support of `N/pN`.* By Nakayama, `Supp(N/pN) = Supp N ∩ V(pΛ) = V(pΛ)`.
     `N/pN` is finite, so `Λ/Ann(N/pN)` embeds in the finite ring `End_Z(N/pN)`.
     So `Supp(N/pN) = V(Ann(N/pN))` is finite.
   - *Contradiction.* If `trdeg Frac(Λ/P) >= 1`, Step 3 applied to `D = Λ/P`
     gives infinitely many maximal ideals of `Λ` containing `P + pΛ`. They all
     lie in `V(pΛ)`, which is finite.

5. **Finite rank.**
   - `Λ_Q = Λ ⊗ Q` is a finitely generated `Q`-algebra. Each minimal prime of
     `Λ_Q` comes from a minimal prime `P` of `Λ` with `P ∩ Z = 0`, and the
     quotient is `(Λ/P) ⊗ Q`. By Step 4 this is a domain of transcendence degree
     zero, finitely generated over `Q`, hence a field.
   - So every prime of `Λ_Q` is maximal and `dim Λ_Q = 0`. A finitely generated
     `Q`-algebra of dimension zero is finite-dimensional, by Noether
     normalization.
   - `N ⊗ Q` is a finitely generated `Λ_Q`-module, so `dim_Q (N ⊗ Q) < ∞`.

6. **Subgroups and the corollary.**
   - *Subgroups.* For `H <= G`, `H ∩ N` has finite rank and `H/(H ∩ N)` embeds
     in `L`.
   - *Normal subgroups of `B = R x| <s,t>`.* Let `K` be normal in `B` with `B/K`
     virtually abelian. Suppose `K ∩ R = 0`. Then `[K,R] <= K ∩ R = 0`, so `K`
     centralizes `R`. An element `r s^i t^j` acts on `R` by `(1+x)^i x^j`, which
     is `1` only for `i = j = 0`. So `K <= R`, hence `K = 0`. Then `B` would be
     virtually abelian, but it contains `Z wr Z = <a,t>`. So `K ∩ R` is a nonzero
     ideal `I`. It contains `fR ≅ R` for some `f != 0`, and `R` contains the
     independent elements `x^k`, `k in Z`, so `I` has infinite rank.
   - *The corollary.* If `B <= G`, put `K = B ∩ N`. Then `B/K` embeds in the
     virtually abelian group `L`, and `K` has finite rank. This contradicts the
     previous item.

**Checks.**
- *Rank one.* `BS(1,m) = Z[1/m] x| Z` acting affinely on `Z_p` with `p ∤ m`
  has a translation subgroup of rank one.
- *The finite-generation hypothesis is needed.* `N = Z[1/p][t^±1] ∩ Z_p`, with
  `t` a transcendental unit, satisfies `N ∩ pZ_p = pN` and has infinite rank.
  `N x| <t>` is closed under sections but is not finitely generated. Step 2 is
  where finite generation enters.

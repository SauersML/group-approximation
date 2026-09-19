---
rg: 2
id: torus-knot-groups-rq-stable-citation
kind: route
title: Torus knot groups are free-by-cyclic with vanishing H_2, so Willett's free-by-cyclic theorem makes them R_q-stable unconditionally
target: torus-knot-groups-are-rq-stable
requires: []
---

Imported with credit, not reproved.  R. Willett, *Conditional representation
stability, classification of \*-homomorphisms, and relative eta invariants*,
arXiv:2408.13350, PDF dated May 25, 2026, read from arXiv on 2026-09-19.
Quotations are verbatim, except that PDF-extraction glyph damage in formulas
has been repaired: `“` for `=`, `¸` for `⋊`, `˚` for `_*`, `p q` for
parentheses, and `R q` for `R_q`.

Definition 1.6: "Let Γ be a group, and let R be a class of finite-dimensional
representations of Γ. For each finite subset S of Γ and ϵ > 0, let Q(S,ϵ)
be a class of quasi-representations, possibly depending on S and ϵ.  The
group Γ is Q-R-stable if for any finite subset S of Γ and ϵ > 0 there exists
a finite subset T of Γ and δ > 0 such that if ϕ: Γ → M_n(C)_1 is a
(T,δ)-representation, then there exists a map θ: Γ → M_k(C) in Q(S,ϵ) and a
representation π: Γ → M_{n+k}(C) in R such that ‖(ϕ(s) ⊕ θ(s)) − π(s)‖ < ϵ
for all s ∈ S. [...] If Q = R, we just say that Γ is R-stable (conditional
on P)."

Remark 1.8: "Specifically, the main case we will use is the class R_q of
finite-dimensional representations that factor through a finite quotient of
Γ, and Q = R = R_q."

Section 1.4: "Recall that a free-by-cyclic group is a group of the form
F ⋊_α Z, where F is a finite rank free group, and Z acts on F by an
automorphism α".

Theorem 1.14: "Let Γ = F ⋊_α Z be a free-by-cyclic group.  Let n be the
rank of F, and let ϕ_* : R^n → R^n be the map induced by ϕ on the first
real homology group. Then H_2(Γ) is free abelian, with rank equal to the
multiplicity m of the eigenvalue 1 of α_*; choose a basis c_1,...,c_m for
H_2(Γ).  The group Γ is R_q-stable, conditional on vanishing of the winding
number invariants w(c_i,·) for all i ∈ {1,...,m}. In particular, if α_*
does not have 1 as an eigenvalue, then Γ is R_q-stable."

The same statement appears as Theorem 7.8, and it rests on Proposition 7.7:
"Let Γ = F ⋊_ϕ Z be a free-by-cyclic group where F is a finitely generated
free group, and ϕ is an automorphism of F. Then Γ is UCT, FD, LLP, and the
BCK assembly map for Γ is an isomorphism."

## Hypothesis check (elementary, proved here)

Let `p, q >= 2` with `gcd(p, q) = 1`, and let `K = <x, y | x^p = y^q>`.  Put
`c = x^p = y^q`.  It is central, since it commutes with both generators.

1. **A map to `Z`.**  Define `f : K -> Z` by `f(x) = q` and `f(y) = p`.  It
   respects the relator, since `pq = qp`.  It is onto because
   `gcd(p, q) = 1`.  Let `N = ker f`.  Then `K = N ⋊ Z`, because the
   quotient `Z` is free, so any preimage of `1` splits `f`.
2. **`N` embeds in `Z/p * Z/q`.**  `K/<c> = <x, y | x^p, y^q> = Z/p * Z/q`.
   Since `f(c^k) = kpq`, the subgroup `N` meets `<c>` trivially.  So `N`
   maps injectively into `Z/p * Z/q`.  Let `f̄ : Z/p * Z/q -> Z/pq` be
   `f mod pq`.  It is well defined, because `f(c) = pq`.  The image of `N`
   is exactly `ker f̄`.
   - `N` maps into `ker f̄`, because `f(N) = 0`.
   - Conversely, suppose `g in K` has `f(g) = kpq`.  Then `g c^(-k)` lies in
     `N` and has the same image as `g`.
3. **`N` is free of rank `(p-1)(q-1)`.**
   - `f̄` maps `x` to `q`, which has order `p` in `Z/pq`, and `y` to `p`,
     which has order `q`.  So `f̄` is injective on both free factors.
     By the Kurosh subgroup theorem, every finite subgroup of `Z/p * Z/q` is
     conjugate into a factor, so `ker f̄` is torsion-free.  Again by Kurosh,
     a subgroup of a free product that meets no conjugate of a factor
     nontrivially is free.
   - `f̄` is onto, because `q` and `p` generate `Z/pq`.  So `ker f̄` has
     index `pq`.
   - The rational Euler characteristic of `Z/p * Z/q` is `1/p + 1/q - 1`,
     so `chi(N) = pq(1/p + 1/q - 1) = p + q - pq`.  Hence
     `rank N = 1 - chi(N) = (p-1)(q-1)`.
   - For `(p, q) = (4, 3)` this gives `N ≅ F_6`.
   So `K ≅ F_((p-1)(q-1)) ⋊_α Z` is free-by-cyclic.
4. **`H_2(K; Z) = 0`.**
   - The relator `x^p y^(-q)` is cyclically reduced and is not a proper
     power in `F(x, y)`: it has one `x`-syllable and one `y`-syllable.  So
     by Lyndon's theorem the presentation 2-complex `X` is aspherical.
   - `H_2(X)` is the kernel of the boundary map on 2-chains, so it is free
     abelian.
   - `chi(X) = 1 - 2 + 1 = 0`, and `H_1(X) = Z^2 / (p, -q)Z ≅ Z` because
     `gcd(p, q) = 1`.  So `b_2 = chi - 1 + b_1 = 0`, and hence `H_2(K) = 0`.
5. **Apply Theorem 1.14.**  By its first sentence, `H_2(K)` is free of rank
   `m`, the multiplicity of `1` as an eigenvalue of `α_*`.  So `m = 0`: the
   map `α_*` does not have `1` as an eigenvalue.  The "in particular" clause
   then gives that `K` is `R_q`-stable.  No winding-number condition remains,
   because the basis `c_1, ..., c_m` is empty.

## Consistency checks

- **Three-manifold theorem.**  Willett's Theorem 7.13 ("the fundamental
  group of a compact, connected, aspherical three-manifold M, possibly with
  boundary ... In particular, if H_2(M) is torsion, then Γ is R_q-stable")
  gives the same conclusion.  The complement of the `(p,q)` torus knot in
  `S^3` is compact and aspherical after removing an open tubular
  neighbourhood.  It has `H_2 = 0` by Alexander duality, and its
  fundamental group is `K(p, q)`.  This is a second route to the same
  import, and it is not needed.
- **Obstruction consistency.**  Dadarlat's rational obstruction vanishes
  because `H^2(K; Q) = 0`, so there is no conflict with
  `dadarlat-matricial-stability-obstruction`.
- **The monodromy.**  The torus knot is fibred, and its monodromy has
  characteristic polynomial equal to the Alexander polynomial
  `(t^(pq) - 1)(t - 1) / ((t^p - 1)(t^q - 1))`.  That polynomial does not
  vanish at `t = 1`, since its value there is `1`.  This independently
  confirms that `1` is not an eigenvalue of `α_*`.
- **The finite-index subgroup `F_6 × Z`.**  For the trivial automorphism,
  Theorem 1.14 attaches six winding-number conditions to `H_2 = Z^6`.
  Willett's Remark 1.17 says that such conditions "are necessary for
  R_q-stability to hold".  So `F_6 × Z` is only conditionally
  `R_q`-stable, although its index-12 overgroup `K(3,4)` is unconditionally
  `R_q`-stable.  Unconditional `R_q`-stability therefore does not pass to
  finite-index subgroups, and the argument here goes through the
  free-by-cyclic structure, not through the product subgroup.

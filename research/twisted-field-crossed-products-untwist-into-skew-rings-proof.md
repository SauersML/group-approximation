---
rg: 2
id: twisted-field-crossed-products-untwist-into-skew-rings-proof
kind: route
title: Adjoin a generic trivialization t of the cocycle, let G act on it through the augmentation ideal, and send a u_g to a t_g v_g
target: twisted-field-crossed-products-untwist-into-skew-rings
requires:
  - rank-condition-rings-have-weakly-finite-images
  - field-crossed-product-rank-condition-survival-cases
---

This route is self-contained and elementary. The notation is the claim's.

1. **Well-defined ring maps.**
   - `σ_g` sends each generator `t_h` of the Laurent ring `K[t^(±1)]` to a unit, namely a scalar in `K^x` times a
     Laurent monomial. So `σ_g` extends to a ring endomorphism of `K[t^(±1)]` that agrees with `σ_g` on `K`.
   - For `h = 1`: `α(g,1) t_g t_g^(-1) = 1 = t_1`, so the definition is consistent. Monomials with `gh = 1` read
     `t_1 = 1`.
2. **Action.**
   - Compute
     `σ_g σ_k (t_h) = σ_g(α(k,h)) · α(g,kh) t_(gkh) t_g^(-1) · (α(g,k) t_(gk) t_g^(-1))^(-1)
     = σ_g(α(k,h)) α(g,kh) α(g,k)^(-1) · t_(gkh) t_(gk)^(-1)`.
   - The cocycle identity turns the scalar into `α(gk,h)`, so the result is `σ_(gk)(t_h)`.
   - `σ_1(t_h) = α(1,h) t_h = t_h`.
   - So `σ` is a homomorphism into the automorphisms of the Laurent ring, with `σ_(g^(-1))` inverse to `σ_g`. It
     extends to `L = Frac`.
3. **Faithfulness.** Take `g ≠ 1`.
   - If `|G| = 2`, then `σ_g(t_g) = α(g,g) t_g^(-1) ≠ t_g`.
   - Otherwise choose `h ∉ {1, g^(-1)}`. Then `σ_g(t_h)` is a scalar times `t_(gh) t_g^(-1)`, where `gh ≠ 1` and
     `g ≠ gh`. This is not a scalar multiple of `t_h`, because Laurent monomials in independent variables are
     distinct.
4. **Homomorphism.**
   - `φ(u_g) φ(u_h) = t_g v_g t_h v_h = t_g σ_g(t_h) v_(gh) = α(g,h) t_(gh) v_(gh) = φ(α(g,h) u_(gh))`.
   - `φ(u_g) φ(a) = t_g σ_g(a) v_g = φ(σ_g(a) u_g)`.
   - `φ(1) = t_1 v_1 = 1`.
   - `φ` is injective because `{t_g v_g}` is left `L`-linearly independent.
5. **Simplicity.** Let `I` be a nonzero ideal of `L ⋊ G`.
   - Take `x ∈ I` of minimal support, translated by some `v_g^(-1)` and scaled so that `x_1 = 1`.
   - For `a ∈ L`, `ax - xa = Σ_g (a - σ_g(a)) x_g v_g` has smaller support, so it is `0`.
   - Faithfulness then forces `x_g = 0` for `g ≠ 1`. So `x = 1` and `I` is the whole ring.
   - A simple ring is its only nonzero image. By `rank-condition-rings-have-weakly-finite-images`, the rank
     condition is therefore equivalent to weak (stable) finiteness.
6. **Lattice.**
   - `σ_g` acts on exponent vectors by `e_h ↦ e_(gh) - e_g`, with `e_1 = 0`.
   - The same formula holds for `[h]-[1] ↦ [gh]-[g] = ([gh]-[1]) - ([g]-[1])`.
   - `{[h]-[1] : h ≠ 1}` is a `Z`-basis of `I_G`.
   - `t_g σ_g(t_h) / t_(gh) = α(g,h)`, so `α = ∂t`.
   - For `α = 1`, `t_h = x_h / x_1` is equivariant, with image the degree-zero part of `K(x_g)`.
7. **Corollary A.** `AB = I_d` with `r < d` over `K*_α G` maps under `φ` to the same identity over `L ⋊ G`, and
   the same holds for `AB = I, BA ≠ I`, since `φ` is injective.
8. **Corollary B.** Extend `ι` by `t_h ↦ c_h` with `c ∈ T^(G \ 1)`.
   - **Independence.** Haar-a.e. `c` is algebraically independent over the countable field `ι(K)`. A nonzero
     polynomial in finitely many coordinates vanishes on a Haar-null subset of a torus, since it is real-analytic
     and not identically zero there. So `ι_c ∈ Emb(L, C)`.
   - **Equivariance.** `(g·ι_c)(t_h) = ι_c(σ_(g^(-1)) t_h) = ι(α(g^(-1),h)) c_(g^(-1)h) c_(g^(-1))^(-1)`.
     - Over `g·ι`, the fibre map is the continuous group automorphism `c ↦ (c_(g^(-1)h) c_(g^(-1))^(-1))_h` of
       `T^(G \ 1)`, followed by the translation by `(ι(α(g^(-1),h)))_h ∈ T^(G \ 1)`. That translation is valid
       because the values have modulus 1 a.e.
     - Both steps preserve Haar measure.
   - **Invariance.** So `ν = ∫ (ι_*Haar) dμ(ι)` is `G`-invariant.
   - **Conclusion.** Case (c) of `field-crossed-product-rank-condition-survival-cases` applied to `L ⋊ G`
     (`α = 1`, char 0) gives the rank condition, and step 7 pulls it back.
9. **Where it stops: split injectivity.** Let `M = K(x_(g,i))` with `G` freely permuting the variables.
   - `M^x / K^x` is the free abelian group on classes of irreducible polynomials, and `G` permutes these classes.
   - A stabilizer of a class `[f]`, with `f ∉ K`, permutes the finite nonempty set `vars(f)` of variables of `f`.
     Because the permutation is free, some power of each stabilizer element is `1`. So stabilizers are trivial
     when `G` is torsion-free.
   - Choosing `f` on one class per orbit and `σ_g f` on its translates is an equivariant section.
   - So `M^x ≅ K^x ⊕ Div` and `H^2(G, K^x) -> H^2(G, M^x)` is split injective.

**COMPLETE.**

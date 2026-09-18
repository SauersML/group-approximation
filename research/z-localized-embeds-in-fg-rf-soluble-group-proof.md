---
rg: 2
id: z-localized-embeds-in-fg-rf-soluble-group-proof
kind: route
title: Direct verification for the Euler lamplighter M ⋊ <y^-1, 1 + l y d/dy>
target: z-localized-embeds-in-fg-rf-soluble-group
requires:
  - fg-metabelian-groups-have-roots-at-finitely-many-primes
---

Notation as in the target.

**1. H ≅ Z ≀ Z.**
- `x^k f_j = f_(j-k)`, so `β_k f_j = x^(-k) β f_(j-k) = (1 + l(j-k)) f_j`.
- The `β_k` are diagonal, so they commute. Suppose `Π_k β_k^(n_k) = 1`. Then the
  rational function `Π_k (1 + l(t - k))^(n_k)` of `t` equals 1 at every integer `t`,
  hence identically. The factors are distinct irreducible polynomials, so all
  `n_k = 0`.
- `x β_k x^(-1) = β_(k-1)`, `x` has infinite order, and `<x> ∩ <β_k : k> = 1`, since
  a nontrivial power of `x` is not diagonal.
- So `H = (⊕_k Z β_k) ⋊ <x> ≅ Z ≀ Z`.

**2. Generation and Z_(l).**
- `β_k f_0 = (1 - lk) f_0`, so `M_0 := Z[H] f_0` contains `(1 - lk)^(±1) f_0` for all
  `k`. Every integer `m ≡ 1 (mod l)` has the form `1 - lk`.
- If `l ∤ b`, then `b^(l-1) ≡ 1 (mod l)` and `1/b = b^(l-2)/b^(l-1)`. So
  `Z_(l) f_0 ⊆ M_0`.
- Applying `x^k` gives every `Z_(l) f_j`, so `M_0 = M`. Hence `G_l = <f_0, x, β>`.

**3. Solubility.** `M` is abelian and normal, and `G_l / M ≅ H` is metabelian.

**4. Residual finiteness.** Let `r >= 1` and let `N` be a multiple of `l^(r-1)`.
- *The finite quotients.* `π : M -> M_(r,N) = ⊕_(j in Z/N) (Z/l^r) f_j` reduces
  coefficients mod `l^r` and indices mod `N`. It is `H`-equivariant for
  `x̄ f_j = f_(j-1)` and `β̄ f_j = (1 + lj) f_j`, which is well defined because `lj mod
  l^r` depends only on `j mod l^(r-1)`. So `(m, h) -> (π(m), h̄)` is a homomorphism onto
  a subgroup of the finite group `M_(r,N) ⋊ Aut(M_(r,N))`.
- *If `h != 1`.* Pick `f_j` with `h f_j = Σ c_i f_i != f_j`. Take `N` larger than the
  spread of the indices involved and `r` large, so that some `c_i != 0` (`i != j`) or
  `c_j - 1` is nonzero mod `l^r`. Then `h̄ != 1`.
- *If `h = 1` and `m != 0`.* Take `N` larger than the support of `m` and `r` large.

**5. Algorithms.** Elements are pairs `(m, h)`:
- `m` is a finitely supported vector with exact coefficients in `Z_(l)`;
- `h = x^a · diag(Π_k (1 + l(j-k))^(n_k))` has finite data `(a, (n_k))`.

Multiplication and equality are computable, so the word problem is solvable. For
`w != 1`, the search over `(r, N)` in 4 terminates with a finite quotient in which
`w` survives, and the quotient is given explicitly. ∎

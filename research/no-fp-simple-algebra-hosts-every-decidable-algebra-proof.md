---
rg: 2
id: no-fp-simple-algebra-hosts-every-decidable-algebra-proof
kind: route
title: Monomial relators x y^n x encode any decidable set, and an embedding reduces membership to the host word problem
target: no-fp-simple-algebra-hosts-every-decidable-algebra
requires:
  - fp-simple-algebras-have-solvable-word-problem
---

1. **Monomial normal forms.** In `A_X`, the ideal is spanned by monomials that
   contain some `x y^n x` with `n in X` as a subword. A polynomial is zero iff
   each of its monomials, after collecting terms, contains such a subword. The
   subwords of the form `x y^m x` of a word are finite in number and can be
   listed, so `A_X` has solvable word problem whenever `X` is decidable.
2. **Membership is visible.** The only subword of `x y^n x` of the form
   `x y^m x` is itself. So `x y^n x = 0` in `A_X` iff `n in X`.
3. **Reduction.** Let `phi : A_X -> B` be an injective homomorphism, and write
   `phi(x), phi(y)` as polynomials of length at most `c` in the generators of
   `B`. Then `n in X` iff `phi(x) phi(y)^n phi(x) = 0` in `B`. That word has
   length at most `c(n+2)`, is written down in time `O(n)`, and its vanishing is
   decided in time `C_B T(C_B c (n+2)) + O(n)`.
4. **Choosing X.** Replace `T` by `l -> max_{k <= l} T(k)`, so `T` is
   nondecreasing, and put `h(n) = n T(n(n+2)) + n^2`. For fixed constants `C_B`
   and `c`, the bound in step 3 is at most `h(n)` for all large `n`. By the time
   hierarchy theorem for unary languages there is a decidable `X ⊆ N`, with `n`
   given in unary, that is not decidable in time `O(h(n))`. For that `X`, no `B`
   in `H` contains `A_X`.
5. **Single fp simple hosts.** A single finitely presented simple algebra has a
   recursive word-problem time bound by `fp-simple-algebras-have-solvable-word-problem`:
   take the running time of its algorithm as `T`. Apply step 4.

---
rg: 2
id: subshift-diagonal-automorphisms-need-infinite-spatial-class
kind: claim
title: A diagonal-preserving automorphism of a minimal-subshift crossed-product ring compresses no centralizer unless its spatial class has infinite order
distinct_from:
  simple-ring-with-centralizer-compressing-automorphism: that asks for any (S, sigma) meeting (G1) and (G2); this rules out, on the flagship (G1) rings LC(X,F_q)xZ, every diagonal-preserving sigma whose spatial homeomorphism has finite order modulo the topological full group, and every "u to u^k" dilation.
  corner-matrix-ring-isos-force-flip-conjugacy: that shows ring isomorphisms between different subshift rings built from diagonal-preserving corner maps force flip conjugacy; this studies self-automorphisms of one ring and which of them have an inner power.
  virtually-inner-ring-automorphisms-fail-centralizer-compression: that is the abstract kill for automorphisms with an inner power; this identifies those automorphisms among the diagonal-preserving automorphisms of the subshift ring, and adds the complexity kill for dilations.
---

**ESTABLISHED** (proof: `subshift-diagonal-automorphisms-spatial-class-proof`).

**Setting.**  `q = p^e` is a prime power, `X` is an infinite minimal subshift
with shift `T`, `S = LC(X,F_q) semidirectProduct_T Z` with `u f u^{-1} =
f o T^{-1}`, and `D = LC(X,F_q)` is its diagonal.  `[[T]]` is the topological
full group: homeomorphisms `g` of `X` with `g(x) = T^{n(x)} x` for a
continuous `n: X -> Z`.  Let `sigma in Aut(S)` be a ring automorphism with
`sigma(D) = D`.

**Theorem.**
1. *(Spatial homeomorphism.)*  There is a unique homeomorphism `phi_sigma` of
   `X` with `sigma(1_A) = 1_(phi_sigma(A))` for every clopen `A`.  It satisfies
   `phi_sigma T phi_sigma^{-1} in [[T]]`, and
   `phi_(sigma tau) = phi_sigma phi_tau`.
2. *(Monomial form.)*  `sigma(u) = c u_nu`, where `c in LC(X, F_q^x)` and
   `u_nu = sum_n 1_(A_n) u^n` for a finite clopen partition `(A_n)` of `X`.
3. *(Inner powers.)*  If `phi_sigma^r in [[T]]` for some `r >= 1`, then
   `sigma^(e r (q-1))` is inner, `Ad(v)` with `v in S^x`.  Hence, by
   `virtually-inner-ring-automorphisms-fail-centralizer-compression` and
   `minimal-subshift-algebra-is-simple-lef-ring`, condition (G2) of
   `simple-ring-with-centralizer-compressing-automorphism` fails for
   `(S, sigma)`, for every `R` and `z`.
4. *(No dilations.)*  `phi_sigma T phi_sigma^{-1} != T^k` for every `k` with
   `|k| >= 2`.  In particular `sigma(u)` never lies in `D^x u^k` with
   `|k| >= 2`, so there is no diagonal-preserving squaring automorphism
   `u -> c u^2`.

**What dies.**  On these rings, the following all fail (G2):
- every inner automorphism, by units of `S` or of any matricially embeddable
  overring;
- every gauge automorphism `f -> f, u -> c u`, and every Frobenius twist;
- `Ad` of every topological-full-group unit;
- every automorphism induced by `psi in Aut(X,T)` with a power of `psi` in
  `<T>`, and every flip `psi T psi^{-1} = T^{-1}` with `psi^2` of that kind;
- the composite of any one of these with inner, gauge and Frobenius
  automorphisms.  Those have trivial spatial class.

The invariant is the spatial class of `phi_sigma` in
`N[[T]] / [[T]]`, where `N[[T]]` is the normalizer of `[[T]]` in `Homeo(X)`.
The automorphism dies at the finite-dimensional equality step of the
virtually-inner kill as soon as this class has finite order.  Dilation
candidates die earlier, at the word-complexity step.

**What survives.**  A diagonal-preserving witness on these rings needs
`phi_sigma` of infinite order modulo `[[T]]`, on a subshift where such
homeomorphisms exist.  The other option is a witness that preserves no
conjugate of `D`: an automorphism mapping `D` to `Ad(w) D` is `Ad(w)`
composed with a diagonal-preserving one, so it has the same spatial class.
Whether every Cartan is conjugate to `D` is the open
`subshift-crossed-product-algebraic-cartans-are-conjugate`.

**Remark, not imported.**  Boyle--Tomiyama (J. Math. Soc. Japan 50 (1998))
is usually read as `N[[T]] = [[T]] . (Aut(X,T) x| <flip>)`.  If that
decomposition holds, a subshift with `Aut(X,T) / <T>` finite leaves no
diagonal-preserving survivor at all.  This has not been checked against the
source, and nothing above depends on it.

DERIVATION
subshift-diagonal-automorphisms-spatial-class-proof

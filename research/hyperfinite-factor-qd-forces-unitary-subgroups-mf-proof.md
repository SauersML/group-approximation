---
rg: 2
id: hyperfinite-factor-qd-forces-unitary-subgroups-mf-proof
kind: route
title: Quasidiagonality passes to C*(Γ) inside R, MF algebras have MF unitary groups
target: hyperfinite-factor-qd-forces-unitary-subgroups-mf
requires: []
artifacts:
  - research/artifacts/stw99-x2-unitary-subgroup-reduction-2026-08-30.md
---

Let `Γ ≤ U(R)` be countable and let `A = C*(Γ) ⊆ R` be the separable unital
C\*-algebra it generates.

1. Quasidiagonality passes to C\*-subalgebras (a quasidiagonal set of
   operators has quasidiagonal subsets; abstractly, Voiculescu's
   characterisation by asymptotically multiplicative, asymptotically
   isometric u.c.p. maps into matrix algebras restricts to subalgebras).
   So `A` is quasidiagonal.
2. A separable quasidiagonal C\*-algebra is MF: the u.c.p. maps
   `φ_n : A → M_{k(n)}` with `‖φ_n(ab) − φ_n(a)φ_n(b)‖ → 0` and
   `‖φ_n(a)‖ → ‖a‖` induce an injective \*-homomorphism
   `A → ∏ M_{k(n)} / ⊕ M_{k(n)}` (Blackadar--Kirchberg).
3. A countable subgroup of the unitary group of an MF algebra is an MF
   group.  Compose `Γ → U(A) → U(∏ M_{k(n)}/⊕ M_{k(n)})` and lift each
   unitary of the corona to a unitary of `∏ M_{k(n)}` (the corona of a
   sequence of matrix algebras has stable rank one, so unitaries lift;
   equivalently choose `V_n(g)` as the unitary part of a polar
   decomposition of any lift, which is `O(1)`-close in norm because the
   lift is asymptotically unitary).  Asymptotic multiplicativity holds
   because the map is a homomorphism modulo `⊕ M_{k(n)}`, and
   `limsup ‖V_n(g) − 1‖ > 0` for `g ≠ 1` because the composite is
   injective on `Γ` (`Γ → U(A)` is the inclusion and `A → corona` is
   injective).

Steps 2--3 are the standard passage "quasidiagonal ⟹ MF ⟹ unitary
subgroups MF"; step 1 is the only place where `R` enters.  Nothing about
`R` beyond `Γ ≤ U(R)` is used, so the same argument shows: for any
quasidiagonal C\*-algebra `B`, every countable subgroup of `U(B)` is MF.

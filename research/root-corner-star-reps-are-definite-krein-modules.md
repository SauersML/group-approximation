---
rg: 2
id: root-corner-star-reps-are-definite-krein-modules
kind: claim
title: Unital star representations of an involution corner of a group algebra are exactly definite-corner Krein modules, and unitary rigidity reaches only the positive ones
distinct_from:
  mf-null-corner-criterion-needs-faithful-ce-trace: that proves MF-null corner implies z in Rad_MF and kills tracial certificates; this proves the converse direction is not a formal consequence of unitary rigidity, because corner representations are Krein (possibly indefinite) group modules, and it locates the two sub-statements a corner proof must contain.
  leavitt-root-corner-algebra-is-mf-null: that is the open MF-nullity hole for the Leavitt root corner; this reformulates that hole exactly as a Krein-module rigidity statement for Delta and does not settle it.
  agent-leavitt-not-bcs-negative-root-corner: that asks for a unital map from the no-CE BCS algebra into the corner; this classifies all unital star representations of the corner itself, and its finite-dimensional part shows no exact finite model can refute either hole.
  bounded-rank-corners-excluded: that excludes bounded-rank detecting projections in a relative commutant of a unitary corona model; this excludes every nonzero finite-dimensional algebra representation, not necessarily star or unitary, of the algebraic corner algebra.
  leavitt-corner-bcs-support-coefficient-gate: that puts a Malcev gate on the coefficient ring of a BCS corner diagram; this applies Malcev to the Krein-induced module of an arbitrary finite-dimensional corner representation.
artifacts:
  - research/root-corner-star-reps-are-definite-krein-modules-proof.md
---

**ESTABLISHED (written proof, not Lean-verified).** This is a structural reduction and a class obstruction for
`leavitt-root-corner-algebra-is-mf-null`. The hole stays OPEN.

## Setting

- `Gamma` is a group and `z in Gamma` is an involution.
- `A = C[Gamma]`, `P = (1 - z)/2`, `Q = (1 + z)/2`, and `B = P A P` is the corner, a unital star algebra with unit `P`.
- `D` is a unital C*-algebra, for example a norm matrix corona `Q_k`.
- A **definite-corner Krein module** of `Gamma` over `D` is a triple `(M, sigma, xi)` made of:
  - a right `D`-module `M` with a `Gamma`-action `sigma` by `D`-linear maps;
  - a `Gamma`-invariant `D`-valued hermitian form `[.,.]` that is conjugate-linear in the first variable and `D`-linear
    in the second (the form may be **indefinite**);
  - a vector `xi` with `sigma(z) xi = -xi` and `[xi, xi] = 1`.

  These must satisfy (KM): `M` is spanned over `D` by `sigma(Gamma) xi`, and `sigma(P) M = xi D`.

## Statement

**(K1) Sign-twisted kernels.** For each double coset `<z> h <z>`, the element `P h P` is nonzero. These elements, one for
each double coset, form a basis of `B`. They satisfy these relations:

```text
P z h P = P h z P = - P h P,      (P h P)* = P h^(-1) P,      (P g P)(P h P) = (1/2)(P g h P - P g z h P).      (K1)
```

Hence a unital star homomorphism `rho : B -> D` is the same thing as a function `phi(g) = rho(P g P)` satisfying all of:

- `phi(1) = 1`;
- `phi(z g) = phi(g z) = -phi(g)`;
- `phi(g^(-1)) = phi(g)*`;
- `phi(g) phi(h) = (1/2)(phi(g h) - phi(g z h))`.

**(K2) Krein induction.** Unital star homomorphisms `rho : B -> D` and definite-corner Krein modules determine each
other through the following two constructions.

- **From `rho` to a module.** Given a unital star homomorphism `rho : B -> D`, form
  `M_rho = A P (x)_B D`. Equip it with `[a P (x) d, b P (x) e] = d* rho(P a* b P) e` and `xi = P (x) 1`. This is a
  definite-corner Krein module.
- **From a module to `rho`.** Given a definite-corner Krein module, set `rho(P g P) = [xi, sigma(g) xi]`. This is a
  unital star homomorphism.
- **Round trips.** Going from `rho` to `M_rho` and back returns `rho`. Going from a module `M` to `rho` and then to
  `M_rho` comes with a natural form-preserving `Gamma`-equivariant surjection `M_rho -> M` sending `xi` to `xi`, so
  `M_rho` is the universal module.

In `M_rho` the `z`-odd part `sigma(P) M_rho = xi D` is free of rank one with the standard positive form `d* e`, and it
is `[.,.]`-orthogonal to the `z`-even part `sigma(Q) M_rho`. Everything indefinite lives in the even part.

**(K3) Positivity criterion.** For a unital star homomorphism `rho : B -> D`, the following are equivalent.

1. The form on `M_rho` is positive semidefinite.
2. The map `E_rho : C[Gamma] -> D`, `x -> rho(P x P)`, is completely positive.
3. `rho(P x* Q x P) >= 0` in `M_n(D)` for every `n` and every `x in M_n(C[Gamma])`.
4. `rho(P g P) = V* pi(g) V` for a unitary representation `pi` of `Gamma` on a Hilbert `D`-module `X`, with an
   isometry `V : D -> X` whose range is `pi(P) X`.

Call such `rho` **positive**.

**(K4) Non-positive corner representations exist.** Take `Gamma = D_inf = <z> * <y>` with `y` an involution. Then
`B = C[T]` is the polynomial star algebra on the self-adjoint element `T = P y P`. The map `T -> t` is a unital star
homomorphism `B -> C` for every real `t`.

- It is positive if and only if `|t| <= 1`, since `rho(P y Q y P) = 1 - t^2`.
- For `|t| > 1` its Krein module is two-dimensional of signature `(1,1)`.

So "every corner representation is a compression of a unitary group representation" is false as a general principle.

**(K5) No finite-dimensional corner representations.** Suppose the normal closure `K` of `z` is finitely generated, and
every finite-dimensional complex representation of `K` is trivial on `z`. Then `B` has no unital algebra homomorphism
into any `M_n(C)` with `n >= 1`. The homomorphism need not be a star map.

For `Delta = St_20(L_(F_2)(1,2))` and `z = x_13(s_1 t_1)`, the hypothesis holds with `K = Delta`, because `Delta` is
infinite, simple and finitely generated (Malcev). Therefore `P_z C[Delta] P_z` has no nonzero finite-dimensional
representation of any kind.

## Consequences for the MF-null corner hole

**(C1) Exact reformulation.** `leavitt-root-corner-algebra-is-mf-null` is equivalent to the statement that `Delta`
has no definite-corner Krein module over any `Q_k`. By (K3) this splits into two independent sub-statements, and the
hole is exactly their conjunction.

- **(R+) Positive part.** There is no unitary representation of `Delta` on a Hilbert `Q_k`-module `X` whose `z`-odd
  part `pi(P) X` is free of rank one and whose `Delta`-translates span a dense submodule of `X`.
- **(R-) Indefinite part.** There is no such Krein module whose form is not positive.

**(C2) Where unitary rigidity stops.** The Property (T) theorem recorded for this `Delta`
(`leavitt-st20-t-free-holes-hold-via-kazhdan`) kills homomorphisms `Delta -> U(Q_k)`.

- **What it gives.** It gives (R+) only when `X` is finitely generated projective. Then
  `L(X) = p M_m(Q_k) p = Q_r` is again a norm corona.
- **Positive gap.** It does not reach countably generated `X`, which amounts to representations into
  `U(M(K (x) Q_k))` with a `Q_k`-sized `z`-odd corner.
- **Indefinite gap.** It does not reach (R-) at all. There the group acts by `J`-unitaries whose norms grow along
  words, so there is no Kazhdan projection and no spectral-gap positivity.
- **Correction.** The sentence in `mf-null-corner-criterion-needs-faithful-ce-trace`, "This is the role Property (T)
  plays in the Kazhdan routes", is therefore a heuristic, not a theorem. MF-nullity of the root corner is **not known
  to follow from (T)**. The corner route asks for a statement strictly stronger than anything the Kazhdan theorem is
  known to deliver.

**(C3) Class that dies: unitarize, then apply unitary rigidity.** This covers any proof of MF-nullity, or of LNC3's
consequences through MF-nullity, that takes a unital star map `rho : B -> Q_k`, extends it to a completely positive map
or a unitary representation of `Delta`, and then applies a unitary rigidity theorem.

- **Invariant.** The Krein form of (K2).
- **Death step.** Every such proof must first prove the positivity (K3.3) for all corner representations of `Delta`.
  No such positivity holds for corners in general, by (K4). It is exactly the unproved content of (R-).

**(C4) Finite models are useless in both directions.** By (K5), neither of the following can be witnessed or refuted
by an exact finite-dimensional model, star or not:

- `leavitt-root-corner-algebra-is-mf-null`;
- the unital map of `agent-leavitt-not-bcs-negative-root-corner`.

Any refutation must be a genuinely asymptotic, infinite-rank Krein module of `Delta` over a corona. Conversely, a
Kazhdan-free proof of the hole must control indefinite asymptotic representations of `Delta`, which is a
non-unitary rigidity with no known model even for Kazhdan groups.

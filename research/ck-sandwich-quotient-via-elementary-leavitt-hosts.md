---
rg: 2
id: ck-sandwich-quotient-via-elementary-leavitt-hosts
kind: route
title: Mark the sandwich ring by the elementary group of a Leavitt tensor host and read the host back as its quotient
target: ck-sandwich-ring-has-fp-projective-simple-quotient
requires: [simple-inputs-have-fp-elementary-leavitt-tensor-hosts, leavitt-tensor-elementary-host-criterion, square-module-ring-hosts-are-sandwich-ring-quotients]
---

Let `S` be the infinite, finitely generated, computably presented simple core.

1. **Host.** [[simple-inputs-have-fp-elementary-leavitt-tensor-hosts]] gives:
   - a finitely presented central simple `F_2`-algebra `B` with `S <= B^x`;
   - `n >= 4` such that `ker(St_n(R) -> E_n(R))` is finitely normally generated,
     where `R = B ⊗ L` and `L = L_(F_2)(1,2)`.
2. **Finite presentation and simplicity.** `S` is perfect, being infinite
   simple. [[leavitt-tensor-elementary-host-criterion]] makes `E_n(R)` a
   finitely presented simple group. It is nonabelian, so its centre is trivial
   and `PE_n(R) = E_n(R)`. `R` is a finitely presented ring (step 1 of
   [[leavitt-tensor-elementary-host-criterion-proof]]).
3. **`R ≅ R^2`.** `L` contains `x_1, x_2, y_1, y_2` with `y_i x_j = δ_ij` and
   `x_1y_1 + x_2y_2 = 1`. Their images `1 ⊗ x_i` and `1 ⊗ y_i` give
   `R_R ≅ R_R^2`, through `a |-> (y_1 a, y_2 a)` with inverse
   `(a,b) |-> x_1 a + x_2 b`.
4. **Transfer.** Item 1 of [[square-module-ring-hosts-are-sandwich-ring-quotients]]
   gives `PE_4(R) ≅ PE_n(R)`, which is finitely presented and simple.
   `S -> R^x`, `s |-> s ⊗ 1`, is injective, because tensor products over a field
   are faithful. Item 3 of the same claim, with `T = H = E_4(R)` and
   `g = e_12(1)`, gives a finitely generated ideal `I` of the sandwich ring `U`
   with `U/I ≅ R`, so `PE_4(U/I)` is finitely presented and simple.

## What the route says

The hole is implied by the Leavitt-host premise and implies group Boone--Higman
for `S`, through [[ck-maximal-kernel-via-projective-quotient-ring]] and
[[boone-higman-via-ck-maximal-kernel]]. So the congruence regime of the CK
envelope cannot be harder than the Leavitt-host premise.

The route does not make the CK envelope a *second* road to Boone--Higman. If the
premise holds, the Leavitt route already gives the conclusion directly. The
point is the other direction: a proof that attacks this hole by features of the
sandwich ring `U` is, at best, attacking the ring-host problem. The gap is
recorded in Attempt 3 of the hole.

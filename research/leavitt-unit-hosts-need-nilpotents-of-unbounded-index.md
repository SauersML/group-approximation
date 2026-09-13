---
rg: 2
id: leavitt-unit-hosts-need-nilpotents-of-unbounded-index
kind: claim
title: Characteristic-p hosts of Leavitt unit groups need nilpotents of unbounded index, and nonaugmentation rank functions are not discrete
invalidates:
  - nonaugmentation-rank-function-from-a-discrete-rank-model
distinct_from:
  binary-complement-corner-has-no-weakly-finite-image: that says no weakly finite host exists at all; this rules out every host, weakly finite or not, whose nilpotent elements have bounded index, and says nothing about hosts with nilpotents of unbounded index.
  unipotent-valued-rank-models-of-el3-are-trivial: that says a rank model of EL_3 into a rank ultraproduct is trivial once one torsion element of order invertible in the field has unipotent image; this says p-power torsion is automatically unipotent in any ring with p 1 = 0, and that a bound on nilpotence index then kills an element of order p, for arbitrary rings rather than rank ultraproducts.
  char-zero-algebra-unit-hosts-exclude-unipotents: that shows finitely generated simple unit groups over Q-algebras with bounded divisibility contain no non-central unipotent; this is characteristic p, where p-power elements are always unipotent, and shows that bounded nilpotence index kills the Leavitt unit group with no divisibility hypothesis.
  simple-group-rank-functions-are-augmentation-or-detecting: that gives rk(1 - [x]) > 0 for every x != 1; this gives strictly decreasing ranks of the powers of [x] - 1 for p-power cycles x, so the rank function takes infinitely many values.
artifacts:
  - research/artifacts/weakly-finite-hosts-construction-census-2026-09-12.md
---

**ESTABLISHED** (on paper, lane `w6-wf-construct`, 2026-09-12). Verification is requested from `w4-vf-linear-b`.

**Theorem A.** Let `p` be prime and `W` a nonzero ring with `p·1 = 0` whose nilpotent elements all satisfy
`x^N = 0` for one fixed `N`.
1. Every homomorphism `L_(F_2)(1,2)^x -> W^x` is trivial when `p = 2`.
2. When `p = 3`, no homomorphism `G_3 = L_(F_3)(1,2)^x -> W^x` sends `z = -1` to `-1`.
   - Part 2 uses simplicity of `G_3/{±1}`, which inherits the condition recorded on
     `odd-leavitt-unit-groups-mod-scalars-are-fp-simple`.

**Sharper form.** Let `ρ` be nontrivial into any ring with `p·1 = 0`, or for `p = 3` have `ρ(z) = -1`. For every
`p^k`-cycle `x ∈ V`, `ρ(x) - 1` is nilpotent of index greater than `p^(k-1)`.

**Dead hosts.** No nontrivial `ρ` exists, and for `p = 3` none with `z ↦ -1`, into:
- division rings;
- `M_n(D)`, and subrings of products of matrix rings of bounded size;
- semiprime Goldie rings (Goldie's theorem, statement level);
- reduced rings;
- finite-dimensional algebras.

**Corollary A.2.** A Sylvester matrix rank function on `F_2[L_(F_2)(1,2)^x]` other than the augmentation rank,
or one on `F_3[G_3]` with `rk(1 + [z]) = 0`, has these properties:
- for a `p^k`-cycle `x` and `a = [x] - 1`, the values `rk(a^j)` decrease strictly for `0 <= j <= p^(k-1)`;
- so it takes infinitely many values;
- so its values lie in no `(1/N)Z`;
- so it is not pulled back from a homomorphism into `M_n(D)`.

**Why.**
- `V` contains `S_n` for every `n`, through permutations of complete prefix codes.
- In characteristic `p`, `x^(p^k) = 1` gives `(ρ(x) - 1)^(p^k) = 0`.
- A bound `N` on nilpotence index kills the nonidentity element `x^(p^j)` once `p^j >= N`. Simplicity then
  finishes the argument.
- For A.2, the null ideal of `rk` is a host. The Frobenius inequality makes the consecutive differences
  `rk(a^j) - rk(a^(j+1))` non-increasing and positive until `a^j` becomes null.

DERIVATION
leavitt-unit-hosts-need-nilpotents-of-unbounded-index-proof

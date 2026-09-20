---
rg: 2
id: approximable-base-faithful-lamp-ranks-force-linear-sofic-defects
kind: claim
title: A matrix-approximable rank function on the integer-lamp Kun--Thom wreath ring that sees one lamp difference yields a linear sofic group with maximal rigid defect, so matrix-model proofs of the coset-field rank condition force a linear sofic nonsofic group
distinct_from:
  coset-field-rank-certificates-need-base-faithful-lamp-ranks: that reduces the rank condition for R_p to base-faithful rank functions on F_p[W] and kills the site-localized suppliers by idempotent dilution; this kills or converts every matrix-approximable supplier, sofic or not, by turning it into an F_p-linear sofic group with a rigid defect of rank distance one.
  kt-wreath-rank-radical-is-rank-fixed-algebra-rigidity: that computes the rank radical of the binary-lamp wreath through rank-realized actions and lamp measures on 2^X; this is about the integer-lamp wreath and rank functions on its group ring, where the invariant is the rank of the lamp difference x_(uo) - x_(gamma u o), and it reads the defect off base-faithfulness rather than off an invariant measure.
  f2-linear-sofic-groups-kill-rigid-compression-defects: that is the open win--win defect row over F_2; this proves that a matrix-model proof of the rank condition for R_2 would refute it, and that its truth rules out every such proof.
  rigid-compression-defect-normalization-dichotomy: that proves DD(C) iff NORM(C) and builds a witness from a failure of NORM; this supplies failures of NORM for the linear sofic classes from rank functions on one explicit group ring.
  integer-lamp-leavitt-cover-wreath-is-torsion-free-nonsofic: that proves nonsoficity of the integer-lamp wreath over the hyperbolic Leavitt cover pair; this uses the integer-lamp wreath over the Theorem E pair only as a carrier and proves a statement about approximable rank functions on its group ring.
  kun-thom-coset-field-crossed-product-has-the-rank-condition: that is the open rank condition for R_p; this is a barrier theorem for one class of proofs of it and a conversion of such proofs into linear sofic nonsofic groups.
---

**ESTABLISHED** by route `approximable-base-faithful-lamp-ranks-defect-proof`.

## Setting

- `Gamma < G` is the Kun--Thom Theorem E pair (`kun-thom-nonsofic-wreath`).
  Both groups are Kazhdan, and `Gamma` is infranormal but not normal in `G`.
- `X = G/Gamma`, with base point `o = Gamma`.
- `W = L x| G`, where `L = directSum_X Z` has lamp generators `x_c`, `c in X`.
  So `W = Z wr_X G`, the group written `Z wr_H G` in
  `coset-field-rank-certificates-need-base-faithful-lamp-ranks`.
- `k` is a field, `O_k = k[L] = k[x_c^(+-1)]`, and `S_k = O_k \ {0}`.
  For `k = F_p` this is the setting of `R_p = F_p(x_c) x| G`.
- Fix `u in G` with `u Gamma u^(-1) < Gamma` strictly and `gamma in Gamma \ u Gamma u^(-1)`.
  Such a pair exists because `Gamma` is infranormal and not normal.
  Put `a = u o` and `b = gamma u o`. Then `a != b`.

**Definition (matrix-approximable rank function).**
A Sylvester matrix rank function `rk` on `k[W]` is *approximable over characteristic `char k`* if
there are:

- fields `k_i` with `char k_i = char k`, sizes `n_i` and a nonprincipal ultrafilter `omega`;
- a unital ring homomorphism `Pi : k[W] -> M_omega`, where
  `M_omega = prod_omega M_(n_i)(k_i) / {rank-null}` carries the ultralimit rank `rk_omega`;

such that `rk = rk_omega o Pi` on matrices over `k[W]`.

This covers:

- weak-* limits of pullbacks of finite-dimensional representations of `W` over fields of
  characteristic `char k`;
- rank-metric asymptotic homomorphisms `W -> GL_(n_i)(k_i)`, extended linearly;
- every unital ring homomorphism from `R_p` into such an `M_omega`, restricted to `F_p[W]`.
  Such a homomorphism is a *matrix model* of `R_p`.

`rk` is *base-faithful* if `rk(s) = 1` for all `s in S_k`.
It *sees one lamp difference* if `rk(x_a - x_b) > 0`.
Base-faithful implies seeing one lamp difference.

## Theorem

Let `rk` be a Sylvester matrix rank function on `k[W]` that is approximable over characteristic
`char k`, with model `Pi`. Put `sigma = Pi|_W : W -> U(M_omega)` and `Q = sigma(W)`.

1. **Conversion.** Suppose `rk` sees one lamp difference. Then:
   - `Q` is a finitely generated group. It is `F_p`-linear sofic if `char k = p > 0`, and
     `C`-linear sofic if `char k = 0`.
   - `sigma(Gamma) <= sigma(G) <= Q` is a rigid pair, and `z = sigma(x_o)` lies in `C_Q(sigma(Gamma))`.
   - The defect element `delta = [sigma(u) z sigma(u)^(-1), sigma(gamma)]` has rank distance
     `rk_omega(delta - 1) = rk(x_a - x_b) > 0` from `1`. This distance is `1` when `rk` is base-faithful.
   - Hence `Q` is linear sofic and **not sofic**, and `NORM` fails at `(sigma|_G, z)`.
     So `DD(F_p-linear sofic)` fails, and sofic is strictly smaller than `F_p`-linear sofic.
     In characteristic 0, `linear-sofic-nonsofic-group` is answered positively.
2. **Barrier.** Suppose `DD(F_p-linear sofic)` holds. For `p = 2` this is the open row
   `f2-linear-sofic-groups-kill-rigid-compression-defects`. Then every rank function on `F_p[W]`
   that is approximable over characteristic `p` kills every translate of the lamp difference:
   `rk(x_(g a) - x_(g b)) = 0` for all `g in G`. In particular:
   - `R_p` has no matrix model;
   - no base-faithful rank function on `F_p[W]` is approximable over characteristic `p`;
   - a rank-function proof of the rank condition for `R_p` must use a non-approximable rank function.
3. **Unconditional kill of monomial models.** Suppose the lifts can be chosen as monomial matrices over
   finite fields. This means `sigma(W)` lies in the image of `prod_omega Mon_(n_i)(F_(q_i))`, where
   `Mon_n(F_q) = (F_q^x)^n x| Sym(n)`. Then `rk(x_(g a) - x_(g b)) = 0` for all `g in G`.

   This covers permutation models, point models and a sofic rank function (which does not exist, since
   `W` is not sofic).
4. **Matrix models of `R_p`.** `R_p` has a matrix model if and only if `F_p[W]` has a base-faithful rank
   function approximable over characteristic `p`. So a matrix model of `R_p` proves two things at once:
   - the rank condition for `R_p`, the positive side of `kun-thom-coset-field-crossed-product-has-the-rank-condition`;
   - `F_p`-linear sofic is not equal to sofic, with the finitely generated witness `Q`.
5. **`W` is not sofic.** This follows from `sofic-groups-kill-rigid-compression-defects` applied to the rigid
   pair `Gamma <= G <= W` with `z = x_o`. The defect `x_a x_b^(-1)` is nontrivial because `L` is
   torsion-free, and the argument is the one in `left-orderable-non-sofic-via-integer-lamp-rigid-pair`.
   This answers negatively the one decidable question left by wave 13, namely whether a sofic rank function
   supplies base-faithful ranks.

## Consequences and belief change

- **The earlier kills are explained.** The wave 10 and wave 13 certificate types all kill
  `x_(g a) - x_(g b)`: marked-site maps, jets, augmentation-adic and Frobenius quotients, and point models.
  Part 2 shows this is forced for every approximable certificate if `DD(F_p)` holds. Part 3 forces it
  unconditionally for point and permutation models.
- **The rank condition for `R_p` is tied to the win--win `F_p` rank row.**
  - If `DD(F_p-linear sofic)` holds, any proof of the rank condition for `R_p` must be non-approximable,
    a "characteristic-`p` von Neumann" dimension.
  - Any matrix model of `R_p` gives both the rank condition and a new separation of approximation classes.
- **Characteristic 0.** The von Neumann rank on `C[W]` comes from `L^inf(T^X) x| G`, where `x_c` acts as a
  coordinate. A nonzero Laurent polynomial is nonzero almost everywhere on `T^X`, so this rank is
  base-faithful. By part 1, if it is approximable over characteristic 0, then `C`-linear sofic is not equal
  to sofic. Elek--Szabo approximability of the von Neumann rank needs soficity, which `W` lacks (part 5).
  So in characteristic 0 the rank condition holds through a certificate that is non-approximable or
  answers Arzhantseva--Paunescu.

## What is left

- **Positive direction.** Build a base-faithful non-approximable rank function on `F_p[W]`. The named
  candidate is the characteristic-`p` Sylvester rank on `L^0(Omega, F_p((t))) x| G`, with `Omega` iid Haar
  on `F_p[[t]]^X`. Any construction must pass through a rank that no char-`p` matrix model realizes, unless
  `DD(F_p)` fails.
- **Negative direction.** A diagonal factorization `diag(s_1..s_d) = A'B'` through `F_p[W]^r`, as in
  `coset-field-rank-certificates-need-base-faithful-lamp-ranks`, would refute Seward's conjecture.
  Part 2 does not bear on it.

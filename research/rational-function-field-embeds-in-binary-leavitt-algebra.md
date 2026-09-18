---
rg: 2
id: rational-function-field-embeds-in-binary-leavitt-algebra
kind: claim
title: The rational function field F_2(t) embeds as a unital subring of the binary Leavitt algebra L_(F_2)(1,2)
distinct_from:
  char-two-laurent-linear-groups-satisfy-boone-higman: that places the Laurent ring F_q[t,t^-1] inside the binary Leavitt algebra; this asks for the fraction field, with an inverse for every nonzero polynomial.
  weyl-algebra-blocks-a-universal-leavitt-host: that excludes the first Weyl algebra from L_K(1,2) in characteristic zero; this asks about a commutative field in characteristic two, where no such exclusion is known.
---

**OPEN.** There is an element `x` of `R = L_(F_2)(1,2)` such that `f(x)` is
invertible in `R` for every nonzero `f in F_2[X]`. Equivalently, `F_2(t)` embeds
as a unital subring of `R`. Such an `x` is automatically transcendental over
`F_2`. Since `M_n(R) ≅ R`, a unital embedding into a corner `eRe` would also
suffice.

**Why it matters.** With `leavitt-subalgebra-linear-groups-satisfy-boone-higman`
it gives `gl-n-f2t-embeds-in-fp-simple-group` for every `n`, by route
`gl-n-f2t-bh-via-leavitt-field`.

## Attempts

Notation: `R = F_2<s_0,s_1,t_0,t_1 | t_a s_b = delta_ab, s_0 t_0 + s_1 t_1 = 1>`.
It is `Z`-graded with `deg s_a = 1` and `deg t_a = -1`, the relations being
homogeneous, and `R_d` is spanned by the `s_mu t_nu` with `|mu| - |nu| = d`.

1. **Degree-sign lemma (proved, 2026-09-17, lane `gq-countable-fields`).** If `x`
   lies in `⊕_(d <= 0) R_d` or in `⊕_(d >= 0) R_d`, then some nonzero `f` has `f(x)`
   non-invertible. So a generator of `F_2(t)` needs nonzero components in both
   strictly positive and strictly negative degree. In particular it cannot lie
   in the locally matricial part `R_0`.
   - *The module.* Let `Ω` be the binary sequences with finitely many zeros,
     and `M` the `F_2`-space with basis `e_w`, `w in Ω`. Put `s_a e_w = e_(aw)`,
     and `t_a e_w = e_(w')` if `w = a w'`, else `0`. Then `t_a s_b = delta_ab` and
     `s_0 t_0 + s_1 t_1 = 1` hold on `M`, so `M` is a unital `R`-module.
   - *Finite invariant subspaces.* Let `l(w)` be the least `|gamma|` with
     `w = gamma 1^∞`, and `M_k = span{e_w : l(w) <= k}`, which is finite-dimensional.
     A monomial `s_mu t_nu` with `|mu| <= |nu|` sends `e_w` either to `0` or, when
     `w = nu w'`, to `e_(mu w')` with `l(mu w') <= |mu| + max(0, l(w) - |nu|) <= max(|mu|, l(w))`.
     So for `x in ⊕_(d<=0) R_d` and `k >= max |mu|` over the monomials of `x`, we
     have `x M_k <= M_k`.
   - *Conclusion.* The characteristic polynomial `f` of `x` on `M_k` satisfies
     `f(x) e_(1^∞) = 0` (Cayley--Hamilton), so `f(x)` is not invertible.
   - *The other sign.* The anti-automorphism `s_a <-> t_a` of `R` preserves the
     relations, maps `R_d` to `R_(-d)`, and sends `f(x)` to `f(x*)`, which reduces
     `⊕_(d >= 0)` to `⊕_(d <= 0)`.
2. **Prefix-exchange units fail when they have a periodic point.** A unit
   `u = sum_i s_(mu_i) t_(nu_i)`, where the `nu_i` and the `mu_i` form complete
   prefix codes, is a copy of an element of Thompson's `V`. It acts on the module
   spanned by one tail-equivalence class by `e_w |-> e_(u(w))`. If `u^k(p) = p`,
   then `(1 + u^k) e_p = 0`, so `f = 1 + X^k` fails. Brin's revealing pairs give
   every element of `V` a periodic point, but this was not re-checked here.
3. **Characteristic zero contrast.** Over `C` the analogue fails. `L_C(1,2)`
   embeds unitally in the Cuntz algebra `O_2`, injectively because it is simple.
   Every element of a unital Banach algebra has nonempty spectrum, so for every
   `x` some `x - lambda` is non-invertible, and `C(X)` does not embed as a unital
   `C`-subalgebra. The same
   Banach-algebra mechanism drives Bilich--Hazrat--Nam's exclusion of the Weyl
   algebra. It has no analogue over `F_2`, and arXiv:2512.09241v2 says nothing
   about rational function fields.

**Where it stands.** Every `x` tested so far has a finite-dimensional invariant
subspace in some Chen module (point module). Whether every element of `R`
has one, which would refute the claim, is the natural next question.

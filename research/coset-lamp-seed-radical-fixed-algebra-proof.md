---
rg: 2
id: coset-lamp-seed-radical-fixed-algebra-proof
kind: route
title: Color cosets by translates of the invariant set, and read the dual shift back as an action
target: coset-lamp-seed-radical-is-ce-fixed-algebra-rigidity
requires:
  - semidirect-seed-radical-is-ce-dual-measure-test
  - central-d8-mark-radical-equals-seed-radical
artifacts:
  - research/artifacts/seed-radical-transfer-2026-09-16.md
---

Full proof: Section 3 of the artifact.

**(C1), self-contained.**

1. Replace `E` by `E' = intersect_(c in C) cE`. This set is exactly `C`-invariant, equals `E` mod null, and
   `kappa(aE' triangle E') > 0`.
2. `Phi(z)(b x_0) = 1_(E')(b^(-1) z)` is well defined because `E'` is `C`-invariant. It is Borel, and
   `Phi(dz) = d.Phi(z)` for the shift `(d.f)(x) = f(d^(-1) x)`.
3. `F_l(z) = (-1)^(sum_x l(x) Phi(z)(x))` are commuting self-adjoint unitaries with `F_l F_(l') = F_(l+l')` and
   `u_d F_l u_d^* = F_l o d^(-1) = F_(d.l)`. So `(l,d) -> F_l u_d` is a homomorphism.
4. `F_(m_a) = (-1)^(1_(E') + 1_(aE')) = 1 - 2 . 1_(E' triangle aE')` has `||F_(m_a) - 1||_2^2 = 4 kappa(E' triangle aE') > 0`.
   A trace-preserving embedding of the crossed product finishes.

**(C2), from `semidirect-seed-radical-is-ce-dual-measure-test` (B2).** The characters of `L` are
`chi_f(l) = (-1)^(sum f l)`, `f in F_2^X`, and the dual action is the shift. With `E = {f(x_0) = 1}`, we have `cE = E`
for `c in C`, `aE = {g(a x_0) = 1}`, and `E triangle aE = {chi_f(m_a) = -1}`, which has positive measure for the
measure produced by (B2).

**(C3), self-contained.** Given `theta : H -> U(Q)` with `theta(h) != 1`, put `Pi(k) = diag(theta(k), theta(tkt))`
and `Pi(tk) = T Pi(k)`, with `T = [[0,1],[1,0]]`. Using `t^2 = 1` and `diag(x,y) T = T diag(y,x)`, the four product
cases `k.k'`, `k.tk'`, `tk.k'` and `tk.tk'` check directly. So `Pi : G -> U(M_2(Q))` is a homomorphism with
`Pi(h) != 1`. For the lamp group use `H = L_0 rtimes A` and `t = delta_(x_0)`.

**Equivalences.** Clauses 1 and 5 are equivalent by (C1) and (C2). The step from invariant sets to invariant
algebras holds because `L^infinity(Z)^C` is generated in norm by its projections, which are the indicators of
`C`-invariant-mod-null sets. Clauses 1 and 2 are equivalent by (C3). Clauses 3 and 4 follow from clauses 1 and 2
by `central-d8-mark-radical-equals-seed-radical`.

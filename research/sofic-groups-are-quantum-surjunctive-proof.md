---
rg: 2
id: sofic-groups-are-quantum-surjunctive-proof
kind: route
title: Transplant the local rule to a sofic model and pack disjoint defect copies into a small relative commutant
target: sofic-groups-are-quantum-surjunctive
requires:
  - quantum-endomorphisms-split-off-their-relative-commutant
artifacts:
  - experiments/quantum-surjunctivity-2026-09-17/clifford_star_f2.py
---

**Input.** From the required claim:
- `Phi` is not onto if and only if the defect algebra `F` is not `C`.
- `F` is a finite-dimensional C*-algebra inside `A_W` with `W = N^-1 N`, and `F` commutes with `Phi(A)`.

Suppose `Phi` is not onto, so `dim F >= 2`. Fix `eps > 0` with `eps (2|W|^2 log d + log 2) < log 2`, and let
`K = (N u N^-1)^8`. Since `e` is in `N`, `K` contains `N`, `N^-1`, `W`, `N N^-1`, `W N^-1` and all products of
two of them.

**Sofic model.** Take a finite set `V` and a map `sigma : G -> Sym(V)` such that at least `(1 - eps)|V|` points `v`
are *good*:
- `sigma(g) sigma(h) v = sigma(gh) v` for `g, h` in `K`;
- `sigma(e) v = v`;
- `g -> sigma(g) v` is injective on `K`.

Write `v.g = sigma(g^-1) v`. For good `v` and `g, h` with `g, h, gh` in `K`, `(v.g).h = v.(gh)`. Let `V_1` be the
set of good points.

**Charts.** For good `v` and finite `L <= K`, the map `t -> v.t` is injective on `L`. Let `iota_v : A_L -> A_(v.L)`
be the *-isomorphism that moves the tensor factor at `t` to the factor at `v.t`. All factors are the same `M_d`.

**Step 1 (transplanted rule).** For good `v` define `Psi_v : M_d -> A_(v.N)` by `Psi_v(x) = iota_v(Phi(x_e))`,
where `x_e` is `x` placed at site `e`.
- Let `v != w` be good with `v.N` meeting `w.N`, so `v.n = w.m` for some `n, m` in `N`.
- Multiplicativity at `w` gives `w = sigma(m) sigma(m^-1) w = sigma(m) sigma(n^-1) v`. Multiplicativity at `v`
  gives `w = sigma(m n^-1) v = v.h` with `h = n m^-1` in `N N^-1`, and `h != e`.
- For `y` in `A_N`, `iota_w(y)` puts site `n'` at `(v.h).n' = v.(h n')`. So `iota_w(y) = iota_v(alpha_h(y))`, with
  `iota_v` defined on `N u hN <= K`.
- Hence `Psi_w(M_d) = iota_v(Phi(A_h))`. It commutes with `Psi_v(M_d) = iota_v(Phi(A_e))`, because `Phi(A_h)` and
  `Phi(A_e)` commute and `iota_v` is a *-isomorphism on `A_(N u hN)`.
- If `v.N` and `w.N` are disjoint, the two images commute trivially.

So the `Psi_v` combine into a unital *-homomorphism `Psi : A_(V_1) -> A_V`. It is injective, because `A_(V_1)` is
a full matrix algebra.

**Step 2 (small commutant).** `Psi(A_(V_1))` is a unital copy of `M_(d^|V_1|)` inside `A_V = M_(d^|V|)`. So
`C = Psi(A_(V_1))' n A_V` is `M_(d^(|V| - |V_1|))`, and `dim C <= d^(2 eps |V|)`.

**Step 3 (defect copies lie in C).** For good `v` let `F_v = iota_v(F) <= A_(v.W)`. This is a unital copy of `F`.
- Let `w` be good with `w.N` meeting `v.W`. As in Step 1, `w = v.h` with `h` in `W N^-1`, and
  `Psi_w(M_d) = iota_v(Phi(A_h))` on `W u hN <= K`.
- `F` commutes with `Phi(A_h)`, so `F_v` commutes with `Psi_w(M_d)`. Every other `Psi_w(M_d)` has support disjoint
  from `v.W`.
- So `F_v <= C`.

**Step 4 (packing).** Choose `P <= V_1` maximal with the sets `v.W`, `v` in `P`, pairwise disjoint.
- Every good `w` has `w.W` meeting some `v.W` with `v` in `P`, so `w = v.h` with `h` in `W W^-1`.
- Hence `|V_1| <= |P| |W|^2` and `|P| >= (1 - eps)|V| / |W|^2`.
- The algebras `F_v`, `v` in `P`, have disjoint supports, so they generate their tensor product inside `C`.
- That product has dimension at least `2^|P|`. Therefore `(1 - eps)|V| log 2 / |W|^2 <= 2 eps |V| log d`, which
  contradicts the choice of `eps`.

So `F = C` and `Phi` is onto. The inverse `Phi^-1` commutes with the shift. It has finite propagation because
`A_e <= Phi(A_(N^-1))`, by Step 3 of the required claim's proof, so `Phi^-1(A_e) <= A_(N^-1)`.

**Amenable remark.** For a Folner set `L`, apply the same count to `Phi` restricted to the sites `h` with
`hN <= L`, inside `A_L`. The boundary `|L \ {h : hN <= L}|` is `o(|L|)`. The count is identical, and no entropy
theory is needed.

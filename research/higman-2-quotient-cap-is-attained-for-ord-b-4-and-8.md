---
rg: 2
id: higman-2-quotient-cap-is-attained-for-ord-b-4-and-8
kind: claim
title: In the finite 2-quotients of H4(3)/<<[a,c]^2>> the cap ord(a) <= 64 ord(b) is attained for ord(b) = 4 and 8 (ord(a) = 256 and 512), and for k = 1, 2, 3 already in the quotient of G/<<b^(2^k)>> by [b,d,d] and [b,d]^(2^(k+1)); there [b,d]^(2^k) loses a doubling
distinct_from:
  higman-2-quotient-order-cap-is-attained-for-small-ord-b: that proves the cap and attains it for ord(b) <= 2 and leaves k = 2 open (ord(a) = 128 at class 13 of G''/<<b^4>>); this attains it for ord(b) = 4 and 8, gives a certified pc model for ord(b) = 4, and finds one relator family X_k that attains it for k = 1, 2, 3.
  higman-power-pair-collapse-is-base-uniform-up-to-torsion: that asks whether a has infinite order in the pro-2 completion of H4(3)/<<[a,c]^2>>; this does not settle it, but reduces it to the cap for the explicit family X_k for all k.
  higman-j-odometer-models-restrict-to-single-cycle-models: that finds ord(a) = 128 in the full class-11 2-quotient; this attains the cap ord(a) = 64 ord(b) at ord(b) = 4 and 8.
  higman-a-has-order-2e-in-gamma-3-2e-mod-r-for-e-le-10: that finds ord(a) = 2^10 in quotients of Gamma(3,2^e)/<<[a,c]^2>>, with ord(b) not fixed (the cap forces ord(b) >= 16); this fixes ord(b) = 2^k and shows the ratio ord(a)/ord(b) = 64 is attained for k = 2, 3.
artifacts:
  - experiments/higman-k2-cap-2026-09-19/run2.sh
  - experiments/higman-k2-cap-2026-09-19/red2.g
  - experiments/higman-k2-cap-2026-09-19/zsq.g
  - experiments/higman-k2-cap-2026-09-19/check-model.g
  - experiments/higman-k2-cap-2026-09-19/probes.txt
  - experiments/higman-k2-cap-2026-09-19/collect.txt
  - experiments/higman-k2-cap-2026-09-19/logs.txt
  - experiments/higman-k2-cap-2026-09-19/mono4.g
  - experiments/higman-k2-cap-2026-09-19/k2-pc.g
---

**ESTABLISHED** (proposed; item 1 certified by an explicit pc group, items 2 to 4 computed with the ANU
p-quotient program) by `higman-2-quotient-cap-is-attained-for-ord-b-4-and-8-proof`.

**Setting.** As in `higman-2-quotient-order-cap-is-attained-for-small-ord-b`:
- `G = H4(3)/<<[a,c]^2>>`, with `x^y = y^-1 x y`;
- `Gamma_k = G/<<b^(2^k)>>`;
- `G'' = G/<<[b,d]^2>>`;
- `P_cl(X)` is the class-`cl` lower exponent-2 central quotient of `X`;
- commutators are left-normed, so `[b,d,d] = [[b,d],d]`.

The cap is `ord(a) | 2^(k+6)` in the 2-quotients of `Gamma_k` (`k >= 1`).

**Statement.**
1. **k = 2.** `Gamma_2` has a finite 2-quotient with orders `(a,b,c,d) = (256,4,16,64)`, so all four
   generators are at their caps. A monolithic pc group of order `2^146` with these orders
   (socle `<a^128>`) is saved as `k2-pc.g` and rechecked by `check-model.g`, including consistency
   of its presentation.
2. **k = 3.** `P_16(Gamma_3)` (order `2^16535`) has `a^256 != 1`, so `ord(a) = 512 = 2^(3+6)` and the cap is
   attained for `ord(b) = 8`. (Larger `ord(a)` is known, up to `2^10`, from
   `higman-a-has-order-2e-in-gamma-3-2e-mod-r-for-e-le-10`, but there `ord(b) >= 16` by the cap.)
   - `P_15(G)` (order `2^11776`) still has `a^256 = 1`.
   - So the first class where `ord(a)` reaches the cap is 12, 14, 16 for `k = 1, 2, 3`.
3. **A uniform family.** Let `X_k = Gamma_k/<<[b,d,d], [b,d]^(2^(k+1)), [a,c^2]^8>>`. Then
   `P_(2k+10)(X_k)` has `ord(a) = 2^(k+6)` for `k = 1, 2, 3`:
   - `k = 1`: `P_12(X_1)` has order `2^404` and `a^64 != 1`;
   - `k = 2`: `P_14(X_2)` has order `2^1221` and `a^128 != 1`;
   - `k = 3`: `P_16(X_3)` has order `2^3551` and `a^256 != 1`.

   Replacing `[b,d]^(2^(k+1))` by `[b,d]^(2^k)` gives `a^(2^(k+5)) = 1` in `P_(2k+10)`, for
   `k = 1, 2, 3` (orders `2^401`, `2^1206`, `2^3529`). So in this family `[b,d]` must have order `2^(k+1) = 2 ord(b)`.

   For `k = 4` the pattern breaks at class `2k+10 = 18`. `P_18(X_4)` has order `2^10125`, with
   `a^256 != 1` (first at class 16) but `a^512 = 1`. So there `ord(a) = 512`, one doubling short of
   the cap `1024`. Class 19 does not finish within 20 minutes.
4. **Symmetric quotient.** `ord(a)` in `P_cl(G'')` stays 128 through class 16 (order `2^6968`). In
   `P_cl(G''/<<b^4>>)` it stays 128 through class 18 (`2^14088`). In `P_cl(G''/<<b^2>>)` it stays 64
   through class 15. So `[b,d]^2 = 1` costs one doubling for `ord(b) = 2, 4`.
5. **Killers.** Adding any one of the following to `X_2` gives `a^128 = 1` at class 14 (table in
   `probes.txt`):
   - `[b,d,b]`, `[b,d,a]`, `[b,d,c]`, `[b,d,c^2]`, `[c,d]^16`;
   - `[a,c,c]`, `[a,c,a]`, `[a^2,c]^8`, `[a,d,d]`, `[c,d,c]`;
   - `[a,d]^32`, `[a,d]^64`, `[b,c]^4`, `[a^4,c]^4`.

   Each was added to `X_2` or to a group mapping onto `X_2`, so it kills in `X_2`. In particular `[b,d]`
   cannot be made central: `[b,d,b]`, `[b,d,a]` and `[b,d,c]` each kill.

**Reduction.** If some family of 2-quotients of `Gamma_k` attains the cap for every `k` (for example `X_k`), then `ord(a)` is unbounded in the finite
2-quotients of `G`, and `a` has infinite order in the pro-2 completion. This now holds for `k <= 3`.
For `X_4` it fails at class 18 (item 3).
In `X_k` the subgroup `<d, [b,d]>` is abelian. The lift `X_k -> X_(k+1)` has to
double `ord(b)` and `ord([b,d])` together.

**Dead.**
- Direct monolithic reduction (GAP's `EpimorphismPGroup`, or `Center` on the `2^1221` group) does
  not finish in 20 minutes.
- `z = a^128` lies in `gamma_I(P)^2` for `I <= 12`, so the linear reduction must use `I = 13`.

**Next.**
- Decide whether `X_4` attains the cap `ord(a) = 1024` at some class `>= 19`, or whether the family
  needs one more relator (or one fewer) from `k = 4` on.
- Look for the lift `X_k -> X_(k+1)` on the abelian subgroup `<d, [b,d]>` in the certified `2^146`
  model and in `X_3`.

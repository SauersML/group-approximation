# Referee report (gq-referee-c): finitely-presented-divisible-ring-engine

- **Node:** `research/finitely-presented-divisible-ring-engine.md` and its `-proof` route. They were landed
  7d1469960 on 2026-09-17 by another session, before the gq swarm.
- **Lens:** independent re-derivation. I also checked the Leavitt pair used by
  `one-steinberg-group-contains-every-gl-n-q`.
- **Verdict: PASS.** The following are all correct:
  - `D` is nonzero;
  - `Q ⊆ Z(D)` unitally;
  - `(w, v)`, `(sw, vt)` is a binary Leavitt pair;
  - the coproduct corollary.

`D = Z<s,t,w,v,b,a | st = ts = 1, vw = 1, s(wv)t = 1 - wv, b(wv) = (wv)b, vbw = b + 1, b(1-wv) = 1 - wv, ab = 1>`.
Write `q = wv`, which is idempotent by R2, and `o = 1 - q`.

## 1. Every integer is a central unit

- `bw = b(wv)w = (qb)w = w(vbw) = w(b+1)` by R2, R4 and R5. By induction, `b w^k = w^k (b+k)`.
- `c_k = v^k a w^k` satisfies `c_k (b+k) = v^k a b w^k = v^k w^k = 1` by R7 and R2. So `c_k` is a *left* inverse
  of `b+k`. The proof calls it a "right inverse". That is naming only; the computation is right.
- R6 gives `(b+k) o = (k+1) o`. So `(k+1) c_k o = c_k (b+k) o = o`, using that `k+1` is central.
- R1 and R3 give `s o t = st - sqt = q`.
- So `y_k = c_k o + s c_k o t` satisfies `(k+1) y_k = o + q = 1`. Since `k+1` is central, `y_k` is a two-sided
  inverse, and it is central.

So `Z -> D` extends to `Q -> Z(D)`. ✓

## 2. D ≠ 0 (the operator model)

On `Q^(Z \ {0})`:
- `s = t` is the involution `σ : 2m ↔ 2m-1`, `-2m ↔ -(2m-1)`, which swaps parity;
- `w e_x = e_(2x)`;
- `v e_(2x) = e_x` and `v e_(odd) = 0`;
- `b = ν_2 + 1` and `a = b^(-1)`, both diagonal.

The relations check one by one:
- **R1:** `σ^2 = 1`.
- **R2:** clear from the definitions of `v` and `w`.
- **R3:** `q` projects onto the even basis vectors, and `σ q σ` projects onto the odd ones, which is `1 - q`.
- **R4:** both `b` and `q` are diagonal.
- **R5:** `vbw e_x = (ν_2(2x)+1) e_x = (b+1) e_x`.
- **R6:** `b = 1` on odd `x`, and `1 - q = 0` on even `x`.
- **R7:** `a` is the inverse diagonal of `b`.

So `D ≠ 0`, and `Q -> D` is injective. ✓

## 3. The binary Leavitt pair x_1 = w, y_1 = v, x_2 = sw, y_2 = vt

- `y_1 x_1 = vw = 1`, and `y_2 x_2 = v(ts)w = vw = 1`.
- `x_1 y_1 + x_2 y_2 = q + s q t = q + (1 - q) = 1`, by R3.
- The cross terms vanish in any ring once `y_i x_i = 1` and `Σ x_i y_i = 1`:
  `y_1 x_2 = y_1 (x_1 y_1 + x_2 y_2) x_2 = y_1 x_2 + y_1 x_2`, so `y_1 x_2 = 0`. The same argument gives
  `y_2 x_1 = 0`.
  - The node's route to the same conclusion (`sw = (1-wv)sw` and `vt = vt(1-wv)`) is also correct.

## 4. Coproduct corollary

- `R *_Z D` is presented by the union of the two presentations, so it is finitely presented. It is a
  `Q`-algebra because it receives `D`.
- The two actions on `(R ⊗ Q) ⊗_Q V` need not commute: the coproduct's universal property needs only two ring
  maps into `End_Z(M)`.
- `r ↦ L_r ⊗ id` is injective for torsion-free `R`. ✓

## 5. Calibration

- R5 (shift) and R6 (vacuum on `1 - wv`) play the roles of `N s_1 = s_1(N+1)` and `N s_2 = 0` in `R_L` (see
  `gq-referee-c-leavitt-resolvent-ring-is-fp-simple-of-char-zero.md`, §4). Dropping either one allows a
  characteristic-`p` model:
  - without R6, set `b = z + ν_2` over `F_p(z)`;
  - without R5, the ring maps to one where `b = a = 1` and `w, v` are arbitrary.
- `D` is not claimed simple, and it is not used as a simple host. `one-steinberg-group-contains-every-gl-n-q`
  needs only `Q ⊆ D` and the Leavitt pair.

---
rg: 2
id: constant-length-substitution-tower-partition-proof
kind: route
title: Bilateral recognizability makes the cutting phase a continuous Z/q-valued function, and unique desubstitution inverts ζ
target: constant-length-substitution-tower-partition
requires: [mosse-bilateral-recognizability]
---

Let `L` work for both of Mossé's theorems.
1. **Equivariance.** `ζ(x)` places `ζ(x_k)` at `[qk, qk+q−1]`, so `ζ(Tx) = T^qζ(x)`.
2. **Phase.**
   - For `x ∈ X` and `i ∈ Z`, the window `x[i−L,i+L]` is a word of `L_u`, occurring at some rank `j` of `u`. Declare `i` a cut of `x` if `j + L ∈ E_1`. By bilateral recognizability this does not depend on the occurrence chosen, and it is locally constant in `x`.
   - The cuts of a shifted point `T^m u′`, where `u′` is a two-sided sequence built from the fixed point, form a coset of `qZ`. The two-sided extension through a legal two-letter word `σ^∞(b).σ^∞(a)`, with `ba` in the language, uses `σ(b)` and `σ(a)` beginning and ending appropriately; replace `σ` by a power if needed (Mossé p. 334).
   - Cuts are defined by windows, and every `x ∈ X` is a limit of such points, so the cut set of `x` is `qZ + p(x)`. Here `p: X → Z/q` is continuous and `p(Tx) = p(x) − 1`.
   - So `V_0 = {p = 0}` is clopen and `X = ⊔_(k<q) T^k V_0`.
3. **`ζ(X) = V_0`.**
   - `⊆`: blocks of `ζ(y)` are aligned with `qZ`, and windows of `ζ(y)` occur in `u` at cut-compatible ranks (since `u = ζ(u)`).
   - `⊇`: if `x ∈ V_0`, unique desubstitution (Theorem 2) gives, for each `k`, the letter `y_k` with `x[qk,qk+q−1] = ζ(y_k)`, determined by a window of bounded radius. Every window of `y` is a word from which a window of `x` comes, hence it lies in `L_u`, so `y ∈ X` and `ζ(y) = x`.
4. **Inverse.** The map `x ↦ y` is continuous (locally determined). It inverts `ζ`, because Theorem 2 makes the source word unique, so `ζ` is injective.

**Backup for Thue–Morse (elementary).** The language has no overlaps, so `000` and `111` never occur, and every window of length 5 contains `00` or `11`. In a concatenation of the blocks `01` and `10`, `00` and `11` occur only across a block boundary. So the phase is read off any length-5 window, and desubstitution is `01 ↦ 0`, `10 ↦ 1`.

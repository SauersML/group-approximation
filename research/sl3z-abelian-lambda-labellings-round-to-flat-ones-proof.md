---
rg: 2
id: sl3z-abelian-lambda-labellings-round-to-flat-ones-proof
kind: route
title: Pass to the Loeb limit, integrate the cocycle by Delorme-Guichardet, clamp the potential, and pull it back internally
target: sl3z-abelian-lambda-labellings-round-to-flat-ones
requires: []
---

Recalled standard inputs, not imported as nodes: Kazhdan's property (T) for `SL_3(Z)`; Delorme–Guichardet
(for a group with (T), `H^1(Γ, π) = 0` for every orthogonal representation `π`); the Loeb measure construction,
with the fact that every Loeb-measurable set agrees a.e. with an internal set.

Fix a basis `a_1, …, a_r` of `A ≅ Z^r` and write labels additively as vectors. Let `M` bound the coordinates of
`Σ`, and `C = max_i log max(||a_i||, ||a_i^(−1)||)`, so `log(||λ|| ||λ^(−1)||) <= 2C|λ|_1`.

1. **Contradiction set-up.** If the theorem fails for `Σ`, there are `c > 0`, finite `Γ`-sets `V_k` and
   `λ_k : V_k × S → Σ` whose non-flat cells number `δ_k|V_k|` with `δ_k → 0`, such that every flat `λ'` has
   `cost(λ_k, λ') >= c|V_k|`.
2. **Loeb cocycle.** Fix a non-principal ultrafilter `U` and let `(Z, μ)` be the Loeb space of the internal sets `V_k`
   with normalized counting measure. `Γ` acts by measure-preserving maps. The internal function `λ_k(·, s)`
   takes finitely many values and defines `w(s, ·) : Z → Z^r`. Each relator cell is non-flat only on an internal
   set of normalized size at most `δ_k → 0`, so the relators of `R` hold for `w` `μ`-a.e. Hence `w` extends
   by the words to a cocycle `w : Γ × Z → Z^r`, defined a.e., with `|w(s, ·)|_∞ <= M` for `s ∈ S`.
3. **Integration.** For each coordinate `i`, the map `b_i(g)(z) = w_i(g, g^(−1)z)` lies in `L²(Z, μ; R)`, since it is
   bounded on generators and so on every `g`. It is a 1-cocycle for the Koopman representation `(π(g)f)(z) = f(g^(−1)z)`.
   By Delorme–Guichardet there is `f_i ∈ L²` with `w_i(g, z) = f_i(gz) − f_i(z)` a.e. Then `f_i mod 1` is
   `Γ`-invariant a.e. Subtract an invariant representative to get an integer-valued `F_i` with `dF_i = w_i` a.e.
4. **Clamping.** Given `ε > 0`, pick `T` with `μ(|F_i| >= T − M) <= ε` for all `i`, and put `F_i^T = max(−T, min(T, F_i))`.
   Clamping is 1-Lipschitz, so `|dF_i^T(s,z)| <= M` a.e. Also `dF_i^T(s, z) = w_i(s, z)` unless `|F_i(z)| >= T − M`
   or `|F_i(sz)| >= T − M`, a set of measure at most `2ε`.
5. **Internal pull-back.** `F^T` takes finitely many values, so it is a.e. equal to an internal
   `F_k : V_k → [−T, T]^r`. Put `λ'_k(v,s) = F_k(sv) − F_k(v)`. This is a coboundary, hence flat. The internal set
   where `λ'_k != λ_k` has Loeb measure at most `2r|S|ε`. On it `|λ'_k|_1 <= rM`, except on an internal set of
   Loeb measure zero, where `|λ'_k|_1 <= 2rT`. So

   ```text
   st( cost(λ_k, λ'_k) / |V_k| )  <=  2r|S|ε (1 + 2CrM)  +  0 · (1 + 4CrT).
   ```

   For `ε` small this is below `c`, so for `U`-most `k` we get `cost(λ_k, λ'_k) < c|V_k|`, contradicting step 1. ∎

**Calibration.**
- *(T) is needed.* For `Γ = Z² = ⟨a, b | [a,b]⟩` on `V = (Z/N)²` with `λ = 1` on `a`-edges and `0` on `b`-edges,
  `λ` is flat but not a coboundary. There `H^1(Γ_v; Z) != 0` and step 3 fails; it is the sole use of (T).
- *Torsion-freeness is needed.* For `A = Z/2` in step 3 the coordinates are not real-valued, and the statement
  becomes a `Z/2`-cosystolic-expansion question about the Schreier complexes, which this proof does not touch.

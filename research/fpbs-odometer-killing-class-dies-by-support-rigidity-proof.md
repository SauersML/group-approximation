---
rg: 2
id: fpbs-odometer-killing-class-dies-by-support-rigidity-proof
kind: route
title: Proof that the odometer killing-word sign coding is two-sided injective (paperfolding recognizability with a fixed majority margin), so the odometer class and every class on its rays has totally dissipative diagonal
target: fpbs-odometer-killing-class-dies-by-support-rigidity
requires:
  - fpbs-zero-entropy-ray-codes-are-support-rigid
  - fpbs-quasiconvex-null-small-classes-exist-on-free-boundary
---

# Proof

**Notation.** The notation is that of `fpbs-quasiconvex-null-small-classes-exist-on-free-boundary-proof` (Step 2):
- `q_n = 2^{n+2}`, `Omega = lim Z/q_n = Z_2` (the dyadic integers), Haar measure `m`, `T x = x + 1`;
- `F_n : Z/q_n -> {a, A, b, B, hole}` are the stage labellings, and `F = lim F_n` a.e.;
- the stage-`n_j` windows have starts `r_j` and killing words `k_j` of length `l_j`.

Admissible choices (A1)--(A3) are as in the claim. For `y ∈ Omega \ {0}` write `y = 2^k u` with `k = v_2(y)` and `u`
a unit. Put `chi(u) = +1` if `u ≡ 1 mod 4` and `chi(u) = -1` if `u ≡ 3 mod 4`, and `p(y) = chi(y / 2^{v_2(y)})`: the
**regular paperfolding** signs. For `k >= 0` put

`class_k = {y ∈ Omega : v_2(y) = k} = {y ≡ 2^k mod 2^{k+1}}`, with `m(class_k) = 2^{-(k+1)}`.

The **window set** is `W_j = {y : y mod q_{n_j} ∈ ±[r_j, r_j + l_j)}` and `Ov = ⋃_j W_j`. For a Borel `E` and a
class `C` of positive measure write `m(E | C) = m(E ∩ C) / m(C)`.

## Step 1. Off the windows the signs are paperfolding

**Lemma 1.1.** For a.e. `y`, if `y ∉ Ov` then `s(y) = p(y)`.

*Proof.* Say `y ≠ 0` (a null set is excluded) and `k = v_2(y)`.

*Unperturbed value.* If `k = 0`, then `F_0(y mod 4)` is `b` for `y ≡ 1` and `B` for `y ≡ 3`, and lifting keeps it.
So the Toeplitz value has sign `chi(y) = p(y)`. If `k >= 1`, then `y` is a stage-`n` hole exactly when
`y ≡ 0` or `q_n / 2 = 2^{n+1} mod 2^{n+2}`, that is, when `k >= n+1`. So `y` is filled at the Toeplitz step
`n -> n+1` with `n + 1 = k`. There `y ≡ q_{n+1}/4 = 2^k mod 2^{k+2}` (when `u ≡ 1 mod 4`) receives `a`, and
`y ≡ 3 q_{n+1}/4 = 3 · 2^k mod 2^{k+2}` (when `u ≡ 3 mod 4`) receives `a^{-1} = A`, by (A1). The sign is `chi(u) = p(y)`.

*No other change.* After it is filled, the value at `y` changes only by an overwrite. Overwrites at stage `n_j` touch
exactly the residues `±[r_j, r_j + l_j) mod q_{n_j}`, which never contain a stage-`n_j` hole. Later holes are
`≡ 0 mod q_{n_j}`, outside every stage-`n_j` window. If `y ∉ Ov`, no overwrite touches `y`, and the limit `F(y)`
exists a.e. (Borel--Cantelli, as in that proof) and equals the Toeplitz value. `□`

(The same computation shows that `p` is odd, `p(-y) = -p(y)`, matching (S).)

## Step 2. The windows are sparse in every class

**Lemma 2.1.** Assume (A2) and (A3), and put `delta = sum_j 2 l_j / q_{n_j}`. Then:
1. `W_j ∩ class_k = ∅` whenever `k >= n_j - 5`;
2. `eta_k := m(Ov | class_k) <= delta + 2^{-5} <= 1/16` for every `k >= 0`;
3. `m(Ov | even) <= 2 delta <= 1/16`.

*Proof.* (1) Put `q = q_{n_j} = 2^{n_j + 2}` and `M = 2^{n_j - 5}`. Then `q/8 = 2^{n_j - 1}` and `q - q/8` are
multiples of `M`. By (A2), `[r_j, r_j + l_j) ⊂ [q/8 + 1, q/8 + l_j + 1]`, and `l_j + 1 < M`, so the window meets no
multiple of `M`. Its negative lies in `[q - q/8 - l_j - 1, q - q/8 - 1]` and also meets none. Since `M | q`, every `y ∈ W_j`
has `y mod M ≠ 0`, so `v_2(y) < n_j - 5`.

(2) By (1), only the stages with `n_j > k + 5` meet `class_k`. Each such `W_j` is two intervals of length `l_j` per
period `q_{n_j}`. An interval of length `l` contains at most `l / 2^{k+1} + 1` points of `class_k`. The period
contains `q_{n_j} / 2^{k+1}` points of `class_k`. So

`m(W_j | class_k) <= 2 (l_j / 2^{k+1} + 1) / (q_{n_j} / 2^{k+1}) = 2 l_j / q_{n_j} + 2^{k + 2} / q_{n_j}
= 2 l_j / q_{n_j} + 2^{k - n_j}`.

Summing, and using that the `n_j` are distinct integers `> k + 5`,

`eta_k <= delta + 2^k sum_{n > k+5} 2^{-n} = delta + 2^{-5} <= 2^{-4}`.

(3) `m(Ov ∩ even) <= m(Ov) <= delta`, and `m(even) = 1/2`. `□`

## Step 3. The two paperfolding statistics

Let `A = {y : s(y+2) = -s(y)}` and `A_par = {y : p(y+2) = -p(y)}`.

**Lemma 3.1.**
1. `A_par ⊇ odd`, where `odd = class_0`.
2. `m(A_par | even) = 1/2`.

*Proof.* (1) If `y` is odd, `y` and `y + 2` are units whose residues mod 4 differ, so `chi(y+2) = -chi(y)`.

(2) First, `m{t : p(t) = +1} = 1/2`. Conditioned on `v_2(t) = k`, the residue `t mod 2^{k+2}` is uniform on
`{2^k, 3 · 2^k}`, so the sign is `±1` with probability `1/2` each.

Write `y = 2z`. The map `z -> 2z` carries `m` to `m( · | even)`. Since `p(2z) = p(z)` for `z ≠ 0`, we need
`m{z : p(z+1) = -p(z)} = 1/2`. Condition on `z mod 4` and write `t` for the Haar-distributed quotient:
- `z = 4t + 1`: `p(z) = +1`, and `p(z+1) = p(2t+1) = chi(2t+1)`, which is `-1` iff `t` is odd. Probability `1/2`.
- `z = 4t + 3`: `p(z) = -1`, and `p(z+1) = p(4(t+1)) = p(t+1)`, which is `+1` with probability `1/2`.
- `z = 4t`: `p(z+1) = +1`, and `p(z) = p(t)`, which is `-1` with probability `1/2`.
- `z = 4t + 2`: `p(z+1) = -1`, and `p(z) = p(2t+1) = chi(2t+1)`, which is `+1` iff `t` is even. Probability `1/2`.

Each conditional probability is `1/2`. `□`

**Lemma 3.2 (the parity gap).** Under (A1)--(A3):
1. `m(A | odd) >= 7/8`;
2. `m(A | even) <= 5/8`.

*Proof.* By Lemma 1.1, `A` and `A_par` agree a.e. off `D = Ov ∪ (Ov - 2)`. Translation by `2` preserves `odd`,
`even` and `m`. So for `C ∈ {odd, even}`, `m(D | C) <= 2 m(Ov | C)`, and this is `<= 1/8` by Lemma 2.1 (2) with
`k = 0`, and (3). Then
- `m(A | odd) >= m(A_par | odd) - 1/8 = 7/8`, by Lemma 3.1 (1);
- `m(A | even) <= m(A_par | even) + 1/8 = 5/8`, by Lemma 3.1 (2). `□`

## Step 4. The generic set and the decoders

Let `dom` be the conull Borel set on which `F` is defined (Borel--Cantelli). Let `𝓔` be the countable family of Borel
sets

`odd, even, A ∩ odd, A ∩ even, class_k, class_k ∩ Ov (k >= 0)`.

Let `X_0` be the set of `x` such that `x + t ∈ dom` for all `t ∈ Z`, and such that for every `E ∈ 𝓔`

`(1/N) sum_{n=1}^{N} 1_E(x + n) -> m(E)` and `(1/N) sum_{n=0}^{N-1} 1_E(x - n) -> m(E)`.

*`X_0` is Borel, `T`-invariant and conull.* It is defined by countably many Borel conditions. Replacing `x` by
`x ± 1` changes each partial sum by at most 2, so the limits do not change. `T` is an ergodic (indeed uniquely
ergodic) measure-preserving automorphism, and so is `T^{-1}`. Birkhoff's theorem, applied to countably many sets in
each direction, gives `m(X_0) = 1`. Also, `T` is aperiodic on `X_0`, since `x + t ≠ x` for `t ∈ Z \ {0}`.

**The decoders.** Put `d_+(n) = n` for `n >= 1` and `d_-(n) = -n` for `n >= 0`. Given `σ ∈ {±1}^N` and a sign
`e ∈ {+, -}`, the decoder `D_e(σ) ∈ Omega ∪ {fail}` reads `σ_n` as the sign at the offset `d_e(n)`. For `I ⊂ N`
and a predicate `P(n)`, write `fr(P ; I) = liminf_N #{n <= N : n ∈ I, P(n)} / #{n <= N : n ∈ I}`.

1. **Parity.** For `c ∈ {0, 1}` let `I_c = {n : c + d_e(n) odd}`, and put
   `S_c = fr(σ_{n+2} = -σ_n ; I_c)`. If exactly one `c` has `S_c > 3/4`, set `x_0 = c`. Otherwise output `fail`.
2. **Level `k` (for `k = 0, 1, 2, ...`).** Given `ρ = x_k ∈ Z/2^{k+1}`, let
   `I_k(ρ) = {n : ρ + d_e(n) ≡ 2^k mod 2^{k+1}}`. For `ρ' ∈ {ρ, ρ + 2^{k+1}} ⊂ Z/2^{k+2}` and `n ∈ I_k(ρ)`, the residue
   `(ρ' + d_e(n)) mod 2^{k+2}` is `2^k` or `3 · 2^k`. Let the predicted sign `π(ρ', n)` be `+1` or `-1`
   accordingly. Put `Ag(ρ') = fr(σ_n = π(ρ', n) ; I_k(ρ))`. Set `x_{k+1} = ρ` if `Ag(ρ) > 1/2`, and
   `x_{k+1} = ρ + 2^{k+1}` otherwise.
3. Output the point `lim x_k ∈ Omega = lim Z/2^k`.

Each step is a Borel function of `σ`, so `D_e` is Borel. The decoder uses only `σ` and the known offsets, never `x`.

**Proposition 4.1.** For `x ∈ X_0`: `D_+(iota_+(x)) = x` and `D_-(iota_-(x)) = x`.

*Proof.* Take `e = +` and `σ = iota_+(x)`, so `σ_n = s(x + n)`. The backward case is the same and is treated at the
end.

*Parity.* Let `c ≡ x mod 2`. For `n ∈ I_c`, `x + n` is odd; for `n ∈ I_{1-c}`, `x + n` is even. Also
`σ_{n+2} = -σ_n` iff `x + n ∈ A`. Since `x ∈ X_0`, the frequencies are limits:
- `S_c = m(A ∩ odd) / m(odd) >= 7/8`;
- `S_{1-c} = m(A ∩ even) / m(even) <= 5/8`,

by Lemma 3.2. So `x_0 = x mod 2`.

*Level `k`.* Assume `x_k = x mod 2^{k+1}`. Then `n ∈ I_k(x_k)` iff `x + n ∈ class_k`. For such `n`, write
`x + n = 2^k u`. With the true candidate `ρ_* = x mod 2^{k+2}`, `(ρ_* + n) mod 2^{k+2} = 2^k (u mod 4)`, so
`π(ρ_*, n) = chi(u) = p(x + n)`. The other candidate adds `2^{k+1}`, which replaces `u` by `u + 2` mod 4 and flips
`chi`, so `π(ρ_* ± 2^{k+1}, n) = -p(x+n)`. By Lemma 1.1, `σ_n = p(x + n)` unless `x + n ∈ Ov`. Hence

`Ag(ρ_*) >= 1 - m(class_k ∩ Ov) / m(class_k) = 1 - eta_k >= 15/16`, and
`Ag(ρ_* ± 2^{k+1}) = 1 - Ag(ρ_*) <= 1/16`.

These are limits, because `x ∈ X_0`, and the second equality holds because every `n ∈ I_k(x_k)` agrees with exactly
one candidate. The decoder therefore picks `ρ_*`, that is, `x_{k+1} = x mod 2^{k+2}`. By induction `x_k = x mod 2^{k+1}`
for all `k`, and the output is `x`.

*Backward.* Now `σ_n = s(x - n)` for `n >= 0`. Then `σ_{n+2} = -σ_n` iff `x - n - 2 ∈ A`, and `x - n - 2` has the same
parity as `x + d_-(n) = x - n`. The frequencies of `1_E(x - n - 2)` and
`1_E(x - n)` have the same limit, because the sums differ by at most 2 terms. So the backward averages in the
definition of `X_0` give the same numbers `>= 7/8` and `<= 5/8`. The level-`k` step is word for word the same with
`x + n` replaced by `x - n`. `□`

## Step 5. Theorem 1 and the rigidity statements

*Proof of Theorem 1.* By Proposition 4.1, `D_+ ∘ iota_+ = id` and `D_- ∘ iota_- = id` on `X_0`. So both
itineraries are injective on `X_0`. `□`

**Corollary 5.1 (the brief's match rigidity).**
1. `zeta` is injective on `X_0`, and `zeta(X_0)` is Borel.
2. If `x, x' ∈ X_0`, `g ∈ F_2` and `g zeta(x) = zeta(x')`, then `x' ∈ x + Z`.

*Proof.* (1) The letter `F(x+n)` determines its sign `s(x+n)`, so `zeta(x)` determines `iota_+(x)`. Injectivity
follows from Theorem 1. `zeta` is Borel on the Borel set `X_0`, and an injective Borel image of a Borel set is Borel
(Lusin--Souslin).

(2) Write `eta = zeta(x)`. In the tree, reducing `g eta` cancels at most `|g|` letters of `eta`, so
`g eta = g' sigma^{i'} eta` for some `i' <= |g|` and some reduced `g'`, with no cancellation between `g'` and
`sigma^{i'} eta`. Hence `sigma^{|g'|}(g eta) = sigma^{i'} eta`. With `g eta = zeta(x')` and
`sigma^t zeta(y) = zeta(y + t)`, this reads `zeta(x' + |g'|) = zeta(x + i')`. Both points lie in `X_0`, which is
`T`-invariant, so (1) gives `x' + |g'| = x + i'`. `□`

*Proof of Corollary 2 of the claim.* The map `x -> (x, x + 1 mod 2)` embeds `X_0` in `X_0 x Z/2` and intertwines
`T` with `sigma(x, j) = (Tx, j+1)`. In the ray code of `fpbs-zero-entropy-ray-codes-are-support-rigid`, the `n`-th
letter at `(x, j)` is `t_{n+j}^{s(x+n)}`, and `t_{n+j} = a` iff `n + j` is odd. With `j ≡ x + 1`, `n + j` is odd iff
`x + n` is even, which is the type rule (T) of `F`. So `zeta^+(x, x+1) = zeta(x)`, and
`zeta(X_0) ⊂ B = zeta^+(X_0 x Z/2)`. `T` is aperiodic on `X_0`, and `(X_0, T, s)` is two-sided injective by
Theorem 1. So Theorem 2 of that claim applies to every imp `(Z, mu_Z)` whose pushforwards `xi_*(mu_Z|_E)` are nonatomic
and carried by `F_2 zeta(X_0) ⊂ F_2 B`.

It remains to check the example `xi_*(mu_Z|_E) << nu`. The set `U = dF_2 \ F_2 zeta(X_0)` is Borel and
`F_2`-invariant. So `nu(U) = sum_g c_g m(zeta^{-1}(g^{-1} U)) = sum_g c_g m(zeta^{-1}(U))`. Also
`zeta^{-1}(U) ⊂ Omega \ X_0` is null. `nu` is nonatomic because `zeta_* m` is: `zeta` is injective on `X_0` and `m`
is nonatomic. Hence `xi_*(mu_Z|_E) << nu` is nonatomic and carried by `F_2 zeta(X_0)`.

The three bullets follow:
- an ergodic PDR action would have a diagonal that is not totally dissipative;
- the Maharam extension of `[nu]` is an imp action over `[nu]`, via the projection;
- the last bullet is the general hypothesis. `□`

## Remarks

- **The killing words are never used.** Only the geometry of the windows enters, through (A2) and (A3). The words
  `k_j` may be arbitrary. So the proof applies verbatim to any sparse overwrite of the paperfolding skeleton with
  these window positions, including every choice of killing words that Lemma 1 of the odometer node allows.
- **The margins are fixed.** They are `7/8` against `5/8` for parity and `15/16` against `1/16` at every level `k`.
  So the decoder needs only a Birkhoff-generic orbit and no rate of convergence. The level-`k` step reads only the
  offsets in `class_k`, which have density `2^{-(k+1)}`. So finite windows of length `L` determine `x` modulo about
  `L / 2^{O(1)}`. The script's test 3b checks this.
- **Calibration** (`experiments/odometer-match-rigidity-2026-09-17/recognize.py`, output `recognize.out`). On
  `Z/2^16`, with windows at stages `(n_j, l_j) = (8, 6), (12, 100)` placed by (A2):
  - Lemma 3.1 holds exactly (`1.0000` and `0.5000`);
  - Lemma 2.1 holds, with `max_k eta_k = 0.0283 <= 0.0552`;
  - the decoders recover `x mod 2^15` forward and backward on 65 residues, and `x mod 2^13` from forward windows of
    length `q/4` for 60 random `x`, with 0 failures.

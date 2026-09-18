# Referee check: the P_eff kill (linear-time lamp centralizers)

Lane bh-free-58, 2026-09-18. This is an independent check of three nodes landed by bh-invent-11
in c0dfc4ce5:
- `linear-time-rauzy-sets-exist`;
- `nv-machines-realize-linear-time-lamp-centralizers` and its `-proof`;
- the upgrade of `fp-simple-group-containing-a-non-efrf-residually-finite-group` to ESTABLISHED.

**Verdict: PASS**, with one repair (R1). The result is load-bearing: it removes the separator
`P_eff` from Synthesis v5. So an independent read was worth doing.

Before reading these nodes I had derived the same mechanism in Kohl's groups `CT_P(Z)`
(section 3 below). This confirms the result in a second host with a different timing device.

## 1. `linear-time-rauzy-sets-exist`: PASS

Every step was checked.

1. **B = −B and 0 ∉ B.** The window `[−M, M]` is symmetric, and 0 has no odd part.
2. **B is open.** `J_n` is a union of classes modulo an even `Q_n`, so `2^n j + 2^n Q_n Z ⊆ B`.
   The elements keep 2-adic valuation `n`.
3. **Linear time.**
   - Halving costs `O(s)` in total.
   - The simulation costs `O(j·n) = O(s·n/2^n)`.
   - Decoding `M_n` from `n ≤ log_2 s` costs `poly(log s)`, for any enumeration whose `n`-th
     table has size polynomial in `log n`.
   - Accepting after `j` silent steps is correct in both cases. If `N_n = ∞`, every odd number
     is in `J_n`; if `N_n ≥ j`, then `|j| ≤ N_n ≤ M`.
4. **Not effectively open.**
   - With `p = lcm(Φ(2^n), 2^(n+1))/2^n` and `p ≤ 2N`, the first element of `1 + pN_{≥1}` above
     `M = 2N+1` lies in `(2N+1, 4N+1]`.
   - That interval is below `Q = 8N+8` and outside `[0, 2N+1] ∪ [6N+7, Q)`.
   - So it is an odd number outside `J_n`, a contradiction. Hence `p ≥ 2N+1`, and `p` bounds
     the halting time.

Rauzy's Proposition 1 (TeX l.200–232) then applies as stated.

## 2. The nV construction: PASS after (R1)

**Checked.**
- **Exact emission.** Phase R lasts `s` steps. Phase T lasts `(C−1)s` steps, with the verifier
  running inside the clock, since `c·s < (C−1)s`. A verifier that has not halted counts as
  reject.
- **No return.** After step 1 the state is never `r` again. The clock may empty `K` at the end
  of a pass, but only in a phase-T state. So `σ`'s brick `{r, K-top ⊥}` is met only at time 0.
- **Lamps.** The supports `V_i` are pairwise disjoint and `ε` moves every point of `V_0`, so
  `⟨a^C, ε⟩ ≅ Z/2 ≀ Z`.
- **Detection.** `g` fixes `V_(Ck)` pointwise iff no branch is in `q_W` at time `Ck`. Otherwise
  it moves points out of `{z = 0}`.
- **Centralizer.** For lamp products, `[g, h] = 1` iff `F ⊆ A`. For shifted elements, the
  conjugation argument gives `A + p = A`, and `A` is not periodic. So `C_(L')(g) = U_A`.
- **Consequence.** Condition (e) of `pbh-coset-wreaths-iff-identity-edge-hnns` holds with
  `M = nV`. So `L(A)` lies in `B_A` and embeds in a finitely presented simple group.

**(R1) Well-definedness of `F`.**
- `F` is `f_+` on `{c = 1}` and `f_-^(-1)` on `{c = 0}`. It is a bijection only if `f_±`
  preserve both slices.
- Lemma 1's completion maps the complement of the rule domains onto the complement of the rule
  images by an arbitrary clopen-transitive map, and such a map may change `c`.
- **Fix.** Run the completion separately inside `{c = 1}` and `{c = 0}`. Both complements
  there still contain `{z = 1}`, so they are nonempty.
- Nothing else changes.

## 3. Independent confirmation in `CT_P(Z)`

The same kill works in Kohl's finitely presented simple groups `CT_P(Z)`. Those groups lie in
`B_A` by `rcwa-groups-satisfy-permutational-boone-higman`. Only the timing device differs. This
is a sketch; it was not landed as a node, since it duplicates the conclusion.

- **Machine.** Configurations of a reversible multi-op counter machine are coded as in
  `ct-z-conjugacy-problem-is-undecidable`: `n = Λ(y)·w`, with a passenger `w` coprime to the
  machine primes `S`.
- **Lamps.** `α` is the code map of the Kari–Ollinger switching bijection. Since `α` preserves
  passengers, `u_i = α^i ε α^(-i)` sits on the time-`i` slice of every run from the start
  state.
- **Clock and comparator** (replacing the dilation `a^C`).
  - Each run gets an input counter `W`, decremented at every step, and an elapsed counter `E`.
  - After the verifier outputs `F(z)` in a counter `Y`, a phase `Y −= 2, E −= 1` runs, then a
    phase `W−−, Y−−`.
  - The run is *special* exactly when `W = Y = 0` there. That happens at time `W_0`, and only
    if `W_0 = F(z)`.
  - The only requirement is slack: `2t(z) + 1 < F(z)`, where `t(z)` is the verifier's running
    time.
- **Detector.**
  - `ε` applies a passenger involution `φ` (`w ↔ ℓ_1 w` at `ℓ_1`-level 0/1) on start
    configurations whose auxiliary counters are zero.
  - `σ` applies `ψ` (`ℓ_1`-level 1 ↔ `ℓ_2`-level 1) on special configurations.
  - Here `ℓ_1, ℓ_2 ∉ S`, and `[φ, ψ] ≠ 1`, so `u_i` and `σ` fail to commute exactly at special
    times.
- **Result.** `C_L(σ) = U_A`, with `A = Z ∖ (S ∪ (−1 − S))`, provided `|S| ≥ 2`. The `−1` shift
  comes from the switching mirror.
  - A Rauzy-type `S` with this slack is `S = B' ∩ N`, where `B' = B ∪ (−1 − B)`.
  - `B = ⋃_n Y_n`, with `Y_n = {2^nΦ} ∪ ⋃_{k ≠ N_n + 1} {2^nΦ + 2^(n+1)Φ3^k j : 3 ∤ j}`.
  - `Φ` is a large odd constant prime to 3, and `N_n` is the halting time of a universal
    reversible counter machine on input `n`.
  - The verifier builds `F` by multiplying stages in `O(F/Φ)` steps and checks shell `k` with
    a `k`-step budget.
- **Why it is not a node.** The conclusion and the mechanism (all branches in parallel, plus a
  state-reading involution) are those of `nv-machines-realize-linear-time-lamp-centralizers`.

## Lesson for general BH

Only two things are needed to kill `P_eff`, and both are available in every full host with a
reversible universal model (symbolic `nV`, arithmetic `CT_P(Z)`):
- lamp placement by one machine element that runs all inputs in parallel;
- a timing device, which can be a clock carried as an input counter and compared with the
  verifier's output, so exact timing costs nothing.

So `P_eff`-type separators, built on effective versions of residual properties, fail uniformly
across the known host families, not only in `nV`. The live separators are the ones that are not
about effectivity: `P_Z` and `(RT)`.

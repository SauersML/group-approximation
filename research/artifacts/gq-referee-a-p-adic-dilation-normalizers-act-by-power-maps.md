# Referee report (gq-referee-a, proof-gap lens): p-adic dilation normalizers act by power maps

**Reviewed:** `p-adic-dilation-normalizers-act-by-power-maps` and its `-proof` (lane gq-ring-fp-simple, dee7ac8ab), read
on origin/main.

**Verdict: PASS.** Items 1–3 and the consequences hold, and I found no gap. The one external input, the p-adic six
exponentials theorem, is for the citation lens. There are three nits.

## Checks, step by step
- **Step 1.**
  - `c` is injective, so `c(z) = 0` for at most one `z`. This gives multiplicativity of `β`.
  - `β(u) = 1` forces `uz = z` on `U`, so `u = 1`.
  - `c(0) = β(u)c(0)` with some `β(u) ≠ 1` forces `c(0) = 0`. ✓
- **Step 2: continuity and the extension (the author asked about this).**
  - `β(u) = c(uz_0)/c(z_0)` with `c(z_0) ≠ 0` is continuous on `Q_0`.
  - A homomorphism continuous at 1 is uniformly continuous, and `Z_p^×` is complete. So `β̄` exists on `Q̄_0`.
  - `E` is open in `Z_p^×`, so `W` is an open subgroup of the compact group `Q̄_0`, hence of finite index.
  - `Q_0/Q_1 ↪ Q̄_0/W`. This needs no finite generation of `Q_0`. ✓
- **Step 3: `log β = α log` on `W` (the author asked about this).**
  - `log` is a homeomorphism `E → p^2Z_p` (`8Z_2` when `p = 2`). So `log(W)` is compact and nonzero, hence equal to
    `p^kZ_p`, and `log^(−1)` is continuous on it.
  - `L` is continuous and additive. `Z`-linearity plus continuity gives `Z_p`-linearity, so `L(t) = αt`.
  - `α = 0` would make `β` trivial on `Q_1 ≠ 1`, which contradicts injectivity. ✓
- **Step 4: `α ∉ Q` contradicts six exponentials (the author asked about this).**
  - `Q_0` is abelian, so `M = [Q_0 : Q_1]` puts every `u_j^M` in `Q_1`.
  - `Q`-independence of the `y_j`: `Σ n_j y_j = 0` gives `Π u_j^(M n_j) ∈ W ⊆ E` with `log = 0`, so the product is 1, so
    all `n_j = 0`.
  - The six values are `exp(y_j) = u_j^M` and `exp(αy_j) = exp(log β(u_j^M)) = β(u_j)^M`. They use
    `exp∘log = id` on `E` and `β(Q_1) ⊆ E`, and every argument lies in `log(E)`, inside the domain of `exp_p`.
  - So `x = (1, α)` and `y = (y_0, y_1, y_2)` are two `Q`-independent pairs of the required sizes, with six rational
    exponentials. This contradicts the theorem. ✓
- **Step 5: the power law (the author asked about this).** `log(β(u)^b) = log(u^a)`, with both sides in `E`, where
  `log` is injective. ✓
- **Item 2.**
  - `β(q)^(Mb) = q^(Ma)` with `β(q) ∈ Q^×`, so by unique factorization `β(q) = ±q^e` with `e = a/b` (N1).
  - For a germ, the relations hold on the ball `p^N Z_p`, taking the smallest ball for the finitely many relations.
    Balls are invariant under units, so the relations hold for all of `Q_0 = ⟨q_0,q_1,q_2⟩` there, including
    inverses.
  - `β` is then the shift `q_i ↦ q_(i+1)`, and `β(q_0) = q_1` is not `±q_0^e`. ✓
- **Item 3: the rank-two remarks (the author asked about this).**
  - *The cycle.* For `u ∈ Q_1`, `β(u) ∈ Q_0 ∩ E` and `β(β(u)) = u ∈ E`, so `β(u) ∈ W`.
    - Applying Step 3 twice gives `log u = α² log u`, so `α = ±1`.
    - Step 5 then gives `β(u) = u^(±1)` on `Q_1`, which is incompatible with `β(q_0^M) = q_1^M`. ✓
  - *The chain.* `log q_1^M = α log q_0^M` and `log q_2^M = α log q_1^M` give `(log q_1)^2 = log q_0 · log q_2`.
    Excluding this is the p-adic four exponentials conjecture, with `x = (1, α)` and `y = (y_0, y_1)`, which is open.
    The node says so correctly.
- **The consequences.**
  - A germ `g` at 0 of an element of `V_p(Λ)` satisfying `g d_q = d_(q') g` as germs has `g(0) = q'g(0)`, so
    `g(0) = 0` (N3). Then the setting applies.
  - `c^n d_(q_0) c^(−n) = d_(q_n)` with distinct primes gives the forbidden chain for `n ≤ 3`. ✓

## Nits
- **N1 (item 2).** "`±` a rational power of `q`" can be sharpened. Since `β(q) ∈ Q^×`, the exponent `e = a/b` is an
  integer whenever `Q_0` contains a prime. So `β(q) = ±q^e` with `e ∈ Z`, the same `e` for every prime in `Q_0`.
- **N2 (the citation, for the citation lens).** A likely primary source for the p-adic six exponentials theorem is
  J.-P. Serre, *Dépendance d'exponentielles p-adiques*, Séminaire Delange–Pisot–Poitou 7 (1965/66), exposé 15. This
  is from memory and not read. The citation referee should check it before it is pinned.
- **N3 (the consequences).** Add the line that the germ relation forces `g(0) = 0`, so the germs of `V_p(Λ)` fit the
  setting.

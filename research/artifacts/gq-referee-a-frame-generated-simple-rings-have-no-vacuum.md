# Referee report (gq-referee-a, proof-gap lens): frame-generated simple rings have no vacuum

**Reviewed:** `frame-generated-simple-rings-have-no-vacuum` and its `-proof` (lane gq-infinite-primes, a863176f1), read
on origin/main (eb9a7edce).

**Verdict: PASS.** Items 1–4 and the `R_L` computation hold, and I found no gap. There are three nits. The Consequences
paragraph "Where room remains" is a reading under the Pimsner sequence and is not reviewed here.

## Checks
- **Item 1.**
  - *`φ` is a ring map.* `s = sp` and `t = pt` come from (T2) at `b = 1`. Then
    `φ(b)φ(b') = tb(s·tb's) = tb(sφ(b')) = tb(b's) = φ(bb')`, and `φ(b) = pφ(b)p`.
  - *`e` and `q`.* `e² = spt = e`, `be = sφ(b)t = e b`, `qs = s − sp = 0` and `tq = t − pt = 0`.
  - *The normal form terminates* (N1). Count the inversions `(t,s)`, `(b,s)` and `(t,b)`. Each of the three moves
    `t_is_j → p_ij`, `b s_i → Σ s_j φ(b)_(ji)` and `t_i b → Σ φ(b)_(ij) t_j` strictly lowers that count in every term.
    ✓
- **Gram matrices and the recursion.**
  - `t_β s_α` peels from the inside, `t_(β_1)s_(α_1) = p_(β_1α_1)`, then `t(b)s = φ(b)` entrywise.
  - Unequal lengths leave a nonempty `s_γ` on the right or `t_γ` on the left.
  - With `t_((β,j)) = t_j t_β` and `s_((α,i)) = s_α s_i`, the `(β,α)` block of `P^(m+1)` is the `k×k` matrix
    `φ(P^(m)_(βα))`. So `P^(m+1) = 0` with `φ` injective gives `P^(m) = 0`. ✓
- **The induction `E_m s_α = s_α` (the author asked about this).**
  - *Base.* `E_1 s_i = (s t s)_i = (sp)_i = s_i`.
  - *Step.* `E_(m+1) = Σ_(|α|=m) s_α e t_α`. For `|α'| = m`:
    `E_(m+1) s_(α')s_j = Σ_α s_α e P^(m)_(αα') s_j = Σ_α s_α P^(m)_(αα') e s_j = (E_m s_(α'))s_j = s_(α')s_j`.
    This uses `eb = be`, `es_j = s_j` and `Σ_α s_α P^(m)_(αα') = Σ_α s_αt_αs_(α') = E_m s_(α')`. ✓
  - *The dual.* `t_δ E_m = t_δ` has the same shape: `tE_1 = tst = pt = t` (N2).
- **The vanishing of `q t_β s_α q` for `|β| ≠ |α|` (the author asked about this).**
  - If `|β| < |α|`: `t_βs_α = Σ b s_γ` with `γ ≠ ∅`, and `q b s_γ q = b q s_γ q = 0`.
  - If `|β| > |α|`: `t_βs_α = Σ t_γ b`, and `q t_γ b q = q t_γ q b = 0`, using `t_γ q = 0` for `γ ≠ ∅`.
  - If the lengths are equal, it is `P^(m)_(βα)q`. ✓
- **Fock idempotents and the truncation.**
  - `G_jG_(j') = δ_(jj') Σ_(β,α) s_β P_(βα) q t_α = δ G_j`.
  - `G_m s_α q = s_α q`, and `q t_δ G_m = q t_δ`, by the dual.
  - So each spanning element `x = s_α q b t_δ` of `RqR` with lengths `≤ n` satisfies `x = GxG`. Then
    `1 = GyG` gives `G = 1`.
  - For `|α| = n+1` and `j ≤ n`, `G_j s_α = Σ s_β q (Σ b s_γ) = 0`. So `s_α = G s_α = 0`, `P^(n+1) = 0`, and descent
    gives `p = 0`. ✓
- **Item 3.**
  - `q ≠ 0` in a simple `R` gives `RqR = R`, hence `p = 0`.
  - `ker φ` is a proper two-sided ideal when `p ≠ 0`, so it is 0 when `B` is simple.
  - A directed union of simple rings along unital maps is simple: a nonzero ideal meets some `B_i` nontrivially,
    hence contains 1. ✓
- **Item 4.** The concatenated (T1) includes the cross terms `t^(a) b s^(a')`. The hypothesis requires them in `B`,
  as stated. ✓

## The `R_L` computation (the author asked about this)
- *On `N`.*
  - `t_1Ns_1 = t_1s_1(N+1) = N+1`.
  - `t_2Ns_2 = 0 = f(0)` for `f = N`.
  - The cross terms vanish by `t_is_j = δ_ij`.
- *On `B`.* For every `f ∈ B`, `f s_1 = s_1 f(N+1)` and `f s_2 = s_2 f(0)`. For polynomials this follows by
  induction.
  - For the resolvents, `(N+c)s_1 = s_1(N+c+1)` gives `(N+c)^(−1)s_1 = s_1(N+c+1)^(−1)`. This uses that
    `(N+c+1)^(−1)` lies in `R_L`, as `leavitt-resolvent-ring-is-fp-simple-of-char-zero` provides.
  - `(N+c)^(−1)s_2 = c^(−1)s_2`, using `Q ⊆ R_L`.
  - `f ↦ f(N+1)` and `f ↦ f(0)` are well defined on `B = Q[N][(N+c)^(−1) : c ≥ 1]`, since `c + 1 ≥ 1` and `c^(−1) ∈ Q`.
    So `φ(f) = diag(f(N+1), f(0))`. ✓
- *(T2).* `t_1 f = t_1 f(s_1t_1 + s_2t_2) = f(N+1)t_1`, and similarly `t_2 f = f(0)t_2`. ✓
- *Injectivity and the index.* `φ` is injective because the substitution `N ↦ N+1` is injective on `Q(N)`. And
  `p = I_2`, so `[1] = 2[1]`. ✓
- *The subframe `(s_1,t_1)`.* It satisfies (T1) and (T2) with `p = 1`, `φ_1(f) = f(N+1)` and vacuum `s_2t_2`. The ring it
  generates with `B` does not contain `s_2`, so item 2 correctly makes its vacuum ideal proper there. ✓

## Nits
- **N1 (item 1).** Give a termination measure for the normal form, for example the inversion count above.
- **N2 (item 2).** Write out the dual induction `t_δE_m = t_δ`. The claim `q t_δ G_m = q t_δ` uses it.
- **N3 (`R_L`).** Cite where `(N+c)^(−1) ∈ R_L` for `c ≥ 2` comes from, the transport of `A` along `s_1`, and note that
  `(N+c)^(−1)s_2 = c^(−1)s_2` uses `Q ⊆ R_L`.

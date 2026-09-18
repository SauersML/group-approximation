# Relative fixed price for finitely generated pairs: a decomposition of shape (B)

Worker swarm-0917-w6-w6-fp-last1, 2026-09-17. Nodes:
- `fpbs-relative-stage-costs-bound-cost-by-stage-liminf`: ESTABLISHED, §1.
- `fpbs-relative-fixed-price-fg-pairs`: OPEN, §2.
- `fpbs-relative-fixed-price-free-pairs`: OPEN, §2.
- `fpbs-locally-free-finite-cost-from-relative-free-pairs`: route, §3.

**Notation.**
- For measurable subrelations `S ⊆ R` of a p.m.p. countable relation,
  `relC(R;S)` is the infimum of `c(Φ)` over graphings `Φ ⊆ R` with
  `S ∨ Φ = R`. If `Ψ` generates `S`, then `Ψ ∪ Φ` generates `R`, so
  `C(R) ≤ C(S) + relC(R;S)`.
- For a p.m.p. action `a` of `Γ` and `Δ ≤ Γ`, write `R_Δ = E_{a|Δ}`.
- `x^+ = max(x, 0)`.

## 0. Why this decomposition

Theorem G of `fpbs/docs/fixed-price-countable-passage.md` assumes H (fixed
price for finitely generated groups). Under H, a counterexample has
`C(Γ) < ∞` and has one of two shapes:
- shape (A): no fixed pseudocost;
- shape (B): fixed pseudocost, and some free action of infinite cost.

Every wave-2 to wave-5 attack on shape (B) at `Γ_mal` tried to build *cheap
repairs* over one malnormal stage. Several ESTABLISHED obstructions block
this:
- finite contact;
- linear perimeter, which puts a floor under every packing certificate;
- extension circularity;
- blindness to lattices and relative L2 invariants.

The one statement left open is the single-stage floor. It gives no way to
reason about the *sign* of the answer.

This artifact swaps the geometric question for one numerical inequality
between finitely generated pairs. That inequality (RFP) holds in every case
where the relative cost can currently be computed (§2.2). Summed along
an exhaustion, it yields the upper bound `C(a) ≤ liminf` of stage costs (§1).

## 1. The stage-liminf lemma (ESTABLISHED, self-contained)

**Lemma 1.** Let `a` be a p.m.p. action of a countable group `Γ`, and let
`Γ_1 ≤ Γ_2 ≤ ⋯` be finitely generated subgroups with `∪_n Γ_n = Γ`.
Put `R_n = R_{Γ_n}` and `c_n = C(R_n)`; each `c_n` is finite, bounded by
the number of generators. Suppose that for all `n < m`

```text
relC(R_m ; R_n) ≤ (c_m − c_n)^+ .                          (RFP along the chain)
```

Then `C(E_a) ≤ liminf_n c_n`.

*Proof.* Let `c = liminf_n c_n`. If `c = ∞` there is nothing to prove, so
assume `c < ∞` and fix `ε > 0`.

1. **Choose a subsequence.** Pick `n_1 < n_2 < ⋯` with
   `|c_{n_k} − c| < ε 2^{-k}`. Then
   `(c_{n_{k+1}} − c_{n_k})^+ < ε 2^{-k} + ε 2^{-k-1} < ε 2^{1-k}`.
2. **Choose graphings.**
   - A graphing `Ψ` of `R_{n_1}` with `c(Ψ) < c_{n_1} + ε < c + 2ε`.
   - For each `k`, a graphing `Φ_k ⊆ R_{n_{k+1}}` with
     `R_{n_k} ∨ Φ_k = R_{n_{k+1}}` and
     `c(Φ_k) < relC(R_{n_{k+1}}; R_{n_k}) + ε 2^{-k} < 3ε 2^{-k}`.
3. **Generation.** By induction on `k`, `Ψ ∪ Φ_1 ∪ ⋯ ∪ Φ_{k-1}` generates
   `R_{n_k}`:
   - `k = 1` is the choice of `Ψ`;
   - for the step, `R_{n_{k+1}} = R_{n_k} ∨ Φ_k`.

   The relations `R_{n_k}` increase, and their union is `E_a`, because the
   `Γ_{n_k}` increase to `Γ`. So `Ψ ∪ ⋃_k Φ_k` generates `E_a`.
4. **Cost.** `C(E_a) ≤ c + 2ε + Σ_k 3ε 2^{-k} = c + 5ε`. Let `ε → 0`. ∎

**Remarks.**
- Only the consecutive pairs `(n_k, n_{k+1})` of *one* subsequence are used.
  So the hypothesis can be weakened to: *for every `ε` there is a subsequence
  along which the stage costs converge to `c` within `ε 2^{-k}` and RFP
  holds for its consecutive pairs.*
- No fixed price input is used. The lemma is an upper semicontinuity
  statement for subgroup exhaustions, under RFP.
- For comparison: in general `C(∪R_n) ≤ liminf C(R_n)` is known only when
  `C(∪R_n) < ∞` ([TD] Prop 6.7, [GL] Prop 2.57). The lemma removes that
  finiteness assumption for subgroup chains, at the price of RFP.

**Integer-valued case.** If every `c_n` is an integer, the subsequence can be
chosen with `c_{n_k} = c` for all `k`. Then RFP only needs
`relC(R_{n_{k+1}}; R_{n_k}) = 0` along pairs of equal cost, and it gives
`C(E_a) ≤ c`.

## 2. Relative fixed price (OPEN)

### 2.1 Statements

**RFP (finitely generated pairs).** Let `K ≤ L` be finitely generated
groups with `K` infinite, and let `a` be a free p.m.p. action of `L`. Then

```text
relC( R_L ; R_K ) ≤ ( C(R_L) − C(R_K) )^+ .
```

Under H this reads `relC ≤ (C(L) − C(K))^+`.

**RFP_free (free pairs).** Let `K ≤ L` be nontrivial finitely generated free
groups, and let `a` be a free p.m.p. action of `L`. Then

```text
relC( R_L ; R_K ) ≤ ( rk L − rk K )^+ .
```

Free groups have fixed price equal to their rank (Gaboriau, lecture notes
Cor 2.25, quoted verbatim in `fpbs-shifted-stage-relative-cost-zero-or-infinite-proof`:
"The following groups are strongly treeable and have fixed price:
C∗(Fn) = C∗(Fn) = n for the free group of rank n."). So RFP_free is exactly
RFP restricted to free pairs.

The reverse inequality `relC(R_L; R_K) ≥ C(R_L) − C(R_K)` always holds,
because `C(R) ≤ C(S) + relC(R;S)`. So RFP says:
- when `C(K) ≤ C(L)`, the relative cost is exactly the cost difference;
- when `C(K) ≥ C(L)`, the relative cost is 0.

### 2.2 Cases where RFP holds

1. **`K` amenable, or `C(R_L) = 1`.** Ershov–Golan–Sapir Lemma 5.7 (imported
   in `fpbs-amen2-cost-inputs`) gives `relC(R;S) ≤ C(R) − 1` for aperiodic
   `S`. Here `R_K` is aperiodic because `K` is infinite and `a` is free.
   - If `K` is amenable, then `C(R_K) = 1`, so this is RFP.
   - If `C(R_L) = 1`, then `relC = 0`.
2. **`K` normal in `L`, or more generally infinitely many contacts.** Let
   `A` be a complete section of `R_K` of measure `< ε`. For a generator `g`
   of `L`, the restriction `g|_A` recovers `g` on `K·A = X`, since
   `g k x = (g k g^{-1}) g x`. So `relC = 0`. More generally,
   `fpbs-infinite-contact-zero-relative-cost` gives `relC = 0` whenever the
   classes of `R_K` are connected by infinite contacts. For instance, this
   holds when `K ∩ g^{-1} K g` has finite index in `K` for every `g` in a
   generating set, so it holds for commensurated `K`. Then the `g|_A` recover
   `g` on `(K ∩ g^{-1}Kg)·A`, and a finite-index subgroup of `K` still has a
   small complete section.
3. **Finite index.** Take small complete sections, as in item 2. `relC = 0`.
4. **Free factors.** Let `L = K * M`, all free. The generators of `M` repair
   everything, so `relC ≤ rk M = rk L − rk K`. Equality holds by the reverse
   inequality.
5. **Rank-deficient malnormal pairs.** For example `K = <a> ≤ F_2`: adding
   `b` gives `relC ≤ 1 = rk L − rk K`.

All the *hard* cases are malnormal pairs, with finite contact, where
`rk K ≥ rk L`. There RFP predicts `relC = 0`. The ESTABLISHED
obstructions (finite contact, linear perimeter, the packing floor) rule out
*packing* certificates of `relC = 0`. They do not rule out `relC = 0`
itself.

### 2.3 How RFP can fail

A counterexample is a pair `K ≤ L` with finite contact and `C(K) ≥ C(L)`,
together with a free action of `L` for which every repair of `R_K` to `R_L`
costs some fixed `δ > 0`.

The sharpest instance is `L = F_2 = <a, b>`, `K = <a, bab^{-2}>`, with `a`
the restriction to `H_2` of the Bernoulli shift `β` of `Γ_mal`. That
instance is exactly `fpbs-mal-bernoulli-single-stage-floor` (§3.2).

## 3. Consequences

### 3.1 RFP_free gives finite cost for locally free groups (route)

**Proposition 2.** Assume RFP_free. Let `Γ` be a countably infinite locally
free group with `c*(Γ) < ∞`. Then every free p.m.p. action `a` of `Γ` has
`C(a) ≤ c*(Γ)`. By `fpbs-locally-free-free-action-costs-are-c-star-or-infinite`,
`C(a) = c*(Γ)`.

*Proof.*
1. **Build a chain.** Let `F_1 ⊆ F_2 ⊆ ⋯` be finite sets increasing to `Γ`,
   with `F_1 ∋ g ≠ 1`. Recall
   `c_F = min { rk L : L ≤ Γ finitely generated, F ⊆ L }` and
   `c* = sup_F c_F`. Put `S_0 = ∅`. Given `Γ_{n-1}` with a finite generating
   set `S_{n-1}`, choose a finitely generated `Γ_n ⊇ F_n ∪ S_{n-1}` of rank
   `c_{F_n ∪ S_{n-1}} ≤ c*`.
   - The `Γ_n` increase and exhaust `Γ`.
   - Each `Γ_n` is free, because `Γ` is locally free.
   - Each `Γ_n` is nontrivial, hence infinite.
   - `rk Γ_n ≤ c*`.
2. **Stage costs.** `a|Γ_n` is free, so by Gaboriau Cor 2.25,
   `c_n = C(R_{Γ_n}) = rk Γ_n`. These are integers in `[1, c*]`.
3. **Apply RFP_free.** For `n < m`, RFP_free for the pair `Γ_n ≤ Γ_m` and the
   free action `a|Γ_m` gives `relC(R_m;R_n) ≤ (rk Γ_m − rk Γ_n)^+
   = (c_m − c_n)^+`.
4. **Conclude.** Lemma 1 gives `C(a) ≤ liminf c_n ≤ c*`. ∎

Only the consecutive pairs of equal rank along one subsequence are used, as in
the integer-valued case of §1. So the following weaker statement suffices:

> for every locally free `Γ` with `c* < ∞` there is a chain as above along
> which `relC(R_{n_{k+1}}; R_{n_k}) = 0` for a subsequence of rank-`c*`
> stages.

**Consequence.** Together with the ESTABLISHED dichotomy and the route
`fpbs-locally-free-fixed-price-from-finite-cost`, RFP_free gives fixed price
`c* = 1 + β_1^(2)(Γ)` for every countable locally free group. This is
unconditional; H is not needed. It covers `Γ_mal`, the Fisher–Lodha groups,
and every other ascending union of free groups.

### 3.2 Γ_mal: RFP_free at one pair is exactly the negation of the single-stage floor

Let `β` be the Bernoulli shift of `Γ_mal`, and write `H_n = <a, b_n>`. The
relation `b_n = b_{n+1} a b_{n+1}^{-2}` identifies the pair `(H_{n+1}, H_n)`
with `(F_2, <a, bab^{-2}>)`, taking `b = b_{n+1}`.

**Proposition 3.** Consider the three statements below. Then (1) ⇒ (2) and (2) ⇔ (3):
1. RFP_free holds for the pair `(H_2, H_1)` and the free action `β|H_2`,
   that is, `relC(R_{H_2}; R_{H_1}) = 0`;
2. `C(β) = 2`;
3. `fpbs-mal-bernoulli-single-stage-floor` fails.

*Proof.*
- (1) ⇒ (2). The shift `θ` conjugates `β` to itself and maps `(H_2, H_1)` to
  `(H_{n+1}, H_n)`. So `relC(R_{H_{n+1}}; R_{H_n}) = 0` for all `n`. The
  proof of Lemma 1, run along the full chain with `c_n = 2`, gives
  `C(β) ≤ 2`. By `fpbs-locally-free-free-action-costs-are-c-star-or-infinite`,
  `C(β) = 2`.
- (2) ⇒ (3), and (3) ⇒ (2). These are the ESTABLISHED
  `fpbs-shifted-stage-relative-cost-zero-or-infinite`: `C(β) = 2` iff
  `relC(E_β; R_{H_1}) = 0`.
- (2) ⇒ (1). Given a graphing of `E_β` of cost `< 2 + ε`, truncate it by
  labels in `H_2`, as in step 2 of the shifted-stage proof. The pieces with
  labels in `H_2` lie in `R_{H_2}`, but they need not generate `R_{H_2}`, so
  this direction is *not* claimed.

So (1) ⇒ (2) ⇔ (3). Hence RFP_free at one pair refutes the floor, and the
floor refutes RFP_free.

### 3.3 What RFP does to Theorem G

**Proposition 4.** Assume H and RFP, and let `Γ` be countable and not
locally finite. Then every free action `a` satisfies `C(a) ≤ c*(Γ)`, where
`c*` is `σ(a)` of the passage document. Under H, `σ(a) = c*` for every free
`a`, by Lemma 4.1 there.

*Proof.* Proposition A there gives a finitely generated exhaustion attaining
`σ(a) = liminf_n C(a|Γ_n)`. Some stage is infinite, because `Γ` is not
locally finite. Drop the earlier stages; this does not change the liminf.
RFP holds for all pairs of the chain, so Lemma 1 gives `C(a) ≤ σ(a)`. ∎

**Residual shapes.** Under H and RFP, a counterexample to fixed price is one
of:
- **(A)** no fixed pseudocost, which RFP does not touch; or
- **(B∞)** shape (B) with `c*(Γ) = ∞`.

Shape (B) with `c* < ∞` is excluded, since Proposition 4 gives (U) there.
So `fpbs-fixed-price-non-amenably-generated-from-fg` now splits into:
1. RFP (finitely generated);
2. fixed pseudocost (FPC), which the bus reports RBL reduces to a finitely
   generated statement (session b-t-nonamgen);
3. **(Cfin)**: under H, `C(Γ) < ∞` implies `c*(Γ) < ∞`.

Items 1 and 3 give (U) for every group of finite cost, and then FPC finishes.

Each prerequisite can fail on its own:
- RFP fails iff some finitely generated pair has a floor;
- FPC fails iff shape (A) occurs;
- Cfin fails iff some group has finite cost while every finitely generated
  exhaustion has stage costs tending to infinity.

For locally free groups, Cfin is ESTABLISHED: a finite-cost free action forces
`C(Γ) = c*`, by `fpbs-locally-free-free-action-costs-are-c-star-or-infinite`.
FPC is also ESTABLISHED there (`PC ≤ c*` together with Prop 6.26). So for
locally free groups only RFP_free remains, which is §3.1.

## 4. Recorded dead ends: attempts to derive RFP from H

None of these gives RFP. They are recorded so they are not retried.

1. **Double `L *_K L`.** H gives `C(L *_K L) = 2C(L) − C(K)` only when `K`
   is amenable; for non-amenable `K` there is no cost formula for
   amalgams. A relative graphing of one factor over `K` also does not
   descend from a graphing of the double.
2. **HNN extension centralizing `K`,** that is `L *_K (K × Z)`. Its cost is
   computable only from the relative cost we want. The argument is circular,
   in the same way as the ESTABLISHED extension-certificate circularity.
3. **Relative rank gradient / mod-`p` homology.** For profinite actions,
   the obvious lower bound `([L : K N_i] − 1)/[L : N_i]` tends to `0`. The
   relative Linnell/Fox L2 invariants vanish (wave 4). So no current
   invariant separates `relC = 0` from `relC > 0` at malnormal pairs. This
   is why RFP is stated as a prerequisite and not proved.

**First falsifiable test.** Does there exist a free action `a` of `F_2` and
a malnormal `K ≤ F_2` of rank `≥ 2` with `relC(R_{F_2}; R_K) > 0`? At
`K = <a, bab^{-2}>` and `a = β|H_2`, a positive answer is exactly
`fpbs-mal-bernoulli-single-stage-floor`.

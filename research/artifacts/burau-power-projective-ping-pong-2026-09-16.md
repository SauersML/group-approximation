# Closed projective ping-pong for powers of the 4-strand Burau generators: the cube threshold

Lane hi-spec-zaremsky-3-05-four-strand-bura (special case / strengthening
angle on `zaremsky-3-05-four-strand-burau-faithful`), 2026-09-16.

Claim: `burau-power-projective-ping-pong-needs-cubes`.

Scripts, in `experiments/zaremsky-3-05-burau-squares-2026-09-16/`:

- `threshold_verify.py`: exact sympy checks of every matrix identity and
  vector used in sections 1 and 3, including the dual plane.
- `bbt_sets_test.py`: a randomized exact test of the section 4 inclusions
  over `Z` and `F_2, F_3, F_5`. It is a sanity check only; the proof is by
  hand.
- `lp.py` and `growth.py`: Cartan-exponent statistics for section 6.

Both scripts exit 0.

## 0. What is new and what is not

**Not new.**

- **Moran and Beridze–Traczyk.** The abstract of BBT says "It is known that
  A^3 and B^3 generate a free group of rank two" and cites:
  - [Mor] S. Moran, Arch. Math. (Basel) 34 (1980), 496–501;
  - [Ber-Tra2] Beridze–Traczyk, Trans. A. Razmadze Math. Inst. 172 (2018).

  Neither was fetched, so both are unverified here.
- **Witzel–Zaremsky** (arXiv:1304.7923, April 2013).
  - Theorem: `<f^m, k^n>` is free for `m, n >= 3`, by ping-pong on the
    Bruhat–Tits building.
  - Remark 3.5: their building rays do not separate for squares.
- **Beridze–Bigelow–Traczyk** (arXiv:1904.11730v3, January 2020; BBT below).
  - Theorem 3.1 / Corollary 3.2: `<A^3, B^3>` is free over `Z_p[t, t^{-1}]`.
  - Their proof uses the sets `X_1, X_2, X_3` of section 4.

Section 4 only rearranges the BBT sets into a clopen 4-set configuration. It
is included so that the threshold statement is complete.

**New here (to my knowledge; see the notes file for the search record).**

1. **Coordinate-free obstruction lemma (section 2).** It rules out 4-set
   ping-pong with closed attracting sets on `P^2`, from two incidence
   conditions between `b^{±1}` and the eigenflags of a proximal diagonal `a`.
2. **Application (section 3).** No 4-set ping-pong for `(f^m, k^n)` on
   `P^2(K)` with all four sets closed exists whenever `min(m, n) <= 2`.
   - This holds for every field `K` with an absolute value and every
     specialization `|t_0| != 1`, and also on the dual plane.
   - Combined with section 4, closed projective ping-pong works exactly when
     `min(m, n) >= 3`.
3. **Closedness is the crux (section 5).** Without it, 4-set ping-pong on
   `P^2(K)` for uncountable `K` is equivalent to freeness itself.

This is an obstruction to a method, not progress on faithfulness. It says
that freeness of `<A^2, B^2>` cannot be proved with closed sets on the
projective plane. That freeness is necessary for faithfulness, since
`<A, B>` free of rank 2 is equivalent to faithfulness of Burau for `n = 4`
(Birman; see BBT §1).

## 1. Matrices and conventions

**Witzel–Zaremsky generators** (arXiv:1304.7923, §2; entries as used there,
re-checked by `threshold_verify.py`):

```text
f = diag(t, 1, t^{-1})
k = [[0, -1-t, -t^{-1}-1-t],
     [0, t^{-1}+1+t, t^{-2}+t^{-1}+1+t],
     [1, 0, 0]]
s = [[1, 1, t^{-1}],
     [-(t^{-2}+1), -(t^{-1}+1), -(t^{-2}+1)],
     [t^{-1}, 1, 1]]
```

- `k = s f s^{-1}`.
- `det s = (t-1)^3 / t^3`.
- Both `f` and `k` have determinant 1.

**BBT generators** (arXiv:1904.11730, (1)–(2) and Lemma 2.1):

```text
A = [[0, 0, -t^{-1}], [0, -t, -t^{-1}+t], [-1, 0, -t^{-1}+1]]
B = [[-t^{-1}, 1, 0], [0, 1, 0], [0, 1, -t]]
T = [[-1, 1, 0], [-1, 0, 1], [-1, 0, 0]]
T^{-1} = [[0, 0, -1], [1, 0, -1], [0, 1, -1]]
T^2 = [[0, -1, 1], [0, -1, 0], [1, -1, 0]]
```

- `T^4 = 1`.
- `A = T B T^{-1}`, `A^{-1} = T^{-1} B T` and `B^{-1} = T^2 B T^2`.

**Conjugacy.** Write `A^σ, B^σ` for the matrices with `t` replaced by `-t`.
With

```text
P = [[-t, -t^2+t, t^2], [t^2+1, 0, -t^2-1], [-t^2, 0, t]],
det P = -t^2 (t-1)^2 (t^2+1),
```

we have `P A^σ = f P` and `P B^σ = k P`. `P` has entries in `Z[t]`, and
`det P` is a monic polynomial up to sign. So over every field `F`, the
reduction of `P` is invertible in `GL_3(F(t)) ⊂ GL_3(F((t)))`.

**Ping-pong.** Let `g, h` act on a set `Z`. A *4-set ping-pong* for `(g, h)`
consists of nonempty, pairwise disjoint sets `X_{g+}, X_{g-}, X_{h+},
X_{h-} ⊆ Z` with

```text
g^{±1} (X_{g±} ∪ X_{h+} ∪ X_{h-}) ⊆ X_{g±},
h^{±1} (X_{h±} ∪ X_{g+} ∪ X_{g-}) ⊆ X_{h±}.
```

**Why it proves freeness.** Let `w` be a nontrivial reduced word in `g, h`.

1. **A power of `g`.** If `w = g^j` with `j != 0`, then `w X_{h+} ⊆ X_{g±}`.
   That set is disjoint from `X_{h+}`, so `w != 1`.
2. **Any other word.** Otherwise, after conjugation, `w` is a reduced word
   whose leftmost and rightmost syllables are nonzero powers of `h`.
   - Pick `x ∈ X_{g+}`. Apply the syllables from the right. Each syllable
     `g^{±j}` or `h^{±j}` with `j >= 1` moves the point into the set with
     its own index.
   - So `w x ∈ X_{h±}`, which is disjoint from `X_{g+}`, and `w != 1`.

Hence `<g, h>` is free on `g, h`.

Relabeling `X_{g+} <-> X_{g-}` exchanges `g` and `g^{-1}`, so it is enough to
treat positive exponents `m, n >= 1`.

`P^2(K)` carries the quotient topology from the absolute value of `K`. Every
invertible linear map is a homeomorphism of `P^2(K)`, and so is coordinatewise
application of a continuous field automorphism.

## 2. The obstruction lemma

**Setup.**

- `K` is a field with an absolute value `| |`.
- `a ∈ GL_3(K)` is diagonal in a basis `u_+, u_0, u_-` with eigenvalues
  `λ_+, λ_0, λ_-` satisfying `|λ_+| > |λ_0| > |λ_-|`.
- `p_+, p_0, p_-` are the corresponding points of `P^2(K)`.
- `ℓ_+ = P(span(u_+, u_0))` and `ℓ_- = P(span(u_0, u_-))`.
- `b ∈ GL_3(K)`.

**Dynamics of `a`.** For `x = [x_+ u_+ + x_0 u_0 + x_- u_-]`:

- (D1) if `x ∉ ℓ_-` (so `x_+ != 0`), then `a^j x -> p_+` as `j -> +∞`;
- (D2) if `x ∈ ℓ_+ \ {p_+}` (so `x_- = 0`, `x_0 != 0`), then
  `a^{-j} x -> p_0`;
- (D1') if `x ∉ ℓ_+`, then `a^{-j} x -> p_-`;
- (D2') if `x ∈ ℓ_- \ {p_-}`, then `a^j x -> p_0`.

**Proof of (D1).** In the coordinates above,
`a^j x = [x_+ : (λ_0/λ_+)^j x_0 : (λ_-/λ_+)^j x_-]`. The ratios have
absolute value `< 1`, so this converges to `[1 : 0 : 0]`. The other three
cases are the same computation.

**Lemma 2.1.** Assume

- (i) `b ℓ_+ != ℓ_+` and `b ℓ_- != ℓ_-`; and
- (ii) at least one of the following:
  - (ii-a) for some `ε ∈ {+1, -1}`, `b^ε p_+ ∈ ℓ_+ \ {p_+}` and
    `b^{-ε} p_- ∈ ℓ_- \ {p_-}`;
  - (ii-b) `b^{δ} p ∈ {p_+, p_-}` for some `δ ∈ {±1}` and some
    `p ∈ {p_+, p_-}`.

Then no 4-set ping-pong for `(a, b)` on `P^2(K)` has `X_{a+}` and `X_{a-}`
closed. Nothing is assumed about `X_{b±}`.

**Proof.** Suppose a configuration exists with `X_{a±}` closed.

**Step 1: `p_+ ∈ X_{a+}` and `p_- ∈ X_{a-}`.**

- Let `S = X_{a+} ∪ X_{b+} ∪ X_{b-}`. Then `a S ⊆ X_{a+} ⊆ S`.
- Suppose some `x ∈ S` lies off `ℓ_-`. Then `a^j x ∈ X_{a+}` for all
  `j >= 1`, and `a^j x -> p_+` by (D1). Since `X_{a+}` is closed,
  `p_+ ∈ X_{a+}`.
- Otherwise `S ⊆ ℓ_-`. Then `X_{a+}` and `X_{b+}` both lie in `ℓ_-`.
  - Also `b X_{a+} ⊆ X_{b+} ⊆ ℓ_-` and `b X_{b+} ⊆ X_{b+} ⊆ ℓ_-`.
  - So `X_{a+}` and `X_{b+}` both lie in `ℓ_- ∩ b^{-1} ℓ_-`.
  - By (i), `b^{-1} ℓ_- != ℓ_-`, so this intersection of two distinct lines
    is a single point.
  - Two nonempty subsets of a single point are not disjoint, a
    contradiction.
- The same argument with `a^{-1}`, `S' = X_{a-} ∪ X_{b±}`, (D1') and
  `b ℓ_+ != ℓ_+` gives `p_- ∈ X_{a-}`.

**Step 2, case (ii-b).** Suppose `b^δ p = q` with `p, q ∈ {p_+, p_-}`.

- By Step 1, `p` lies in `X_{a+}` or `X_{a-}`.
- Hence `q = b^δ p ∈ X_{bδ}`.
- But `q` also lies in `X_{a+}` or `X_{a-}` by Step 1. This contradicts
  disjointness.

**Step 2, case (ii-a).**

- **`p_0 ∈ X_{a-}`.** We have `p_+ ∈ X_{a+}`, so `y = b^ε p_+ ∈ X_{bε}`.
  - The ping-pong inclusions give `a^{-1} X_{bε} ⊆ X_{a-}` and
    `a^{-1} X_{a-} ⊆ X_{a-}`. Hence `a^{-j} y ∈ X_{a-}` for every `j >= 1`.
  - Since `y ∈ ℓ_+ \ {p_+}`, (D2) gives `a^{-j} y -> p_0`.
  - As `X_{a-}` is closed, `p_0 ∈ X_{a-}`.
- **`p_0 ∈ X_{a+}`.** Symmetrically, `p_- ∈ X_{a-}` gives
  `z = b^{-ε} p_- ∈ X_{b,-ε}`.
  - The iterates `a^j z` lie in `X_{a+}` for `j >= 1`.
  - Since `z ∈ ℓ_- \ {p_-}`, (D2') gives `a^j z -> p_0`, so `p_0 ∈ X_{a+}`.

So `p_0 ∈ X_{a+} ∩ X_{a-}`, which contradicts disjointness. ∎

**Remarks.**

- **Frame orientation.** Replacing `a` by `a^{-1}` swaps `p_+ <-> p_-` and
  `ℓ_+ <-> ℓ_-`. Hypotheses (i) and (ii) are invariant under this swap: (ii-a)
  with `ε` becomes (ii-a) with `-ε`. So in applications it does not matter
  which of the two extreme eigenvalues is the larger.
- **Where the absolute value enters.** Only through (D1), (D2), (D1') and
  (D2'), that is, through strict gaps among `|λ_+|, |λ_0|, |λ_-|`.
- **What condition (ii-a) says.** One of `b^{±1}` carries an attracting point
  of `a` into the corresponding attracting line without leaving the line.
  This is a failure of the transversality that proximal ping-pong needs.

## 3. Application: min(m, n) <= 2

Throughout this section:

- `K` is a field with an absolute value, and `t_0 ∈ K^×` with `|t_0| != 1`.
- All matrices are specialized at `t = t_0`.
- `e_1, e_2, e_3` is the standard basis.

**Lemma 3.0 (nonvanishing).** Suppose `φ = ± t^c ∏_d Φ_d(t)^{c_d}`, with
`Φ_d` the cyclotomic polynomials and `c, c_d ∈ Z`. Then `φ(t_0)` is defined
and nonzero.

*Proof.* `Φ_d` divides `t^d - 1` in `Z[t]`. So `Φ_d(t_0) = 0` forces
`t_0^d = 1`, hence `|t_0| = 1`. ∎

Every entry named "nonzero" below has this form. It is built from `t`,
`t+1 = Φ_2`, `t^2+1 = Φ_4` and `t^2+t+1 = Φ_3`, and `threshold_verify.py`
checks the form by factoring. Also `det s = (t-1)^3/t^3 = Φ_1^3/t^3`, so
`s(t_0)` is invertible.

**Explicit matrices** (factored; `threshold_verify.py` asserts each one):

```text
k^{-1} = [[0, 0, 1],
          [(t+1)(t^2+1)/t^2, (t^2+t+1)/t, 0],
          [-(t^2+t+1)/t, -(t+1), 0]]
k^2    = [[-(t^2+t+1)/t, -(t+1)(t^2+t+1)/t, -(t+1)^2(t^2+1)/t^2],
          [(t+1)(t^2+1)/t^2, (t^2+t+1)^2/t^2, (t+1)(t^2+1)(t^2+t+1)/t^3],
          [0, -(t+1), -(t^2+t+1)/t]]
k^{-2} = [[-(t^2+t+1)/t, -(t+1), 0],
          [(t+1)(t^2+1)(t^2+t+1)/t^3, (t^2+t+1)^2/t^2, (t+1)(t^2+1)/t^2],
          [-(t+1)^2(t^2+1)/t^2, -(t+1)(t^2+t+1)/t, -(t^2+t+1)/t]]
```

**The frame for `a = f^m`.**

- `a = diag(t_0^m, 1, t_0^{-m})` has three strict gaps in absolute value.
- Its extreme eigenpoints are `e_1` and `e_3`, and the middle one is `e_2`.
- The two attracting lines are `L_3 = {x_3 = 0} = P(span(e_1, e_2))` and
  `L_1 = {x_1 = 0} = P(span(e_2, e_3))`.

By the frame-orientation remark after Lemma 2.1, the hypotheses read the
same whether `|t_0| > 1` or `|t_0| < 1`:

- (i) `b L_3 != L_3`, i.e. `(b e_1)_3 != 0` or `(b e_2)_3 != 0`; and
  `b L_1 != L_1`, i.e. `(b e_2)_1 != 0` or `(b e_3)_1 != 0`.
- (ii-a) For some `ε`, the vector `b^ε e_1` has `x_3 = 0` and `x_2 != 0`,
  and `b^{-ε} e_3` has `x_1 = 0` and `x_2 != 0`.
- (ii-b) Some `b^{±1} e_i` with `i ∈ {1, 3}` is proportional to `e_1` or
  `e_3`.

**Proposition 3.1.** If `n ∈ {1, 2}` and `m >= 1`, no 4-set ping-pong for
`(f^m, k^n)` on `P^2(K)` has `X_{f±}` closed.

*Proof.* Apply Lemma 2.1 with `a = f^m` and `b = k^n`.

- **`n = 1`.** `k e_1 = e_3`, the first column of `k`, so (ii-b) holds.
  - (i): `(k e_1)_3 = 1` and `(k e_2)_1 = -(t_0+1) != 0`.
- **`n = 2`.** Condition (ii-a) holds with `ε = +1`:
  - `k^2 e_1 = (-(t^2+t+1)/t, (t+1)(t^2+1)/t^2, 0)`;
  - `k^{-2} e_3 = (0, (t+1)(t^2+1)/t^2, -(t^2+t+1)/t)`.
  - (i): `(k^2 e_2)_3 = -(t_0+1) != 0` and
    `(k^2 e_2)_1 = -(t_0+1)(t_0^2+t_0+1)/t_0 != 0`. ∎

**Proposition 3.2 (dual plane).** Suppose `n ∈ {1, 2}` and `m >= 1`, and let
`g` act on the dual plane by `(g^{-1})^T` on column vectors. Then no 4-set
ping-pong for `(f^m, k^n)` on `P^2(K)^*` has `X_{f±}` closed.

*Proof.* Apply Lemma 2.1 with `a = f^{-m}`, which has the same frame, and
`b = (k^{-n})^T`. Then `b e_i` is row `i` of `k^{-n}`, and `b^{-1} e_i` is
row `i` of `k^n`.

- **`n = 1`.** `b^{-1} e_3` is row 3 of `k`, which is `e_1`, so (ii-b) holds.
  - (i): `(b e_1)_3 = (k^{-1})_{13} = 1` and
    `(b e_3)_1 = (k^{-1})_{31} = -(t_0^2+t_0+1)/t_0 != 0`.
- **`n = 2`.** Condition (ii-a) holds with `ε = +1`:
  - `b e_1` is row 1 of `k^{-2}`, namely `(-(t^2+t+1)/t, -(t+1), 0)`;
  - `b^{-1} e_3` is row 3 of `k^2`, namely `(0, -(t+1), -(t^2+t+1)/t)`.
  - (i): `(b e_2)_3 = (k^{-2})_{23} = (t_0+1)(t_0^2+1)/t_0^2 != 0` and
    `(b e_3)_1 = (k^{-2})_{31} = -(t_0+1)^2(t_0^2+1)/t_0^2 != 0`. ∎

**The symmetry `s`.** We have `s^{-1} f s = k^{-1}`, checked by
`threshold_verify.py`, and `s^{-1} k s = f` by definition of `k`.

- Hence `x -> s^{-1} x` carries a 4-set ping-pong for `(f^m, k^n)` to one
  for `(k^{-m}, f^n)`.
- Reading it as a configuration for `(f^n, k^m)`, with the `k`-labels `±`
  swapped:
  - the new `f`-sets are `s^{-1} X_{k±}`;
  - the new `k`-sets are `s^{-1} X_{f∓}`.
- Closedness is preserved. On the dual plane the same holds with `s^T`.

**Corollary 3.3.** Let `K`, `t_0` be as above and `m, n >= 1`.

1. If `m ∈ {1, 2}`, no 4-set ping-pong for `(f^m, k^n)` on `P^2(K)` or
   `P^2(K)^*` has `X_{k±}` closed.
2. If `min(m, n) <= 2`, no 4-set ping-pong for `(f^m, k^n)` on `P^2(K)` or
   `P^2(K)^*` has all four sets closed.
3. The same holds for `(A^m, B^n)` specialized at `t_0`.
   - The identities `P A^σ = f P` and `P B^σ = k P` at `t = -t_0` say that
     `P(-t_0)` conjugates `(A(t_0), B(t_0))` to `(f(-t_0), k(-t_0))`.
   - Here `|-t_0| != 1`, and `det P(-t_0) = -t_0^2(t_0+1)^2(t_0^2+1)` is
     nonzero by Lemma 3.0.
   - So `x -> P(-t_0) x` transports configurations in both directions.

*Proof.* Part 1 is Propositions 3.1 and 3.2 transported by the symmetry `s`.
Parts 2 and 3 follow. ∎

**Consistency at exponent 3.** For `n = 3`, `k^3 e_1 = k^2 e_3` has third
coordinate `-(t^2+t+1)/t != 0`, so (ii-a) fails with `ε = +1`.
`threshold_verify.py` confirms that the hypotheses of Lemma 2.1, as encoded
there, fail for `(m, n) = (3, 3)` in all four settings (`X_f` or `X_k`
closed, on `P^2` or its dual). This is consistent with section 4.

## 4. Existence for m, n >= 3 (BBT sets)

**Setting.**

- `F` is any field and `K = F((t))`, with valuation `v` = lowest `t`-degree
  (`v(0) = +∞`) and absolute value `|x| = 2^{-v(x)}`.
- For `x = [x_1 : x_2 : x_3] ∈ P^2(K)`, write `v_i = v(x_i)`.
- Every condition below depends only on the differences `v_i - v_j`, so it
  is well defined on projective points.

**The sets.** For `d >= 1` let `Y_d = {v_1 <= v_2 - d and v_1 <= v_3 - d}`,
which forces `x_1 != 0`. Set

```text
X_1 = Y_2,
X_2 = {v_1 = v_2 = v_3},
X_3 = {v_2 <= v_1 - 2 and v_2 <= v_3 - 2},
X_4 = {v_3 <= v_1 - 2 and v_3 <= v_2 - 2}.
```

`X_1`, `X_2` and `X_3` are the sets in the proof of BBT Theorem 3.1. `X_4`
is added here.

- **Disjointness.** The four sets are pairwise disjoint: in `X_1`, `X_3` and
  `X_4` a different coordinate has strictly smallest valuation, and in `X_2`
  none does.
- **Clopen.** Let `φ_i(x) = |x_i| / max_j |x_j|`.
  - It is continuous on `K^3 \ {0}` and invariant under scaling, so it is
    continuous on `P^2(K)`.
  - It takes values in `{0} ∪ {2^{-c} : c >= 0}`.
  - Hence `{φ_i = 1} = {φ_i > 1/2}` and `{φ_i <= 1/4} = {φ_i < 1/2}` are
    both open and closed.
  - `X_1 = {φ_1 = 1, φ_2 <= 1/4, φ_3 <= 1/4}` and `X_2 = {φ_1 = φ_2 = φ_3 = 1}`,
    and similarly for `X_3` and `X_4`, so all four sets are clopen.
  - Their images under the homeomorphisms `T^{±1}`, `T^2` and `P` are clopen
    as well.

**Facts** (items 2–5 are BBT's items 2–5; item 1 is not there).

1. `B Y_d ⊆ Y_{d+1}` for `d >= 1`.
2. `T X_1 ⊆ X_2`.
3. `T^{-1} X_1 ⊆ X_3`.
4. `B X_2 ⊆ Y_1`.
5. `B X_3 ⊆ X_2`.
6. `T^2 X_1 ⊆ X_4`.

*Proofs.* Note `B x = (-t^{-1} x_1 + x_2, x_2, x_2 - t x_3)`.

1. Let `x ∈ Y_d`, `d >= 1`.
   - First coordinate: `v(t^{-1} x_1) = v_1 - 1 < v_2`, so it has valuation
     `v_1 - 1`.
   - Second coordinate: `v_2 >= v_1 + d = (v_1 - 1) + (d+1)`.
   - Third coordinate: `v(x_2 - t x_3) >= min(v_2, v_3 + 1) >= v_1 + d`.
   - So `B x ∈ Y_{d+1}`.
2. `T x = (-x_1 + x_2, -x_1 + x_3, -x_1)`. For `x ∈ X_1` all three
   coordinates have valuation `v_1`.
3. `T^{-1} x = (-x_3, x_1 - x_3, x_2 - x_3)`. For `x ∈ X_1`:
   - the second coordinate has valuation `v_1`;
   - the other two have valuation `>= min(v_2, v_3) >= v_1 + 2`.
4. Let `x ∈ X_2`, with common valuation `v`. The coordinates of `B x` have
   valuations `v - 1`, `v` and `v`.
   - For the third, `v(t x_3) = v + 1 > v = v(x_2)`.
   - So `B x ∈ Y_1`.
5. Let `x ∈ X_3`.
   - `v(t^{-1} x_1) = v_1 - 1 >= v_2 + 1`, so the first coordinate has
     valuation `v_2`.
   - The second coordinate is `x_2`.
   - `v(t x_3) = v_3 + 1 >= v_2 + 3`, so the third coordinate has valuation
     `v_2`.
   - So `B x ∈ X_2`.
6. `T^2 x = (-x_2 + x_3, -x_2, x_1 - x_2)`. For `x ∈ X_1`:
   - the third coordinate has valuation `v_1`;
   - the other two have valuation `>= v_1 + 2`.

**Consequence.** Let `n >= 3`. Chaining facts 1, 4 and 5 gives
`B^n (X_1 ∪ X_2 ∪ X_3) ⊆ X_1`:

- `X_3 -> X_2 -> Y_1 -> Y_2 = X_1`, after which `B` keeps `Y_d ⊆ X_1`;
- `X_2 -> Y_n ⊆ X_1`;
- `X_1 -> Y_{n+2} ⊆ X_1`.

**Configuration.** Put

```text
S_{B+} = X_1,   S_{A+} = T X_1 ⊆ X_2,   S_{A-} = T^{-1} X_1 ⊆ X_3,   S_{B-} = T^2 X_1 ⊆ X_4.
```

These sets are nonempty (`e_1 ∈ X_1`), clopen and pairwise disjoint. Use
`T^4 = 1`, `A = T B T^{-1}`, `A^{-1} = T^{-1} B T` and `B^{-1} = T^2 B T^2`,
and let `m, n >= 3`.

- **`B^n`.** `S_{B+} ∪ S_{A+} ∪ S_{A-} ⊆ X_1 ∪ X_2 ∪ X_3`, which `B^n` maps
  into `X_1 = S_{B+}`.
- **`B^{-n} = T^2 B^n T^2`.** `T^2` maps `S_{B-}`, `S_{A+}` and `S_{A-}` to
  `X_1`, `T^3 X_1 = T^{-1} X_1 ⊆ X_3` and `T X_1 ⊆ X_2` respectively.
  Then `B^n` maps into `X_1`, and `T^2` maps `X_1` onto `S_{B-}`.
- **`A^m = T B^m T^{-1}`.** `T^{-1}` maps `S_{A+}`, `S_{B+}` and `S_{B-}` to
  `X_1`, `T^{-1} X_1 ⊆ X_3` and `T X_1 ⊆ X_2` respectively.
  Then `B^m` maps into `X_1`, and `T` maps `X_1` onto `S_{A+}`.
- **`A^{-m} = T^{-1} B^m T`.** `T` maps `S_{A-}`, `S_{B+}` and `S_{B-}` to
  `X_1`, `T X_1 ⊆ X_2` and `T^3 X_1 ⊆ X_3` respectively.
  Then `B^m` maps into `X_1`, and `T^{-1}` maps `X_1` onto `S_{A-}`.

So `(S_{A±}, S_{B±})` is a clopen 4-set ping-pong for `(A^m, B^n)` on
`P^2(F((t)))`.

**Transfer to `(f^m, k^n)`.**

- Let `σ: F((t)) -> F((t))` be the continuous automorphism `t -> -t`; it is
  the identity if `char F = 2`.
- `σ` preserves `v`, so it fixes every `S` set.
- Applying `σ` coordinatewise gives `A^σ x^σ = (A x)^σ`. Hence the same sets
  are a ping-pong for `(A^{σ m}, B^{σ n})`.
- `P ∈ GL_3(F(t))` is invertible over every `F`, because `det P` is a monic
  polynomial up to sign, and `P A^σ P^{-1} = f`, `P B^σ P^{-1} = k`.
- So `P S_{A±}, P S_{B±}` is a clopen 4-set ping-pong for `(f^m, k^n)` on
  `P^2(F((t)))`. ∎

**Which square transitions the BBT sets handle.** Take `m = n = 2` and the
same sets.

- Fact 4 gives `B^2 X_2 ⊆ Y_2 = X_1`, but fact 5 only gives
  `B^2 X_3 ⊆ Y_1`.
- So `B^2` maps `S_{A+} ∪ S_{B+}` into `S_{B+}`, but not `S_{A-}`.
- Conjugating by powers of `T` shows that each square letter is handled only
  after a letter of one sign:
  - `A^{-2}` after `B^{+}`;
  - `B^{-2}` after `A^{-}`;
  - `A^{2}` after `B^{-}`;
  - `B^2` after `A^{+}`.
- Reduced words whose consecutive syllables follow the cycle
  `A^+ -> B^+ -> A^- -> B^- -> A^+`, reading right to left, are therefore
  covered with all exponents `>= 2`. Every other transition needs exponent
  `>= 3`.

This is BBT Theorem 3.1 in `A, B` language (their condition "`n_i >= 2`
whenever `m_{i-1} = 1`"). `bbt_sets_test.py` finds failures for `m = n = 2`
in exactly four of the eight (target, source) pairs.

## 5. Closedness is essential

**Proposition 5.1.** Let `K` be an uncountable field and `g, h ∈ GL_3(K)`.
A 4-set ping-pong for `(g, h)` on `P^2(K)`, with arbitrary sets, exists iff
`<g, h>` is free on `g, h`.

*Proof.* "Only if" is the ping-pong argument of section 1. For "if", let
`G = <g, h>` be free on `g, h`.

1. **No nontrivial scalars.** A nontrivial scalar would be central in `G`,
   but a free group of rank 2 has trivial center.
2. **A point with trivial stabilizer.**
   - Each `γ ∈ G \ {1}` is a non-scalar matrix. So its fixed set in
     `P^2(K)`, the union of its projectivized eigenspaces, lies in a finite
     union of lines.
   - `G` is countable, so these fixed sets lie in countably many lines `L_j`.
   - There are uncountably many lines, so pick a line `L` not among the
     `L_j`. Each `L_j` meets `L` in at most one point, and `L` has
     uncountably many points.
   - So some `x ∈ L` has trivial stabilizer in `G`.
3. **The configuration.** For each generator letter `c ∈ {g^{±1}, h^{±1}}`,
   let `X_c = {w x : w a reduced word whose leftmost letter is c}`.
   - Left multiplication by `g^{±1}` sends a reduced word beginning with
     `g^{±1}`, `h` or `h^{-1}` to a reduced word beginning with `g^{±1}`.
     The same holds for `h^{±1}`.
   - The sets are nonempty.
   - They are pairwise disjoint, because `w -> w x` is injective. ∎

`P^2(F((t)))` is uncountable for every field `F`. So over `F((t))`:

- **Arbitrary sets.** A 4-set ping-pong for `(A^2, B^2)`, or for
  `(f^2, k^2)`, exists iff `<A^2, B^2>` is free. Asking for a configuration
  with arbitrary sets is a restatement of the problem.
- **Closed sets.** Corollary 3.3 shows that closed configurations do not
  exist.
- **The gap between them.** The two statements differ in how the
  hypothetical ping-pong sets sit near the eigenflags of `f` and `k`. Any
  such sets would have to be non-closed there, like the orbit-type sets in
  the proof above.

## 6. Scope

**What is covered.**

- **Ambient spaces.** 4-set ping-pong on `P^2(K)` and on its dual, for any
  absolute value with `|t_0| != 1`: archimedean or not, and any
  characteristic.
- **Pairs.** `(f^m, k^n)` and `(A^m, B^n)`.
- **The obstruction.**
  - If `n <= 2`, the two `f`-sets cannot both be closed.
  - If `m <= 2`, the two `k`-sets cannot both be closed.

**What is not covered.**

1. **Other spaces.** Ping-pong on the flag variety, on the Bruhat–Tits
   building (the Witzel–Zaremsky setting; their Remark 3.5 notes that closed
   rays do not separate for squares), or on `P^2` over a completion where
   `|t_0| = 1`. Nothing here rules out building sets.
2. **The 2-set form.** Here `X_g ∪ X_h` with `g^j X_h ⊆ X_g` for `j != 0`.
   - The 4-set form implies the 2-set form. The converse is not claimed.
   - Lemma 2.1 uses the separate sets `X_{a+}` and `X_{a-}` to place `p_0`
     in both.
   - With a single closed `X_a`, the same Step 1 argument places `p_+`,
     `p_-` and `p_0` in `X_a`. This is not a contradiction by itself, so the
     2-set closed case is **open here**.
3. **Other generating pairs and word-adapted arguments.**
   - Ping-pong for a different generating pair of the same subgroup, for
     example after Nielsen moves.
   - Arguments adapted to particular words, such as the transition
     bookkeeping of BBT's Theorem 3.1.
4. **Freeness itself.** Nothing here says whether `<A^2, B^2>` is free.

**Numerical evidence (not proof).** Computed by `growth.py 2 5`, which uses
`lp.py`, in the experiments folder; it enumerates all 324 reduced words of
length 5.

- For `(f^2, k^2)`, the minimum over reduced words of length `L` in
  `f^{±2}, k^{±2}` of the gap `λ_1 - λ_3` between Cartan (valuative) exponents
  is:

  | `L` | 1 | 2 | 3 | 4 | 5 |
  |---|---|---|---|---|---|
  | min gap | 4 | 7 | 9 | 12 | 14 |

  Here `λ_1` is the maximum `t`-degree of an entry, and `λ_1 + λ_2` the
  maximum degree of a 2×2 minor.
- This is consistent with linear growth and no short relations, but it
  proves nothing.

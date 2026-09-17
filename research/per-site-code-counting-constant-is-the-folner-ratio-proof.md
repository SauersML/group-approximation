---
rg: 2
id: per-site-code-counting-constant-is-the-folner-ratio-proof
kind: route
title: Count sites against codewords for the upper bound, split each site into m pieces along a Hall reader field for the lower bound, and mass-transport the field
target: per-site-code-counting-constant-is-the-folner-ratio
requires:
  - bernoulli-window-codeword-folner-ratio-bound
  - nonamenable-groups-carry-arrow-shift-strict-automata
---

Notation is as in the target claim. Entropies are in nats. The action is `(k.rho)(g) = rho(k^(-1) g)`.

**Import.**
- **(H) Marshall Hall, 1948.** A family of finite sets has a system of distinct representatives iff every finite
  subfamily of size `r` has a union with at least `r` elements. This is the same import (H) that the established route
  `arrow-shift-strict-automata-proof` uses. It is not re-pinned here, and only the "if" half is used, in Step 2.

**Step 1: the count (item 1).**
- Fix a finite nonempty `S <= G`. Since `x|_S` is uniform on `(A^k)^S`,

      |S| k log q = H(x|_S) <= H(y_(SF)) + H(x|_S | y_(SF)).

- **Subadditivity.** `H(y_(SF)) <= sum_(g in SF) H(y_g) <= |SF| c`.
- **Decoding.** `H(x|_S | y_(SF)) <= sum_(t in S) H(x(t) | y_(SF)) <= sum_(t in S) H(x(t) | y_(tF)) <= |S| d`, because
  `tF <= SF` and conditioning on more lowers entropy.
- Divide by `|S|` and take the infimum over `S`. This gives `k log q <= lambda(F) c + d`.
- Since `lambda(F) >= 1` for nonempty `F`, the right side is at most `lambda(F)(c + d)`. So `kappa(F) <= lambda(F)`.
- Only the per-site costs of the family enter.

**Step 2: reader fields (item 2).**
- **Only if.** Let `rho in Y_(F,m)` and write `r(h, i)` for the unique `g` with `rho(g) = (i, g^(-1) h)`. Then
  `r(h, i) in hF`. It is injective on `G x [m]`, since `rho(g)` records both `i` and `h = g (g^(-1) h)`. For finite
  nonempty `S`, the map `r` sends `S x [m]` injectively into `SF`, so `|SF| >= m|S|` and `lambda(F) >= m`.
- **If.** Suppose `lambda(F) >= m`. The targets are `(h, i) in G x [m]`, and each has candidate set `hF`. A finite set
  of targets with projection `P` has at most `m|P|` elements, and its candidates form `PF` with `|PF| >= m|P|`.
- So by (H) there is an injective `r : G x [m] -> G` with `r(h, i) in hF`.
- Put `rho(g) = (i, g^(-1) h)` if `g = r(h, i)`, and `rho(g) = *` otherwise. This is well defined by injectivity,
  `g^(-1) h in F^(-1)`, and `g = r(h, i)` is the only `g` with `rho(g) = (i, g^(-1) h)`. So `rho in Y_(F,m)`.
- **Invariance and finite type.** If `rho in Y_(F,m)` and `k in G`, the unique witness for `(h, i)` in `k.rho` is
  `k r(k^(-1) h, i)`. Membership is checked at each `h` on the finite window `hF`.

**Step 3: the Hall family (item 3).**
- Let `rho in Y_(F,m)` with injection `r` as in Step 2, `n >= 1` and `k = mn`. Split `x(h) in A^(mn)` into blocks
  `x(h)_1, ..., x(h)_m in A^n`.
- Define `y_g = x(g u)_i` if `rho(g) = (i, u)`, and `y_g = *` if `rho(g) = *`.
- **Local rules.** Since `u in F^(-1)`, `y_g` reads `x` only on `g F^(-1)`. So `E = F^(-1)`, `B = A^n ∪ {*}`, and
  `psi_g` depends on `g` only through `rho(g)`. That gives at most `m|F| + 1` rules.
- **Decoding.** For every `t`, `x(t)_i = y_(r(t, i))`, and `r(t, i) in tF`. So `x(t)` is a function of `y_(tF)`, and
  `d = 0`. Globally `y` determines `x`.
- **Site entropy.** `H(y_g) <= log |B| = n log q + log(1 + q^(-n))`.
- **Ratio.** `k log q / (c + d) >= mn log q / (n log q + log(1 + q^(-n)))`, which tends to `m` as `n -> infinity`.
  So `kappa(F) >= m` for every integer `m <= lambda(F)`.
- With Step 1, `floor(lambda(F)) <= kappa(F) <= lambda(F)`.

**Step 4: group dichotomy (item 4).**
- **Amenable.** By `bernoulli-window-codeword-folner-ratio-bound`, `lambda(F) = 1` exactly when `<F F^(-1)>` is
  amenable. So if `G` is amenable, `lambda(F) = 1` for every `F`, and Step 3 gives `kappa(F) = 1`.
- **Nonamenable.** By item 1 of `nonamenable-groups-carry-arrow-shift-strict-automata`, there are a finite symmetric
  `S` containing `e` and a map `f : G -> G` with `f(g) in gS` and `|f^(-1)(h)| >= 2` for all `h`.
  - Distinct points have disjoint fibres, so induction on `r` gives `|(f^r)^(-1)(h)| >= 2^r`.
  - By symmetry of `S`, `(f^r)^(-1)(h) <= hS^r`.
  - Fix a total order on `S^r`. Let `r(h, i)` be the `i`-th element of `(f^r)^(-1)(h)`, ordered by the offset
    `h^(-1) g`, for `i <= 2^r`.
  - This is injective on `G x [2^r]` with `r(h, i) in hS^r`. The definition of Step 2 then gives a point of
    `Y_(S^r, 2^r)`.
  - So Step 3 gives `kappa(S^r) >= 2^r`, with no use of (H). In particular `kappa(S) >= 2 > 1`.
- This proves the dichotomy.

**Step 5: the gate (item 5).**
- Let `mu` be a `G`-invariant Borel probability measure on `Y_(F,m)` and fix `i in [m]`.
- Exactly one `g` has `rho(g) = (i, g^(-1))`, the witness for `(e, i)`. Summing the indicators over `g in G`,
  countable additivity gives `1 = sum_(g in G) mu(rho(g) = (i, g^(-1)))`.
- `rho(g) = (g^(-1).rho)(e)` and `mu` is invariant, so `rho(g)` has the law of `rho(e)`. So the sum equals
  `sum_g mu(rho(e) = (i, g^(-1))) = mu(rho(e) in {i} x F^(-1))`.
- Summing over `i` gives `m = mu(rho(e) != *) <= 1`, which is impossible for `m >= 2`.

**Step 6: the enlargement remark in Consequences.**
- For `F <= F'`, `H(x(1) | y_(F')) <= H(x(1) | y_F)`, so `Phi` does not increase. Also `|SF'| >= |SF|`, so
  `lambda(F') >= lambda(F)`.
- Applying the definition of `lambda` to `SF^(j-1)` gives `|SF^j| >= lambda(F)|SF^(j-1)|`, hence
  `lambda(F^j) >= lambda(F)^j`.
- A deficit witness has `lambda(F) > 1` by `bernoulli-window-codeword-folner-ratio-bound`. Replacing `F` by
  `F ∪ F^j` gives `lambda >= 2^j` for large `j` without raising `Phi`.

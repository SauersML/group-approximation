---
rg: 2
id: torsion-free-single-defect-rules-need-strict-linear-parts-proof
kind: route
title: Build a one-defect correction witness whose background is chosen by a capacity matching that Kemperman's inequality feeds
target: torsion-free-single-defect-rules-need-strict-linear-parts
requires:
  - avoidable-patches-of-affine-rules-inherit-linear-injectivity
  - kemperman-torsion-free-product-sets-grow
---

**Conventions.**
- `tau(x)(g) = mu((x(gm))_(m in M))`, `(Lx)(g) = sum_m c_m x(gm)`, and `x|_(gM)` is the pattern `m -> x(gm)`.
- `D(x)(g) = t [x|_(gM) = p]`, so `tau(x) = Lx + c + D(x)`.
- `L` is a `G`-equivariant linear map of `F_q^G`.

**Step 1 (linear part injective).** `mu` differs from `lambda = sum_m c_m x_m + c` only at the pattern `p`.
Fix `m_0 in M` and `s = p_(m_0)`. Then `mu` agrees with `lambda` on every pattern in which `s` does not occur.
Since `q >= 3`, `avoidable-patches-of-affine-rules-inherit-linear-injectivity` applies: if `tau` is injective,
then `L` is injective.

**Step 2 (reduction).** It remains to show that `L` is not surjective. Suppose it is. Then some `w in F_q^G`
has `Lw = delta_e`. No finiteness of the support of `w` is needed. Evaluating at `e`,

```text
sum_m c_m w(m) = 1,   so   w|_M != 0.
```

We build `x` with

```text
(W1)  x|_M = p;
(W2)  x|_(gM) != p           for every g != e;
(W3)  x'|_(gM) != p          for every g in G, where x' = x + t w.
```

Given these, `D(x) = t delta_e` and `D(x') = 0`. Then

```text
tau(x') = Lx + t Lw + c + 0 = Lx + t delta_e + c = Lx + c + D(x) = tau(x).
```

Also `x' != x`, since `w != 0` and `t != 0`. This contradicts injectivity of `tau`. So `L` is injective and
not surjective, which is the theorem.

At `g = e`, (W3) holds automatically: `x'|_M = p + t w|_M != p`.

**Step 3 (translates leave M).** Let `g != e`. If `gM ⊆ M`, then `gM = M` since `|gM| = |M|`. So
`g^i m in M` for all `i >= 0`, where `m in M` is fixed. Two of these coincide, and then `g^k = e` for some
`k >= 1`. Because `G` is torsion-free, `g = e`. Hence `S_g := gM \ M` is nonempty for `g != e`, and
`|S_g| <= |M|`.

**Step 4 (the events).** The free coordinates are `x(h)` for `h notin M`; `x` is fixed to `p` on `M`. For
`g != e` there are two events.
- `A_g`: `x|_(gM) = p`.
- `B_g`: `x'|_(gM) = p`, that is, `x(gm) = p_m - t w(gm)` for all `m`.

Each event prescribes one value `v_E(h)` for every `h in gM`. If a prescription on `gM ∩ M` disagrees with
the fixed values, then the event is impossible and we discard it. Otherwise the event holds exactly when
`x(h) = v_E(h)` for every `h in S_g`. So the event fails as soon as one free coordinate `h in S_g` takes a
value other than `v_E(h)`.

**Step 5 (finite capacity matching).** Let `F ⊂ G \ {e}` be finite, and let `E_F` be the set of surviving
events `A_g, B_g` with `g in F`. Form the bipartite graph from `E_F` to the coordinates `FM \ M`, joining
`E` (for `g`) to every `h in S_g`.

For `E' ⊆ E_F`, let `Gamma ⊆ F` be the set of `g` that `E'` involves. Then `|E'| <= 2|Gamma|`, and the
neighbourhood of `E'` is `Gamma M \ M`. By `kemperman-torsion-free-product-sets-grow` (derived form, with
`C = M`), and because `q >= 3`,

```text
(q - 1) |Gamma M \ M|  >=  (q - 1) |Gamma|  >=  2 |Gamma|  >=  |E'|.
```

Replace each coordinate by `q - 1` copies. Hall's marriage theorem for finite bipartite graphs then gives a
map `phi: E_F -> FM \ M` with `phi(E) in S_g` for `E` at `g`, and at most `q - 1` events on each coordinate.

For each `h`, the values `{v_E(h) : phi(E) = h}` number at most `q - 1 < q`. So choose `x(h)` in `F_q`
outside them, and set `x(h) = 0` at the remaining free coordinates. Every event of `E_F` then fails at its
coordinate `phi(E)`. So the set

```text
C_F = { x in F_q^(G \ M) : (W2) and (W3) hold at every g in F }
```

is nonempty.

**Step 6 (compactness).** Each `C_F` is clopen in the compact space `F_q^(G \ M)`, since every event depends
on the finitely many coordinates of `gM`. Also `C_(F_1) ∩ C_(F_2) ⊇ C_(F_1 ∪ F_2) != ∅`. So the family has
the finite intersection property. Any `x` in `∩_F C_F`, extended by `p` on `M`, satisfies (W1)-(W3). This
completes Step 2 and the proof. ∎

**Part (b): arbitrary groups, large fields.** Now let `G` be any group, and suppose `q >= 2|M| + 1` and
that no `g != e` has `gM = M`. Steps 1, 2, 4 and 6 do not use torsion-freeness.
- *Step 3.* It holds as written: `gM ⊆ M` forces `gM = M`, hence `g = e`.
- *Step 5.* It needs no matching. A free coordinate `h` lies in `gM` only for `g in hM^-1`, so in at most
  `|M|` translates, and hence in at most `2|M| <= q - 1` events. Assign each event of `E_F` to any
  coordinate of its (nonempty) `S_g`. Then each `h` carries at most `q - 1` forbidden values, and the rest
  of Step 5 is unchanged.

**Where the hypotheses enter.**
- *Torsion-freeness* enters twice: in Step 3, which also follows from Kemperman with `Gamma = {g}`, and in
  Step 5, through the product-set bound.
- *`q >= 3`* enters in Step 1 and in the capacity `q - 1 >= 2` of Step 5.
- *Neither the finiteness of `L^-1` nor its support is used.* This is why the exceptional translates of
  `constant-background-kills-unit-linear-defect-rules` (`hM ⊆ M ∪ N^-1`) do not arise: the background is not
  constant, and it is chosen coordinate by coordinate against both defect fields at once.

**Imports and standard facts.**
- Kemperman's inequality is imported, with a verbatim quotation, in
  `kemperman-torsion-free-product-sets-grow-citation`.
- Hall's marriage theorem for finite bipartite graphs, in the capacity form obtained by duplicating vertices,
  is textbook combinatorics. So is Tychonoff's theorem for finite discrete factors.

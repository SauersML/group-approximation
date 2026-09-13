# Right-cancellative incidence patterns: a loop firewall for Rokhlin-window domination

Lane w7-inf-cancellative, 2026-09-12. Status: every result here is written out in full and is
**held OPEN until w4-vf-positive-b re-derives it**. Logs are base 2 and `q = 2`, so `log q = 1` bit.

Sources, all on main:
- `research/artifacts/rokhlin-window-random-order-transport-2026-09-12.md`: Theorem 1, Corollary 2,
  Propositions 3, 4 and 6, Examples 5 and 8, the Z/5 parity code, and the finite-model Section 7.
- `bernoulli-rokhlin-deficit-has-a-finitary-witness`: `Phi` depends only on the incidence
  pattern, and every group pattern has a canonical host.
- `bernoulli-witness-information-is-bounded-by-code-reads`: the read bound `I <= m H(psi)`.

## 0. Summary

1. **Firewall (Theorem A plus Theorem B).** Some incidence patterns satisfy both cancellation laws,
   are realized inside finite loops, and have `Phi -> 0` at a special site.
2. **Which axiom (Theorem C).** No group realizes these patterns. The proof uses associativity
   twice, in the form of translation invariance (the quadrangle closure). So a domination proof must
   use associativity, not just cancellation, division, identity or a finite index set.
3. **Finite-model step (Section 5).** In the loop the whole loop is a finite index set closed under
   the codewords, yet `Phi(o) -> 0`. Counting only gives domination on average over sites, and
   converting that into domination at `o` is a translation step. So the finite-model step and the
   translation step are independent inputs.
4. **End-fixing tree (Section 6).** A pointer code on `T_3` fixing an end has `Phi -> 0` at every
   site, under a transitive automorphism group. It violates right cancellation, as the modular
   function forces. Right-cancellative downward windows on the tree are free-monoid patterns, so
   they are dominated.
5. **Decision.** Domination is REFUTED for abstract right-cancellative patterns. Domination for
   associative patterns is the original open problem (INF), and I did not prove it.

## 1. Abstract patterns

An **abstract pattern** consists of:
- a finite set `F` of codewords, a finite set `E` of positions, and a set of sites;
- a reading map `w : F × E -> sites`, `(f, e) -> w_f(e)`;
- a special site `o`.

Its axioms:
- **(L) Left cancellation:** each row `w_f` is injective, so every codeword reads `|E|` distinct
  sites.
- **(R) Right cancellation:** each column `w_(.)(e)` is injective, so distinct readers of one site
  read it at distinct positions.

So a pattern is a partial Latin rectangle with rows `F`, columns `E` and symbols the sites.
- With `x` iid uniform on `A^k` over the sites, put `y_f = psi((x(w_f(e)))_(e in E))`.
- Put `Phi = (1/k)[H(psi(iid)) + H(x(o) | y_F)]`.
- Under (L) each `y_f` has the law of `psi(iid)`.

A group `G` **realizes** the pattern if there are injections `F -> G`, `E -> G` and sites `-> G`,
with `o -> 1`, such that `w_f(e)` maps to `f e` and no two distinct sites are identified. Group
patterns satisfy (L) and (R). By the finitary witness theorem, a realized pattern with `Phi < log q`
is a Rokhlin deficit of its host.

## 2. Theorem A: the shared-pointer parity gadget

Fix `k = 2^t`, a number `R` of gadgets, and an odd `n = 2m + 1 >= R`.
- **Positions:** three pointer positions `P1, P2, P3` and value positions `Z/n`, so `|E| = n + 3`.
- **Code:** `psi(p_1, p_2, p_3; v_0, ..., v_(n-1)) = (j, XOR_i v_i[j])`, where
  `j = (p_1|_t + p_2|_t + p_3|_t) mod 2^t` and `p|_t` is the first `t` bits.
- `psi` is symmetric in the pointer inputs and symmetric in the value inputs.
- `H(psi(iid)) = t + 1`: `j` is uniform, and given `j` the XOR bit is a fresh uniform bit.

**Gadget `g`** (`g in Z/n`, `0 <= g < R`) uses:
- the shared site `x0 = o`;
- fresh sites `alpha_1..alpha_m`, `beta_1..beta_m`, `gamma_1..gamma_(m+1)`;
- fresh pointer sites `a, b, c`.

It has three codewords, with positions taken mod `n`:

| codeword | pointers at `(P1,P2,P3)` | value positions |
|---|---|---|
| `W_1^g` | `(a, b, c)` | `x0` at `g`; `alpha_i` at `g+i`; `beta_i` at `g+m+i` |
| `W_2^g` | `(b, c, a)` | `alpha_i` at `g+i-1`; `gamma_l` at `g+m+l-1` |
| `W_3^g` | `(c, a, b)` | `beta_i` at `g+m+i-1`; `gamma_l` at `g+l-2` |

**Cancellation check.**
- **(L):** each row fills all `n` value positions with distinct fresh sites (plus `x0` in `W_1`).
- **(R):**
  - each pointer site sits at three distinct pointer positions;
  - `alpha_i` sits at `g+i` and `g+i-1`, and `beta_i` at `g+m+i` and `g+m+i-1`;
  - `gamma_l` sits at `g+m+l-1` and `g+l-2`, which differ by `m+1`, nonzero mod `n`;
  - `x0` sits at position `g` in `W_1^g` only, and the `g` are distinct.
- Mask sites are local to their gadget.

**Decoding.**
- The value windows satisfy `W_1 Δ W_2 Δ W_3 = {x0}`: `A∪B∪{x0}`, `A∪C` and `B∪C`.
- All three codewords output the same pointer `j_g`.
- XOR of their three output bits gives `x0[j_g]`.
- The `j_g` are functions of disjoint pointer sites, so they are iid uniform on `[k]`.
- Hence `H(x0 | y_F) <= E #{coordinates not hit} = k (1 - 1/k)^R <= k e^(-R/k)`.

**Theorem A.** With `R = ceil(2 k ln k)` and `n` the least odd integer `>= R`, the pattern satisfies
(L) and (R), `psi` is non-affine, and

    Phi <= (log2 k + 1 + 1/k) / k  ->  0.

**Hand checks.**
- `k = 4`: `R = 12`, `n = 13`, residual `4 (3/4)^12 = 0.127`, `Phi <= 0.782 < 1`.
- `k = 8`: `R = 34`, `n = 35`, residual `8 (7/8)^34 = 0.085`, `Phi <= 0.511`.
- `k = 2`: `R = 3`, `n = 3`, residual `0.25`, `Phi <= 1.125`, so this size gives no deficit.

**Consistency with the read bound.** `o` has `R` readers, and `I(x0; y_F) <= k <= R (t + 1)`.

**Why the overlaps matter (fresh petals are dominated).**
- Suppose the readers of `o` read it at distinct positions and their other inputs are fresh.
- Then `sum_f I(x(o); y_f) <= sum_p I(v_p; psi) <= I(v; psi) <= H(psi)`, by superadditivity for
  independent inputs.
- This is Proposition 3 under (R). The gadget beats it only through the non-readers `W_2`, `W_3`,
  which cancel the masks.

## 3. Theorem B: finite loops realize every cancellative pattern

**Theorem B.** Every finite pattern satisfying (L) and (R) is realized, with no extra coincidences,
by the multiplication `c · e` of a finite loop.

**Proof.**
1. Pad the rectangle to a partial Latin square of order `N = max(|F|, |E|, #sites)`.
2. Evans (T. Evans, *Embedding incomplete latin squares*, Amer. Math. Monthly 67 (1960) 958-961):
   it embeds in a Latin square of order `2N`. That square is the table of a quasigroup `Q`.
3. The old cells are unchanged, so `F · E` in `Q` is exactly the pattern.
4. An isotope `x ∘ y = (x / v) · (u \ y)` is a loop with identity `u · v`. Take `v = u \ o`, so `o`
   is the identity. Relabelling rows `f -> f · v` and columns `e -> u · e` gives
   `(f · v) ∘ (u · e) = f · e`, so the incidence is unchanged.

So finite loops (identity, both division laws, finite) carry configurations with `Phi(o) -> 0`.

## 4. Theorem C: no group realizes the gadget, and where associativity enters

**Theorem C.** No group `G` contains codewords `c_1, c_2, c_3` and a window `E = P ⊔ E_val` with
`|P| = 3`, `c_1 P = c_2 P = c_3 P` as sets, and `c_1 E_val Δ c_2 E_val Δ c_3 E_val` a single
element. In particular no group realizes one gadget of Theorem A.

**Proof.**
1. **The shift.** Put `delta = c_1^-1 c_2`. Then `delta P = P`, using associativity and inverses:
   `c_2 p = c_1 (delta p)`.
2. **The stabilizer.** The left stabilizer `K = {g : g P = P}` acts freely on `P`, since `g p = p`
   forces `g = 1`. So `|K|` divides `3`.
3. **The cyclic triple.** `delta != 1`, so `K = <delta> ≅ Z/3`. Likewise `c_1^-1 c_3 ∈ K` and
   `c_3 != c_2`, so `c_3 = c_1 delta^2`.
4. **The ring identity.** In `F_2[G]`, symmetric difference is addition, and `1_(c E) = c Ê` with
   `Ê = sum_(e in E_val) e`. This uses associativity again: `(c_1 delta) e = c_1 (delta e)`. So
   `c_1 (1 + delta + delta^2) Ê = x0`.
5. **The contradiction.** Multiply on the left by `c_1 (1 + delta) c_1^-1`. The left side becomes
   `c_1 (1 + delta^3) Ê = 0`. The right side becomes `x0 + (c_1 delta c_1^-1) x0 != 0`.

**The axiom a domination proof must use.**
- Theorems A and B show that (L), (R), identity, division, finiteness and a closed finite index set
  do not force domination.
- Theorem C kills the gadget in groups through two associativity steps:
  1. the shared reads of two codewords define one shift `delta`, the same at every shared site;
  2. that shift acts on all their other reads.
- This is the quadrangle (Reidemeister) closure: if `c e = c' e'`, `c r = c' r'` and `d e = d' e'`,
  then `d r = d' r'`. A Latin square satisfies it iff it is isotopic to a group table (Frolov; Brandt).
- In Theorem 1 the same axiom appears as `y_h(T_g x) = y_(gh)(x)`, i.e. `g(he) = (gh)e`. In
  Proposition 6 it appears as translation invariance `H(x(s) | y_(sF)) = H(x(1) | y_F)`.

So a proof of domination must use associativity through translation invariance of the pattern. The
star (Example 5) already shows it must also use right cancellation.

## 5. The finite-model step, checked in the loop

**Counting in the loop.**
- Let `Q` be the finite loop of Theorem B, of order `N`, with codewords at every `c in Q`.
- `Q` is closed under every codeword, with ratio `|Q E| / |Q| = 1`. This is Step 4 of Section 7 of
  the transport artifact.
- Counting gives `N k = H(x_Q) <= N H(psi) + sum_s H(x(s) | y_Q)`.
- So the average of `[H(psi) + H(x(s) | y_Q)]/k` over sites is at least `1`.

**What this does not give.** It does not bound `Phi(o)`. Theorem A puts at least
`N(k - t - 1) - k` bits of residual on sites other than `o`.
- In a group, translation invariance turns the average into a bound at `o`.
- In a loop the configuration seen from `s` (codewords `s·f` reading `(s·f)·e`) is not the translate
  of the one seen from `o`.

So the known trap has a second half. A proof that counts a finite index set proves average
domination, and the passage to `o` is a separate translation step that needs associativity. Neither
input implies the other.

## 6. The end-fixing tree

Let `T` be the 3-regular tree with a fixed end `ξ`, `p` the parent map toward `ξ`, and `Aut(T, ξ)`.
This group is amenable, non-unimodular and vertex-transitive.

**6.1. A homogeneous star (not right-cancellative).**
- **Code:** the codeword at `v` reads `(v, p(v), ..., p^d(v))`, and
  `psi(u_0, ..., u_d) = (j(u_0), u_1[j], ..., u_d[j])`, so `H(psi) = t + d`.
- **Readers:** site `o` is read at position `i` by its `2^i` descendants of depth `i`, each
  revealing `o[j(x(w))]` with iid pointers. That is `2^(d+1) - 2` reveals.
- **Bound:** take `d` least with `2^(d+1) - 2 >= 2 k ln k`. Then the residual is at most `1/k`, and
  `Phi <= (t + d + 1/k)/k -> 0` at every site, since `Aut(T, ξ)` is transitive.
- **Hand check:** `k = 256` gives `d = 11` and `Phi <= 0.075`.
- **Cancellation:** (R) fails at every `i >= 1`, and the excess `2^i` is the modular function.
- **Consistency:** the Proposition 6 count still holds on this transitive structure,
  `Phi >= 1/lambda(F)` with `lambda(F) = 2^d` (level counting), and it is not violated.

So homogeneity, amenability of the automorphism group and a composable partial translation do not
force domination. Right cancellation, equivalently unimodular reading, is needed.

**6.2. Right-cancellative windows on the tree.**
- The injective partial translations are the child maps.
- A window of descendants to depth `d`, with positions labelled by words in `{0,1}^(<=d)`, is (R)
  and (L).
- Any finite piece lies below a common ancestor `r`, and addresses relative to `r` embed it in the
  free monoid `{0,1}^*`, which lies inside the free group with no extra coincidences.
- So these patterns are dominated (free groups are sofic, hence Rokhlin-maximal).
- **Not done:** mixed windows with cousin types.

The tree is the firewall for **unimodularity**. The loop is the firewall for **associativity**.

## 7. Calibrations

- **Example 5 (star):** violates (R). Section 6.1 is its homogeneous version.
- **Proposition 3 (sunflower):** under (R) with fresh petals, superadditivity dominates it
  (Section 2). The gadget needs overlapping windows and non-readers, as Section 8 of the transport
  artifact requires.
- **Proposition 4 (affine codes):** the gadget code is non-affine (a pointer selects the coordinate).
- **Proposition 6 and Example 8:** both need translation invariance, which loops lack. The copy code
  has `H(psi) = |E| k`, so `Phi >= |E|`.
- **Z/5 parity:** `E = {0,1,2}`, `x(0) = y_1 + y_2 + y_4`, `Phi = 1` exactly. It is group-realized
  and dominated with equality.
  - In `F_2[Z/5]`, `1 + s + s^2` is a unit, so Theorem C's ring step does not bite without a shared
    pointer.
  - With a pointer set of size 3 the stabilizer is `Z/3`, where `(1 + s)(1 + s + s^2) = 0`.
- **Filters:** Section 8 of the transport artifact, `|E| >= 3`, and non-maximal `<E E^-1>`.
  - Theorem A has unbounded windows, as required.
  - The group filters do not apply, since loops are not groups.

## 8. Where it stopped, and the next lead

**Stopped.** I did not prove domination from (L), (R) and associativity; that is INF itself.
Cousin-type right-cancellative tree windows (6.2) are not decided.

**Next lead: shared-pointer gadgets in groups.**
- By Theorem C's steps 1-3, codewords sharing a pointer set `P` lie in `c_1 K` for a finite subgroup
  `K` acting freely on `P`, and the value XOR is `c_1 (sum_(K') kappa) Ê`.
- The ring test passes iff `sigma = sum_(K') kappa` is a unit of `F_2[K]`; for finite `K` a
  non-zero-divisor is a unit. For example `K = Z/5` with `K' = {1, s, s^2}` passes.
- Then `Ê = sigma^-1 c_1^-1 x0`, so `|E_val| <= |K| <= |P|`.
- So a group-realizable gadget whose code XORs all value inputs has a value window no larger than its
  pointer set.
- The lead is a code whose value part does not XOR over all value positions, or a large `K` with a
  unit `sigma`. That is the one construction that could turn Theorem A into an INF witness.

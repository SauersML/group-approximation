---
rg: 2
id: baumslag-gersten-groups-lie-in-class-c
kind: claim
title: The stable-letter subgroup of BS(1,n) has a rigid relative seed (a line sink carrying one global sign), so the Baumslag–Gersten group and its BS(1,n) analogues lie in class 𝒞; rigidity comes from the derived-subshift theorem, since the halving-coupled C_Z layers live only on the classical seed orbit
requires:
  - relative-seeds-glue-graphs-of-groups-into-class-c
  - quantum-rigidity-is-decided-on-the-derived-subshift
  - locally-finite-splittings-preserve-rigid-sft-compactifications
  - baumslag-gersten-seed-forcing-length-is-non-elementary
distinct_from:
  baumslag-gersten-seed-forcing-length-is-non-elementary: that proves (RS1) for a relative seed y_b of (BS(1,2), ⟨b⟩), measures the forcing length of the glued seed, and leaves (RS2) and (RS3) for y_b open; this adds three local rules to y_b, proves (RS1)–(RS3), and so puts the Baumslag–Gersten group in 𝒞.
  locally-finite-splittings-preserve-rigid-sft-compactifications: that puts BS(1,n) itself in 𝒞, with a vertex sink; this gives BS(1,n) a relative seed whose sink is a line, the axis of the stable letter.
  quantum-rigidity-is-decided-on-the-derived-subshift: that is the general reduction used here; this is its first application to an open rigidity question.
---

**ESTABLISHED** (lane proof, elementary; bh-invent-10, 2026-09-18; not independently reviewed). Route:
`baumslag-gersten-class-c-proof`. This closes the item left OPEN in
`baumslag-gersten-seed-forcing-length-is-non-elementary`.

## Setting

- `V_n = BS(1, n) = ⟨a, b | b a b^(-1) = a^n⟩` with `n ≥ 2`. Then `a^(nm) b = b a^m`.
- `T` is the Bass–Serre tree of `V_n` over `⟨a⟩`.
  - Its vertices are the cosets `h⟨a⟩`.
  - Each vertex `h⟨a⟩` has one *up* neighbour `hb^(-1)⟨a⟩` and `n` *down* neighbours `h a^i b⟨a⟩`,
    `i ∈ Z/n`.
  - Up-rays converge to one end `ω`.
  - The axis of `b` is the line `{b^k⟨a⟩}`.
- `BG_n = ⟨V_n, t | t a t^(-1) = b⟩`. `BG_2` is the Baumslag–Gersten group `⟨a, t | a^(a^t) = a^2⟩`.

## The relative seed `y_b^+` for `(V_n, ⟨b⟩)`

**Alphabet.** `↑` (a non-axis element), and axis letters `(axis, c)` with `c ∈ {+, *, −}`.

**Rules.**
- (T) Axis-ness is constant along `a`.
- (C) On axis cosets, the letters `c` follow `C_Z` along `a`: the allowed steps `c(h) → c(ha)` are `++`, `+*`,
  `*−` and `−−`.
- (LR) If `h` is axis, then `hb^(-1)` is axis, and exactly one of `h a^i b` (`i ∈ Z/n`) is axis.
- (Sg) If `h` and `hb` are both axis, they carry the same letter `c`.
- (Ax) If `c(h) = *`, then `hb` is axis.

**Seed.** `(axis, *)` at `1`.

**Forced point.** `y_b(b^k a^j) = (axis, σ(j))`, where `σ(j)` is `+` for `j < 0`, `*` for `j = 0` and `−` for
`j > 0`. Every other element carries `↑`.

Compared with `y_b` of the parent node, three changes are made:
- pointers are replaced by the single letter `↑`;
- (LR) and (Sg) are added;
- (Br) and exclusivity become consequences of (LR).

## Theorem

1. **(RS1).** `y_b` is the only point of `Y = Y_b^+` with the seed at `1`, and `Stab(y_b) = ⟨b⟩`.
2. **(RS2).** `Y` is the orbit closure of `y_b`. Its points are:
   - (α) the translates `h.y_b`;
   - (β) the *signed lines* `(L, ε)`: `L` is any line in `T` from `ω` to a down-end, every axis letter on `L` is
     `ε ∈ {+, −}`, and every other element carries `↑`;
   - (γ) the constant point `↑^(V_n)`.
3. **(RS3).** `Y` is `D`-quantum rigid over every field for all large `D`.
4. **Consequently** `(V_n, ⟨b⟩) ∈ 𝓡`, and `BG_n ∈ 𝒞` for every `n ≥ 2`, in particular the Baumslag–Gersten group.
   - More generally, a finite graph of groups lies in `𝒞` if its vertex groups are copies of `BS(1, n_i)`, and
     every edge group maps to a conjugate of `⟨a_i⟩` or of `⟨b_i⟩` (or to a finite-index subgroup of `⟨a_i⟩`) in
     the vertex group at each end.
   - This is by `relative-seeds-glue-graphs-of-groups-into-class-c`, with `(V_n, ⟨a⟩) ∈ 𝓡` and `V_n ∈ 𝒞` from
     the parents.

## How rigidity is obtained

- The derived subshift is `Y' = (β) ∪ (γ)`, a perfect set. Every signed line is a limit of signed lines with nearby
  down-ends.
- **Reduction.** `y_b` is locally forced, so `quantum-rigidity-is-decided-on-the-derived-subshift` reduces (RS3)
  to rigidity of `Y'`.
- **Rigidity of `Y'` by monotone chains** (route §3). On `Y'` the letters are
  - the axis idempotents `X_v` of the tree vertices, which increase toward `ω` and are pairwise orthogonal on
    incomparable branches;
  - one sign, which (Sg) propagates down the tree by `E_+^c = E_+^v X_c`.

  Both commute.
- **The parent's obstacle.** The coupled `C_Z` layers that `b` links by halving, `b^k a^(nj) b = b^(k+1) a^j`,
  exist only on the seed orbit (α). The derived-subshift theorem treats that orbit classically. On the boundary the
  layers collapse to a single global sign.

## Lesson for general BH

**A tower rung's rigidity is paid on the boundary, and there the sink data must collapse to finitely many global
parameters.**
- The Baumslag–Gersten rung was blocked by coupled counters on a line sink. After the derived-subshift reduction,
  the counters are invisible, because they live on the classical seed orbit. What remains is a tree-indexed line and
  one sign, and monotone chains handle both.
- **The recipe for further HNN rungs** over an infinite subgroup `C`:
  - give `(A, C)` a locally forced relative seed;
  - add local rules (like (LR) and (Sg)) until every seedless limit is determined by tree data plus finitely many
    globally propagated parameters;
  - then rigidity follows from monotone chains.
- **For CAP.** A hard membership problem must be carried by the forcing on the seed orbit, where it is free. It
  must not leave a non-collapsing residue on the boundary. Whether hard membership can be forced without such a
  residue is the rung-1c question in its sharpest form.

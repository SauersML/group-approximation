---
rg: 2
id: baumslag-gersten-seed-forcing-length-is-non-elementary
kind: claim
title: The Baumslag–Gersten group carries an explicit seed SFT, glued from relative seeds on BS(1,2), whose forcing length is non-elementary (at least a tower of height about log n), although its word problem is polynomial; so forcing length does not measure certified complexity, and BG lies in 𝒞 once one explicit relative seed for (BS(1,2), ⟨b⟩) is rigid
requires:
  - relative-seeds-glue-graphs-of-groups-into-class-c
  - locally-finite-splittings-preserve-rigid-sft-compactifications
  - heisenberg-rigid-seed-certifies-only-the-malcev-normal-form
distinct_from:
  heisenberg-rigid-seed-certifies-only-the-malcev-normal-form: that is rung 1b, where forcing length is quadratic and equals the distortion of the centre; this is rung 1c's distortion test, where forcing length is non-elementary while the word problem stays polynomial.
  relative-seeds-glue-graphs-of-groups-into-class-c: that is the gluing theorem; this supplies the two relative seeds the Baumslag–Gersten splitting needs, proves (RS1) for both, and leaves rigidity of one of them open.
---

**ESTABLISHED** for items 1–3 below (lane proof, bh-emitter-a, 2026-09-18; elementary; not reviewed).
**OPEN:** rigidity and orbit closure, (RS2) and (RS3), for the relative seed `y_b`.

## Setting

- **The groups.** `V = BS(1,2) = ⟨a, b | b a b^{-1} = a²⟩`, and
  `BG = ⟨a, t | a^{a^t} = a²⟩ = ⟨V, t | t a t^{-1} = b⟩`, an HNN extension of `V` along `⟨a⟩ → ⟨b⟩`.
- **Distortion.** `b^k a b^{-k} = a^{2^k}` and `b^k = t a^k t^{-1}`, so `|a^{2^k}| ≤ 2|a^k| + 5` in `BG`.
  - Put `N_0 = 1` and `N_{j+1} = 2^{N_j}`, a tower of height `j`. Then `|a^{N_j}| ≤ 6·2^j`.
  - So `⟨a⟩` has distortion at least `tower(log₂ n − 3)`, which is non-elementary.
- **Word problem.** `WP(BG)` is decidable in polynomial time. This is Myasnikov–Ushakov–Won, J. Algebra 345
  (2011), via power circuits (recalled, not re-read).
- **The tree of `V`.** In the Bass–Serre tree `T_V` of `V = ⟨a⟩ *_{a ↦ a²}`, the vertex `h⟨a⟩` has one neighbor
  `h b^{-1}⟨a⟩` ("up") and two, `h a^i b⟨a⟩` for `i ∈ Z/2` ("down-i", labeled relative to `h`).
  - The label shifts by `i ↦ i − 1` under `h ↦ ha`.
  - `b` is hyperbolic with axis `{b^k⟨a⟩}`.

## 1. The two relative seeds on `V` (RS1)

**`y_a` for `(V, ⟨a⟩)`.**
- The labels are the pointers of `locally-finite-splittings-rigid-compactification-proof` on `T_V` (up,
  down-0, down-1), plus `sink`, with its rules (T) and (X). The seed is `sink` at `1`.
- (RS1): the sink vertex `⟨a⟩` is forced, and then every pointer toward it. The stabilizer is the stabilizer of a
  vertex, `⟨a⟩`.
- Rigidity and orbit closure follow from the gluing theorem, since `⟨a⟩` is a vertex group (its statement 1,
  second bullet).

**`y_b` for `(V, ⟨b⟩)`.**
- **Labels.** `axis` or a pointer on the vertex part. On axis vertices, also a `C_Z` letter.
- **Rules.**
  - (T) along `a`, as for `y_a`. `axis` is constant along `a`, and axis vertices carry `C_Z` along `a`.
  - (Ax) `*` at `h` iff `*` at `hb`.
  - (Br) If `*` is at `h`, then `hab` is not `axis`.
  - (X) exclusivity on every edge, where axis vertices never point.
- **Seed.** `*` at `1`.
- **(RS1).**
  - (Ax) forces `*` exactly at `b^k`.
  - (T) and `C_Z` force the letters on the axis cosets `b^k⟨a⟩`, with `*` only at `b^k`.
  - (Br) and (X) force every other vertex to point toward the axis, by the tree argument of the parent (§2).
  - The stabilizer preserves the set of `*`-elements `⟨b⟩`, so it lies in `⟨b⟩`. Conversely, `b` maps the axis,
    the `*`-set and the letters `σ(j)` at `b^k a^j` to themselves.
  - So `Stab(y_b) = ⟨b⟩`.
- **What remains.** (RS2) and (RS3) for `y_b` are **open**. The axis is a sink that is a line, not a vertex. It
  carries coupled `C_Z` layers that `b` links by halving (`b^k a^{2j} b = b^{k+1} a^j`).

## 2. The glued seed over `BG` (C1)

- **The tree of `BG`.** At the vertex `hV` of the Bass–Serre tree of `BG`:
  - the `t`-edges are the cosets `c⟨b⟩` (to `c t V`);
  - the `t^{-1}`-edges are the cosets `c⟨a⟩` (to `c t^{-1} V`).
  - This is because `h b^k t = h t a^k`.
- **Types.** Each coset `hV` carries one of three types, constant along `a` and `b`:
  - `S`: the sink, carrying the rigid seed of `V` from the parent (a `T_V`-sink `⟨a⟩` with `C_Z` along `a`);
  - `P_t`: a `y_b`-layer, whose `*`-coset is the exit;
  - `P_{t^{-1}}`: a `y_a`-layer, whose `sink`-coset is the exit.
- **(Xt).** `h` is `P_t` and `*` iff `ht` is not (`P_{t^{-1}}` and `sink`). The sites `h` and `ht` are adjacent.
- **The seed.** Type `S` with the `V`-seed letter at `1`.
- **(C1) holds.**
  - The seed makes `V` the sink. For `h ∈ V`, (Xt) makes `ht` a sink element of a `y_a`-layer, along the whole
    coset `h⟨b⟩ t = ht⟨a⟩`, so each neighbor's layer is forced by its (RS1).
  - The same argument runs outward, using (Xt) in both directions.
  - The stabilizer fixes the unique sink `V` and then the `V`-seed point, so it is trivial.
  - The seed letter (type `S` plus the `V`-seed letter) occurs only at `1`.
- **Class `𝒞`.** By `relative-seeds-glue-graphs-of-groups-into-class-c`, `BG ∈ 𝒞` as soon as `y_b` also satisfies
  (RS2) and (RS3). The associated subgroups are exactly `⟨a⟩` and `⟨b⟩`.

## 3. Forcing length is non-elementary

- **Where the `±` values come from.** The `±` values of `C_Z` on the sink line `⟨a⟩ ⊂ V` enter only the `C_Z`
  rules along `a`.
  - (T), (X), (Ax), (Br) and (Xt) mention types, pointers, `sink` and `*`, never `±`.
  - Under unit propagation, `−` at `a^m` is derived only from `*` or `−` at `a^{m−1}`, since `−` may be preceded
    by `*` or `−`.
  - So forcing `y_*(a^N)` takes at least `N` steps.
- **The bound.** With `N = N_j` and `|a^{N_j}| ≤ 6·2^j`, the forcing length on `B_n` is at least
  `tower(log₂ n − 3)`.
- **Comparison.** Forcing length is non-elementary, but `WP(BG)` is polynomial. So no elementary function of
  word-problem complexity bounds the forcing length of a seed. Forcing length measures how long the forced
  counter is, not how hard it is to evaluate.

## 4. What it certifies

- **The membership problems.** By statement 3 of the gluing theorem, a rigid relative seed is a membership
  oracle for its subgroup. The seeds here encode membership in `⟨a⟩` and in `⟨b⟩` inside `V = Z[1/2] ⋊ Z`, both
  in polynomial time.
- **Evaluation.** `WP(BG) ≤ Eval(y_*)`, since `g = 1` iff the seed letter sits at `g`.
  - We expect `Eval(y_*)` to be polynomial through power circuits: every label is a sign, a parity or a tree
    position of a power-circuit normal form.
  - That is a sketch, not proved here.
- **Conclusion.** Either way, what the seed certifies is the power-circuit normal form, not the non-elementary
  distortion.

## Lesson for general BH

Distortion, even non-elementary distortion, certifies nothing: Baumslag–Gersten gets a seed with forcing length at
least a tower of height about `log n`, yet its word problem is polynomial.
- **Forcing length is an upper-bound resource.** It is design-dependent, and a global sign layer could shorten
  it. It is not a CAP invariant. This corrects the "bound forcing length" refinement proposed at rung 1b.
- **The CAP invariant is evaluation.** It is the complexity of evaluating the forced labels, that is, of the
  membership oracles the relative seeds must be.
- **Where the real rung 1c test lives.** It needs relative seeds for subgroups whose membership problem is hard,
  as in the Aanderaa–Cohen and Clapham towers of bh-invent-03. Distorted but easy subgroups such as `⟨a⟩ ⊂ BG` do
  not test CAP.

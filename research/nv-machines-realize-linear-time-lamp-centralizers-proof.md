---
rg: 2
id: nv-machines-realize-linear-time-lamp-centralizers-proof
kind: route
title: Clocked reversible stack machines in nV, a mirrored orbit of one cylinder, and a spare-bit detector whose setwise stabilizers read every branch of the unread tail
target: nv-machines-realize-linear-time-lamp-centralizers
requires:
  - permutational-boone-higman-iff-full-cantor-hosts
  - pbh-coset-wreaths-iff-identity-edge-hnns
---

Lane proof (bh-invent-11, 2026-09-18), not reviewed. Notation as in the target.

## 0. Hosts and bricks

- `nV` acts on `C^n`, where `C = {0,1}^N`.
- A **brick** is a product of cylinders. A **brick map** replaces a prefix in each coordinate.
- `nV` is **full**: every homeomorphism of `C^n` that is locally a brick map lies in `nV`.
- `nV` is **clopen transitive**: any two nonempty clopen sets are related by such a local map.

Both facts are from `permutational-boone-higman-iff-full-cantor-hosts` (via `pbh-full-cantor-hosts-proof`).

## 1. Stack machines as elements of nV

**Encoding.**
- Fix a finite alphabet containing a bottom marker `⊥`, and code its symbols by binary blocks of
  one length.
- Coordinate 1 begins with a header block `(c, z, q)`: copy bit `c`, spare bit `z`, state `q`.
  Stack 1 follows the header. Coordinates `2..n` hold stacks `2..n`, top first.
- A rule `ρ` reads the state and a bounded top word of each stack, writes a new state, and
  replaces those top words. On `C^n` it is a brick map `D_ρ → R_ρ`.
- Every rule reads and writes `z = 0`.

**Lemma 1 (completion).** Suppose the domains `D_ρ` are pairwise disjoint, and so are the images
`R_ρ`. Then some `f ∈ nV` agrees with every rule on its domain.

*Proof.* The rules define an `nV`-local homeomorphism `⋃D_ρ → ⋃R_ρ`. Both complements contain
`{z = 1}`, so they are nonempty clopen sets. By clopen transitivity, some `nV`-local homeomorphism
maps one complement onto the other. The union of the two maps is an `nV`-local homeomorphism of
`C^n`, and fullness puts it in `nV`. ∎

**Lemma 2 (history).** A deterministic machine, i.e. one with pairwise disjoint domains, becomes
reversible with the same step count when every rule also pushes its own index onto a history
stack `H`.

*Proof.* Distinct rules then write distinct top blocks on `H`, so their images are disjoint.
Every configuration evolves exactly as before, one step per step. ∎

## 2. The branch program for a verifier

Let `V` witness `S ∈ NLIN₁` with constant `c`, and fix `C >= c + 2`. The program uses stacks:
- `G` and `W`: the input tail and the certificate tail; unconstrained, read by popping;
- `K` and `K'`: the clock;
- `X_1, ..., X_m`: the work stacks of `V`, where `X_1` receives the input;
- `D`: idle pushes;
- `H`: history.

**The initial cylinder `U_0`.** It fixes the header `(c = 1, z = 0, r)`, where `r` is the reading
state, and requires top `⊥` on every stack except `G` and `W`.

**Phase R (reading).**
- In state `r` with `G`-top `1`: pop `G`, push a token on `K` and on `X_1`, and stay in `r`.
- In state `r` with `G`-top `0`: do the same, then pass to phase T.

A point whose `G`-tail starts `1^(s-1) 0` leaves phase R at time `s`, with `s` tokens on `K` and
on `X_1`. The tail `1^∞` reads forever.

**Phase T (clock and verification), exactly `(C-1)s` steps.** Each step does two things.
- **Clock.** Move one token between `K` and `K'`, direction by pass parity. A rule reads the top
  two symbols of the source stack, so the last move of a pass is recognized in the step that
  makes it. Pass `π ∈ {1, ..., C-1}` is kept in the state.
- **Verifier.** Run one step of `V` on `X_1, ..., X_m`, popping certificate bits from `W` when
  `V` reads them. Once `V` has halted, push junk on `D` instead and keep its verdict in the state.

`V` halts within `c·s < (C-1)s` steps, so the verdict is fixed before the clock ends.

**Emission.**
- The last step of pass `C-1` enters `q_W` if the verdict is accept, and `q_dorm` otherwise. So
  the state at time exactly `C·s` is `q_W` or `q_dorm`.
- From `q_W`, the next step goes to `q_dorm`.
- In `q_dorm` the program pushes junk on `D` forever.

**Result.** Only the state `q_W` is detected. A point of `U_0` whose tails encode `(s, w)` is in
`q_W` at time `t` iff `t = C·s` and `V` accepts `(1^s, w)`. At every time `t >= 1`, the clopen
image of `U_0` is a finite union of cylinders, one per tail prefix read so far. After Lemma 2 and
Lemma 1 the program is an element `f_S ∈ nV`. The rule domains cover every configuration reachable
from `U_0`, so `f_S` follows the program there.

**No return.** For `t >= 1`, `f_S^t(U_0)` is disjoint from `U_0`. Its points are in state `r` with
a token on top of `K`, or in a later phase. And `r` is never re-entered.

## 3. A mirrored orbit

Build `f_+ = f_{S_+}` and `f_- = f_{S_-}` on one layout, and define four involutions or elements.
- **`F`**: acts as `f_+` on `{c = 1}` and as `f_-^(-1)` on `{c = 0}`. It is a brick map piece by
  piece, so `F ∈ nV`.
- **`σ`**: the involution that flips `c` on the brick `{state r, K-top ⊥}`.
- **`g`**: the involution that flips `z` on `{state q_W}`.
- **`ε`**: the involution that flips the first bit below `⊥` on `D`, on the brick
  `V_0 = U_0 ∩ {c = 1}`. It moves every point of `V_0` and nothing else.

Put `a = σF ∈ nV`.

**Lemma 3.** For `i >= 0`, `a^i(V_0) = f_+^i(U_0) × {c=1}` and `a^(-i)(V_0) = f_-^i(U_0) × {c=0}`.

*Proof.* `σ` is trivial on `f_±^i(U_0)` for `i >= 1`, by the no-return property. So by induction
`a^i(V_0) = F(f_+^(i-1)(U_0) × {1}) = f_+^i(U_0) × {1}`. For the other direction,
`a^(-1) = F^(-1)σ`, and `σ(V_0) = U_0 × {0}`. `F^(-1)` acts as `f_-` on copy 0, so
`a^(-i)(V_0) = f_-^i(U_0) × {0}` by the same induction. ∎

Put `V_i = a^i(V_0)`. They are pairwise disjoint: a coincidence would give `a^k(V_0) ∩ V_0 ≠ ∅`
for some `k ≠ 0`, which Lemma 3 and no-return exclude.

**Lemma 4.** `g` is the identity on `V_i` iff `i ∉ C·S_+ ∪ (−C·S_-)`. Otherwise `g(V_i)` contains
points with `z = 1`, while every `V_j` lies in `{z = 0}`.

*Proof.* By Lemma 3 and the emission property of §2. ∎

## 4. The centralizer

Let `L' = ⟨a^C, ε⟩` and `u'_k = a^(Ck) ε a^(-Ck)`. Then `u'_k` is an involution supported exactly
on `V_(Ck)`.
- The supports are disjoint, so the `u'_k` commute and are independent, and `a^C` shifts them.
- `a^(Cp)` with `p ≠ 0` moves `V_0` off itself, while lamp products fix it.
- So `L' ≅ Z/2 ≀ Z`, with `u'_k ↔ u_k`.

By Lemma 4, `g` is the identity on `V_(Ck)` iff `k ∈ A = Z ∖ (S_+ ∪ −S_-)`.

**Lamp products.** Let `h = ∏_(k∈F) u'_k` for a finite `F`.
- If `F ⊆ A`, then `g` is the identity on `supp h = ⋃_F V_(Ck)`, so `[g, h] = 1`.
- If some `k ∈ F ∖ A`, then `supp(g h g^(-1)) = g(supp h)` contains points with `z = 1`, while
  `supp h` does not. So `[g, h] ≠ 1`.

**Shifted elements.** Suppose `h = a^(Cp) ∏_F u'_k` with `p ≠ 0` commutes with `g`. Conjugating
`u'_i` by `h` gives `u'_(i+p)`. So `g u'_(i+p) g^(-1) = h (g u'_i g^(-1)) h^(-1)`. By the lamp case
`g` commutes with `u'_i` iff `i ∈ A`, so this equation gives `A + p ⊆ A`. The same argument
applied to `h^(-1)` gives `A - p ⊆ A`. So `A` would be periodic, which is excluded.

Hence `C_(L')(g) = U_A`. ∎

## 5. Consequences

- **Condition (e).** `nV ∈ B_A`, so condition (e) of `pbh-coset-wreaths-iff-identity-edge-hnns`
  holds with `G = L'`, `C = U_A`, `M = nV` and `m = g`. The equivalent forms (a)–(d) give the
  lists in the target.
- **Dyson groups.** `L(A) = L *_(U_A) L` is the kernel of
  `L *_(U_A) (U_A × Z/2) → Z/2`, so it lies in `B_A` as a subgroup.
- **Size of `n`.** `n` is the number of stacks, which depends on the verifiers.

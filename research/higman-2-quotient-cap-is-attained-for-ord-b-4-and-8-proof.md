---
rg: 2
id: higman-2-quotient-cap-is-attained-for-ord-b-4-and-8-proof
kind: route
title: The ANU p-quotient program computes the lower exponent-2 central quotients of G/<<b^4>>, G/<<b^8>> and the family X_k and collects powers of a; a linear-algebra reduction on an abelian layer turns the class-14 quotient of X_2 into a small certified pc model
target: higman-2-quotient-cap-is-attained-for-ord-b-4-and-8
requires:
  - higman-2-quotient-order-cap-is-attained-for-small-ord-b
artifacts:
  - experiments/higman-k2-cap-2026-09-19/run2.sh
  - experiments/higman-k2-cap-2026-09-19/red2.g
  - experiments/higman-k2-cap-2026-09-19/zsq.g
  - experiments/higman-k2-cap-2026-09-19/check-model.g
  - experiments/higman-k2-cap-2026-09-19/probes.txt
  - experiments/higman-k2-cap-2026-09-19/collect.txt
  - experiments/higman-k2-cap-2026-09-19/logs.txt
  - experiments/higman-k2-cap-2026-09-19/mono4.g
  - experiments/higman-k2-cap-2026-09-19/k2-pc.g
---

Notation is as in the target. All scripts are in `experiments/higman-k2-cap-2026-09-19/`. `logs.txt`
holds the relevant lines of every run, and `probes.txt` and `collect.txt` summarise them.

## 1. The cap

The cap `ord(a) | 2^(k+6)`, `ord(c) | 2^(k+2)` and `ord(d) | 2^(k+4)` in the 2-quotients of `Gamma_k` is
item 1 of `higman-2-quotient-order-cap-is-attained-for-small-ord-b`. So `ord(a) = 2^(k+6)` as soon as
`a^(2^(k+5)) != 1` in some 2-quotient of `Gamma_k`. All the quotients below are quotients of some
`Gamma_k`.

## 2. The p-quotient computation (items 2 to 5)

`run2.sh NAME CL EXTRA WORDS` feeds the standalone ANU p-quotient program (`pq`, the `anupq`
package's binary, run with `-s 450000000`). The input is the presentation
`{a,b,c,d | b^a b^-3, c^b c^-3, d^c d^-3, a^d a^-3, [a,c]^2 EXTRA}`.

- It computes `P_cl` class by class, in chunks of at most 20 minutes, saving the presentation after
  each class and restoring it for the next chunk.
- After each class it collects each word of `WORDS` in the pcp generators `x1..x4` (the images of
  `a,b,c,d`, pq's advanced option 23). It logs `IDENTITY` or `NONTRIVIAL`.
- pq checks consistency of each new class itself, so each `P_cl` is a consistent power-commutator
  presentation of the largest class-`cl` lower exponent-2 central quotient.
- pq's commutators are left-normed, as in the target.

Since `P_cl(X)` is a finite 2-quotient of `X`, one `NONTRIVIAL` for `x1^(2^(k+5))` proves
`ord(a) = 2^(k+6)` in a finite 2-quotient of `Gamma_k`. An `IDENTITY` only shows `ord(a)` in `P_cl`,
not in all 2-quotients. So items 3 (the `[b,d]^(2^k)` half), 4 and 5 are statements about the classes
computed.

The runs are the following (the full table is in `probes.txt`):
- `Z3` (`EXTRA = b^8`, class 16): order `2^16535`, `x1^256` nontrivial and `x1^512 = 1`, giving item 2.
- `G2` (`EXTRA` empty, class 15): order `2^11776`, `x1^256 = 1`.
- `L1`, `R3`, `K5` are `X_1`, `X_2`, `X_3` at classes 12, 14, 16. `R3` also contains the redundant
  `[a,c^2]^16`.
- `L2`, `L3`, `K4` are the `[b,d]^(2^k)` variants.
- `K7` is `X_4` (`EXTRA = b^16, [b,d,d], [b,d]^32, [a,c^2]^8`) at classes up to 18 (order `2^10125`):
  `x1^256` is nontrivial from class 16 on, and `x1^512 = 1` at every class computed.
- `S1`, `X`, `T1` are `G''`, `G''/<<b^4>>` and `G''/<<b^2>>`.
- Each killer in item 5 is a separate run at class 14.

## 3. A small model for k = 2 (item 1)

`R3.gap` is the class-14 quotient `P = P_14(X_2)` (order `2^1221`), written by pq's option 25 as a GAP
pc group with the images of `a,b,c,d`. GAP reads it back and checks the five defining relators of `G`
and `b^4` on these images, with orders `(256,4,16,64)`. Commutators here are left-normed.

`red2.g` makes it smaller.

**Lemma.** Let `P` be a finite 2-group and `A` an abelian normal subgroup. Let `V = A/A^2` and
`z in A \ A^2`. Take a linear form `f` on `V` with `f(z) = 1`, and let `W` be the span of the
`P`-translates of `f`. Then `N = {v in A : w(v) = 0 for all w in W}` is a normal subgroup of `P`, lies
in `A` and contains `A^2`, does not contain `z`, and `|A/N| = 2^(dim W)`.

*Proof.* `N` is a subgroup of `A` containing `A^2`, since each `w` is a homomorphism `A -> F_2` that
kills `A^2`. For `g in P` and `v in N`, `w(v^g) = (g.w)(v) = 0` because `W` is `P`-invariant, so
`N` is normal. `f(z) = 1` with `f in W`, so `z` is not in `N`. Finally `A/N` is dual to `W`. ∎

**What red2.g does.** pq orders the pc generators by weight, so `gamma_I(P)` is spanned by generators
`S+1..n`, where `2^S = |P_(I-1)|`. Take `I = 13`, so `S = 476`. Then `A = gamma_13(P)` has dimension
745; it is abelian since `2·13 > 14`, and the script checks this. `zsq.g` shows that
`z = a^128` lies in `gamma_I^2` for `I = 8..12` but not for `I = 13`.

- It writes the conjugation action of all 476 top generators on `V` as matrices over `F_2`. `V` is
  read off exponent vectors, which is valid because every carry in `A` is a square.
- It takes six forms `f` with `f(z) = 1` and computes `W` for each (`dim W` = 4 or 5, spanned under
  `a,b,c,d`, which generate `P`).
- It keeps a smallest `W` and writes `Q = P/N` as a new power-conjugate presentation on the 476 top
  generators and a basis of `A/N`, with GAP's `SingleCollector`. The relations are read off the
  genuine quotient `P/N`, so they hold in a group of order `|P/N|`. Consistency is checked
  independently on the final model (below).
- It checks the relators and orders again in `Q` and saves `Q` as `k2-big-pc.g`. Then `mono4.g`
  repeatedly factors out a complement of `<z>` in `Omega_1(Z(Q))` until the socle is `<z>`, saving
  `k2-pc.g` after each step.

**Result.** The reduction takes `2^1221` to `2^480` (`dim W = 4`). The monolithic loop then goes
`2^480 -> 2^318 -> 2^217 -> 2^170 -> 2^150 -> 2^147 -> 2^146`, with socle ranks `163, 102, 48, 21, 4, 2`
and finally 1. The orders stay `(256,4,16,64)` at every step (`k2m4.out` lines in `logs.txt`).

`check-model.g` reads `k2-pc.g` from scratch and prints:
- `|MQ| = 2^146`, a 2-group, with the five relators holding on the images of `a,b,c,d`;
- the images generate `MQ`, with orders `[256, 4, 16, 64]` and socle rank 1;
- `presentation consistent: true`, from GAP's `IsConfluent` on the saved collector.

So `k2-pc.g` is a finite 2-group quotient of `Gamma_2`, with `ord(b) = 4` and `ord(a) = 256`. It
certifies item 1 without trusting pq or `red2.g`.

## 4. What is not proved

- The `IDENTITY` results are class-bounded. For example, `a^128 = 1` in `P_18(G''/<<b^4>>)` does not
  give `a^128 = 1` in all 2-quotients of `G''/<<b^4>>`.
- Whether `X_k` attains the cap for all `k` is open. It holds for `k = 1, 2, 3` at class `2k+10`,
  and fails for `k = 4` at class 18 (the classes computed).

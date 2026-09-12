---
rg: 2
id: p-adic-analytic-torsion-free-groups-satisfy-strong-atiyah
kind: claim
title: Subgroups of torsion-free compact p-adic analytic groups satisfy Strong Atiyah, and their group rings are domains in characteristic 0 and p
distinct_from:
  elementary-amenable-torsion-free-strong-atiyah: that is Linnell's amenable class; this is the p-adic analytic class of Farkas--Linnell, which contains infinite property (T) groups such as Gamma(3) in SL_3(Z).
  raag-out-and-mapping-class-virtually-strong-atiyah: that is Fisher--Ng's theorem for finite-index subgroups of Out(A_Gamma) and mapping class groups, proved by approximating with p-adic analytic quotients; this is the p-adic analytic input itself.
  strong-atiyah-torsion-free: that is the open conjecture for every torsion-free group; this is an established class.
  kaplansky-zero-divisor-conjecture: that is the zero-divisor conjecture over every field; this proves it only for these groups and only in characteristic 0 and in the characteristic p of the analytic structure.
artifacts:
  - research/artifacts/strong-atiyah-kazhdan-groups-2026-09-12.md
---

**ESTABLISHED (literature import).** Let `p` be a prime and let `W` be a
torsion-free compact `p`-adic analytic group. Let `H` be any abstract subgroup
of `W`. Then:

1. `H` satisfies the Strong Atiyah Conjecture over `C`: for every finite matrix
   `A` over `C[H]`, `rk_{N(H)}(A)` is an integer;
2. if `W` contains a normal subgroup of finite index isomorphic to
   `CS(u,d,p) = {A in Mat_d(Z_p) : A = I_d mod p^u}` (with `u >= 2` if `p = 2`),
   then `k[H]` is a domain for every field `k` of characteristic `0` or `p`.

**Instances.**
- `Gamma(p)` in `SL_d(Z)` for odd `p`, and `Gamma(4)`, together with all their
  subgroups, since `Gamma(p) <= CS(1,d,p)` and `Gamma(4) <= CS(2,d,2)`;
- every torsion-free open subgroup `W` of `SL_d(Z_p)`, for both parts. Let
  `Z = 1 + p^u Z_p` act as central scalars, with `u` so large that `Z` has no
  nontrivial `d`-th roots of unity. Then `W Z = W x Z` is torsion-free. For `v`
  large, every `A` in `CS(v,d,p)` has `det A = lambda^d` with `lambda` in `Z`, and
  `lambda^(-1) A` lies in `SL_d(Z_p)` and is congruent to `I` modulo a power of
  `p` so high that it lies in `W`. So `CS(v,d,p) <= W x Z` is normal of finite
  index, and Theorems 1.1--1.3 apply to `W x Z`.

**Source, read from the arXiv sources on MSI (2026-09-12).**
- Farkas--Linnell, *Congruence subgroups and the Atiyah conjecture*,
  arXiv:math/0511747 (Contemp. Math. 420, 2006). Theorem 1.1, verbatim:
  "let `G` be a torsion-free group which contains a normal subgroup of finite
  index isomorphic to `CS(u,d,p)`. Then there is a division ring `D(G)` such
  that `Qbar[G] <= D(G) <= U(G)`." Theorems 1.2 and 1.3: for
  `Gamma = CS(u,d,p)`, `k[Gamma]` is a domain over every field of
  characteristic `p`, and then over every field of characteristic `0`.
- Fisher--Ng, arXiv:2606.19606, Section 2: "Farkas--Linnell [Theorem 1.1] show
  that torsion-free compact `p`-adic analytic groups satisfy the Strong Atiyah
  Conjecture over `Qbar`", and with Jaikin-Zapirain's base change for sofic
  groups, Theorem `thm:p-adic-atiyah`: "If `G` is a torsion-free compact
  `p`-adic analytic group, then `G` satisfies the Strong Atiyah Conjecture over
  `C`." Also verbatim: passage to subgroups holds "for subgroups of torsion-free
  groups".

By Linnell's theorem a division ring between `Qbar[G]` and `U(G)` gives Strong
Atiyah over `Qbar`. Subgroups inherit both Strong Atiyah and being a domain.

*Review note, 2026-09-12 (`swarm5-reviewer`, from the arXiv PDFs):* Theorems 1.2
and 1.3 of Farkas--Linnell are stated only for `Gamma = CS(u,d,p)` itself. For a
`W` that properly contains `CS(u,d,p)` with finite index, part 2 needs two more
inputs:
- **Characteristic `p`:** Farkas--Linnell Theorem 6.1, that `k[[W]]` is a
  noetherian domain, together with the inclusion `k[H] <= k[[W]]`. Fisher--Ng
  restate it as Theorem 2.10.
- **Characteristic `0`:** part 1, since Strong Atiyah over `C` gives no zero
  divisors (Fisher--Ng, Section 2).

The conclusion stands. See `research/artifacts/review-swarm5-2026-09-12.md`.

Trust surface: Farkas--Linnell was read at theorem-statement level from source,
not line by line; the base change to `C` is Jaikin-Zapirain as quoted by
Fisher--Ng.

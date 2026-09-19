---
rg: 2
id: fpbs-letter-contact-words-have-relative-cayley-cost-one
kind: claim
title: If a letter subgroup <s,v> meets its conjugate by the other letter, the v-lines plus Cayley edges of cost 1+eps generate every free F_2-action, so F_n amalgamated with F_2 over a contact word attains 1+beta_1 inside the Cayley graphing on every free action
artifacts:
  - research/artifacts/fpbs-relative-cayley-cost-letter-saturation-2026-09-18.md
  - experiments/fpbs-relative-cayley-cost-2026-09-17/census.py
  - experiments/fpbs-relative-cayley-cost-2026-09-17/census_usage.py
  - experiments/fpbs-relative-cayley-cost-2026-09-17/probe.py
  - experiments/fpbs-relative-cayley-cost-2026-09-17/stallings.py
  - experiments/fpbs-relative-cayley-cost-2026-09-17/witnesses.py
distinct_from:
  fpbs-infinite-contact-zero-relative-cost: that proves zero relative cost when subrelation classes are connected by infinitely many edges of an arbitrary graphing, by marked sprinkling; this takes the repair edges inside one Cayley letter, as an explicit eps-small set, and applies it to Cayley subgraphing cost of amalgams
  fpbs-wq-normal-subgroup-cost-transfer: that transfers cost across wq-normal inclusions with unrestricted repair graphings; this is the one-step contact move with repairs restricted to the letter Phi_t, which is what C_sub(S) needs
  fpbs-one-relator-twice-used-letter-fixed-price: that reaches C_sub(S) = 1 + beta_1 for one-relator groups with a letter used exactly twice via dual-forest Morse matchings; this reaches it for F_n *_{u=v} F_2 with v a contact word, including relators such as abaBab.DDDCCC in which every letter is used three times
  fpbs-morse-deficit-vanishes-for-full-presentations: that is the open vanishing claim for all groups; this proves its C_sub form for one class of amalgams and does not cover the sharp test abaBab = cdcDcd
  fpbs-letter-saturated-morse-matchings-die-on-bernoulli: that caps per-letter shares of fixed-list Morse matchings; this bypasses Morse matchings and bounds C_sub(S) directly
---

**ESTABLISHED (written deduction).** Proof in `fpbs-letter-contact-words-have-relative-cayley-cost-one-proof`.

**Setting.**
- `a` is a free p.m.p. action of `F(c,d)`.
- For a word `v`, the `v`-line graphing is `S_v = {(x, v x)}`.
- The relative Cayley cost is `RC_a(v) = inf mu(F)`, over Borel `F subset Phi_c cup Phi_d` with `<F cup S_v> = E_a`.
- `{s, t} = {c, d}` and `H_s = <s, v>`.

**Lemma 1 (contact repair).** Let a countable group act freely and p.m.p. Let `H` be a subgroup and `t` an element,
with `H cap t^{-1} H t` infinite. Then for every `eps > 0`, the relation `R_H` together with the `t`-edges out of some
set of measure `< eps` generates `R_{<H,t>}`.

**Theorem A.** If `H_s cap t^{-1} H_s t != 1` for some choice of `s`, then `RC_a(v) = 1` for every free action `a`.

**Corollary A'.** Let `u in F_n \ {1}`, with `n >= 1`, let `v` satisfy Theorem A, and put

```text
G = F_n *_{u=v} F(c,d) = <a_1..a_n, c, d | u v^{-1}>,     S = {a_1..a_n, c, d}.
```

Then for every free p.m.p. action `a` of `G`,

```text
C_sub^a(S) = C(a) = n + 1 = 1 + beta_1^(2)(G).
```

So the hole at `S` holds for these groups, and so do both halves (P1) and (P2) of
`fpbs-hole-at-s-is-s-price-plus-invariant-cayley-cost`. By Theorem B of `fpbs-bernoulli-morse-collapse-criterion`,
the Morse deficit over `P_L` then tends to `0`. That theorem is PROPOSED ESTABLISHED, so this last step is conditional
on it.

**Scope.**
- Fixed price `n + 1` for these amalgams is classical, from Gaboriau's amalgam formula over an amenable subgroup. The
  new content is attainment inside the Cayley graphing `Phi_S`, on every free action.
- Examples in which every letter is used at least 3 times: `u = abaBab`, and `v` in {`cccddd`, `cdcdcD`, `ccdcdcd`,
  `cdcdcDD`, `cddcddcD`}. The census of Section 7 of the artifact finds 55 such contact classes of length at most 9.
  Explicit contact elements, found by `witnesses.py` and checkable by hand:
  - `ddd` lies in `<c, cccddd> cap d^{-1} <c, cccddd> d`;
  - `(dc)^3 = d (cdcdcD) d` lies in `<d, cdcdcD>`, and so does `c (dc)^3 c^{-1} = (cd)^3 = (cdcdcD) d`.
- It does **not** cover `v = cdcDcd`, which has no contact. See
  `fpbs-saturated-cayley-repair-couples-to-ascending-union`.

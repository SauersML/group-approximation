---
rg: 2
id: euler-base-annihilator-over-lamplighter-is-not-fg
kind: claim
title: The Euler base Z_(l)[y^±1] is not finitely presented over Z[Z≀Z], nor is its induced module over Z[Q] for any group Q ⊇ Z≀Z, though over the ring D it needs one left and one two-sided relation
distinct_from:
  z-localized-embeds-in-fg-rf-soluble-group: that constructs the finitely generated residually finite Euler lamplighter G_l = M ⋊ (Z≀Z); this shows its base M is not finitely presented as a module over the lamplighter, or over any overgroup of it, which blocks the freest finitely presented extension of G_l.
  kms-configuration-letters-inherit-exponent-p: that calibrates the characteristic-0 KMS variant; this tests the ingredient that calibration isolated, imposing the Euler relation by finitely many module relations, and finds it fails over any top.
  resolvent-ring-has-path-normal-form: that is the ring R_l, whose shift part is the same skew Laurent ring D; this concerns the D-module D/Du inside a group.
artifacts:
  - research/artifacts/gq-referee-a-euler-base-annihilator-over-lamplighter-is-not-fg.md
  - research/artifacts/gq-referee-b-euler-base-annihilator-over-lamplighter-is-not-fg.md
---

**ESTABLISHED** through `euler-base-annihilator-over-lamplighter-is-not-fg-proof`. Lane proof, with
proof-gap review PASS by gq-referee-a and citation review PASS by gq-referee-b (reports in
`artifacts`). It uses no unread citation.

**Setting** (`z-localized-embeds-in-fg-rf-soluble-group`).
- `M = Z_(l)[y^(±1)]` with basis `f_j = y^j`.
- `H = <x, β> ≅ Z≀Z`, with `x f_j = f_(j-1)` and `β f_j = (1+lj) f_j`.
- The lamps are `β_k = x^(-k) β x^k`, so `β_k f_j = (1 + l(j-k)) f_j`, and `B = <β_k : k in Z>` is free
  abelian on them.
- Write `ε : Z[B] -> Z_(l)` for the ring map `β_k -> 1 - lk`.

**Statement.**
1. **Presentation over D.** Put `r = x β x^(-1) - β - l in Z[H]`, the Euler element, and `D = Z[H]/(r)`,
   the quotient by the two-sided ideal. Then `M ≅ D / D(β - 1)` as `D`-modules. The one left relation
   `β - 1` and the one two-sided relation `r` suffice. This `D` is the skew Laurent ring
   `A[x^(±1); σ]` of `resolvent-ring-has-path-normal-form`, with `u = β - 1`.
2. **No finite presentation over the lamplighter.** The annihilator of `f_0` in `Z[H]` is
   `J = ⊕_m x^m ker ε`, and it is not finitely generated as a left ideal. So `M = Z[H]/J` is not a
   finitely presented `Z[H]`-module. In particular, for every finite set `F ⊂ Z`, the shifted Euler
   relations `r x^k f_0 = 0` (`k in F`) together with `(β-1) f_0 = 0` do not imply the others.
3. **No finite presentation over any overgroup.** For every group `Q ⊇ H`, the induced module
   `Z[Q] ⊗_(Z[H]) M` is not finitely presented over `Z[Q]`. An instance is Baumslag's finitely presented
   group `<a, s, t | [s,t], [a, a^t], a^s = a a^t>`. Both "`<a, t> ≅ Z≀Z`" and "metabelian" were checked
   directly by gq-referee-a and gq-referee-b; Baumslag, Proc. AMS 35 (1972), 61–62, was not read at source.

**Reading for the characteristic-0 program** (ingredient 2 of `gq-gq-infinite-primes-kms-reading.md` §3).
- *BR form.* Use the KMS convention `f^g = g^(-1) f g`. In `G_l = M ⋊ H` this is `f^g = g^(-1)·f`. Then
  the Euler relation at the generator reads `f^(β_(-1)^(-1)) = f^(β^(-1)) f^l`, where
  `β_(-1) = x β x^(-1)` acts as `β + l`. So `v^(f(a)) = v^(a')` holds for `v = f_0`, with `a = β_(-1)^(-1)`,
  `a' = β^(-1)` and the monic polynomial `f(t) = t - l`. That is a Baumslag–Remeslennikov conjoint
  relation in the form of KMS Lemma 4.1, and the lamps commute, as that lemma requires. (Corrected after
  gq-referee-b: with the left-action convention the pair would be `(β_(-1), β)`.)
- *Where it propagates.* The BR mechanism carries such a relation along conjugation by elements
  commuting with the conjoint pair. Here that is the lamp group `B`, not `x`.
- *What is needed.* Item 2 shows that the missing instances `r x^k f_0 = 0` are genuinely infinitely many.
  Item 3 shows no top repairs this in the freest way.
- *The split host is excluded.* By gq-referee-a's strengthening R1, `(Z[Q] ⊗ M) ⋊ Q` is not finitely
  presented for any `Q ⊇ H`. The argument: `Q` is a retract, and Crowell's sequence makes an abelian
  base of a finitely presented split extension a finitely presented module. The proof is in its report
  and is not re-derived here.
- *What is not excluded.* In a split host `N ⋊ Q` with abelian base, the `Z[Q]`-span of `M` is a
  quotient of the induced module, and `N` must be finitely presented. So either the span is a proper
  quotient, or `N` is strictly larger than the span. Non-split hosts and non-metabelian hosts are not
  addressed. One such host is the Steinberg group of `euler-base-embeds-in-fp-steinberg-group`.
- *Scope.* Deliverable (a), an explicit finite presentation, is not achieved. This node is a partial
  (b): an obstruction for the freest extension, not for all.

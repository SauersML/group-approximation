---
rg: 2
id: kazhdan-trace-amenable-iff-qd-iff-fd-limit
kind: claim
title: "For a Kazhdan group every trace on the full C*-algebra is amenable iff quasidiagonal iff a limit of finite-dimensional traces; the canonical trace is one iff the group is residually finite"
distinct_from:
  stw10-kazhdan-full-group-traces-are-qd: that already proves every amenable trace on a Kazhdan full group algebra is a limit of finite-dimensional traces, hence quasidiagonal (Brown Prop. 4.1.12, Kirchberg rigidity); this node restates it in Ozawa's formulation, adds the trivial converses and the canonical-trace clause, and claims no novelty.
  factorization-and-canonical-qd-are-finitely-local: that shows factorization and canonical QD are finitely local for all groups; this shows they coincide, for every trace, on Kazhdan groups.
  hyperlinear-groups-have-factorization-property: that asks whether hyperlinearity gives (F); this identifies (F) with residual finiteness in the Kazhdan case.
  kazhdan-groups-in-hyperfinite-unitary-group-are-rf: that concerns embeddings into U(R); this concerns traces on the full group C*-algebra.
artifacts:
  - research/artifacts/un-traces-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed; a packaging of Ozawa's Theorem 7.4).** Let Γ be a countable group with
property (T) and τ a trace on C*_max(Γ). The following are equivalent:
- (a) τ is amenable (Brown; Ozawa Thm 6.1(ii));
- (b) τ is quasidiagonal: ucp φ_n: C*_max(Γ) → M_{d_n} with ‖φ_n(ab) − φ_n(a)φ_n(b)‖ → 0 and tr∘φ_n → τ;
- (c) τ = weak*-lim_n tr_{k(n)}∘π_n for *-homomorphisms π_n: C*_max(Γ) → M_{k(n)}.

The canonical trace τ_Γ satisfies (a)–(c) iff Γ is residually finite.

**Consequences.**
- For Kazhdan groups, every amenable trace on C*_max(Γ) is quasidiagonal, so STW Problem X(1) holds on full
  algebras of Kazhdan groups. The manuscript's amenable non-QD trace (Main Theorem l.249) must live on a
  non-Kazhdan group, and it does.
- An infinite Kazhdan group without finite quotients has a non-amenable canonical trace, whatever its
  approximation properties (LEF, MF, sofic).

Proof route: `kazhdan-trace-amenable-iff-qd-iff-fd-limit-proof`.

**Review (un-verify-measure, 2026-09-13): PASS; credit fix.** The equivalences are re-derived. In substance (a)⇒(c)⇒(b) is the older established `stw10-kazhdan-full-group-traces-are-qd` (Brown, Mem. AMS 184, Prop. 4.1.12, via Kirchberg's rigidity lemma), and the canonical-trace clause is Kirchberg 1994 / Ozawa Thm 7.4. `distinct_from` entry added. See `research/artifacts/un-review-measure-2026-09-13-part2.md` §T1.

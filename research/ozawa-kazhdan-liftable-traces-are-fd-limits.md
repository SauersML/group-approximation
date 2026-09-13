---
rg: 2
id: ozawa-kazhdan-liftable-traces-are-fd-limits
kind: claim
title: "Ozawa: on the full C*-algebra of a Kazhdan group a trace is liftable iff it is a limit of traces of finite-dimensional representations"
distinct_from:
  kazhdan-groups-in-hyperfinite-unitary-group-are-rf: that is Kirchberg–Valette for Kazhdan subgroups of U(R); this imports the trace-level theorem for arbitrary traces on C*Γ and its factorization-property corollary.
artifacts:
  - research/artifacts/un-traces-2026-09-13-part1.md
---

**ESTABLISHED (import).** N. Ozawa, *About the QWEP conjecture*, Internat. J. Math. 15 (2004) 501–530,
arXiv:math/0306067v2. Read from the arXiv PDF page images on 2026-09-13.

- **Theorem 7.4** (p. 26): "Let τ be a trace on the full C*-algebra C*Γ of a group Γ with Kazhdan's
  property (T). Then, τ is liftable if and only if there is a sequence of *-homomorphisms π_n: C*Γ → M_{k(n)}
  such that τ(a) = lim_n tr_{k(n)} π_n(a). In particular, a group Γ with the properties (F) and (T) is
  residually finite."
- **Definition 7.2** (p. 24): "We say a group Γ has the property (F) (the factorization property) if the
  trace τ on the full C*-algebra C*Γ, defined by τ(s) = δ_{1,s} for s ∈ Γ, is liftable."
- **Theorem 6.1** (p. 21, Kirchberg): for a trace τ on A ⊆ B(H) the following are equivalent. (i) τ extends
  to an A-central state on B(H). (ii) "There is a net of ucp maps θ_i: A → M_{n(i)} such that
  τ(a) = lim_i tr_{n(i)}(θ_i(a)) and lim_i tr_{n(i)}(θ_i(ab*) − θ_i(a)θ_i(b)*) = 0 for every a, b in A."
  (ii') τ is liftable. (iii) μ_τ is min-continuous on A⊗Ā. (iv) σ_τ is min-continuous on A⊗Ā.
- p. 26: "infinite simple groups with Kazhdan's property (T) … do not have the property (F) as it was shown
  by Kirchberg [Ki3]" (E. Kirchberg, Math. Ann. 299 (1994) 551–563). Section 7 assumes groups countable
  and discrete.

Condition (ii) is Brown's amenable trace, so amenable = liftable.

**Review (un-verify-measure, 2026-09-13): PASS.** Theorem 6.1, Definition 7.2, Theorem 7.4 and the p. 26 Kirchberg remark checked verbatim against the arXiv PDF (pdftotext). See `research/artifacts/un-review-measure-2026-09-13-part2.md` §T0.

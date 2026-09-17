---
rg: 2
id: thompson-f-amenable-via-exotic-co-amenable-subgroup
kind: route
title: Find a co-amenable subgroup of F that is neither elementary amenable nor contains F, and prove that F-free subgroups of F are amenable
target: thompson-f-is-amenable
requires:
  - f-has-a-co-amenable-subgroup-neither-ea-nor-containing-f
  - every-f-free-subgroup-of-thompson-f-is-amenable
  - thompson-f-interval-stabilizer-cosets-separate-only-if-amenable
---

**Contrast.** `thompson-f-amenable-via-dyadic-extensive-amenability` has a single prerequisite, and it is
equivalent to the target (item 3 of the sandwich claim, trivial kernel). Here each prerequisite is weaker than
the target on its own, and neither is known to imply it.

**Route.** Let `K` be the subgroup given by `f-has-a-co-amenable-subgroup-neither-ea-nor-containing-f`.
- `K` contains no copy of `F`, so by `every-f-free-subgroup-of-thompson-f-is-amenable` it is amenable.
- `F/K` carries an invariant mean.
- By item 3 of `thompson-f-interval-stabilizer-cosets-separate-only-if-amenable`, `F` is amenable.

**Why this is the decomposition.** By `f-sandwich-splits-collapse-unless-kernel-is-brin-sapir-exotic`, every
co-amenable-induction split collapses to a reformulation unless its subgroup is Brin–Sapir exotic. Twisted
embeddings collapse the same way. This route is the one uncollapsed split.

**The prerequisites fail independently.**

| | P1 = `f-has-a-co-amenable-subgroup-neither-ea-nor-containing-f` | P2 = `every-f-free-subgroup-of-thompson-f-is-amenable` |
|---|---|---|
| Implied by | `A` together with the failure of Brin–Sapir | `A`; also the Brin–Sapir conjecture, since EA groups are amenable |
| Fails if | the Brin–Sapir conjecture holds; or some other constraint rules out F-free co-amenable subgroups, e.g. a proof that `F` is not sofic | some F-free subgroup of `F` is non-amenable, which would prove `thompson-f-is-not-amenable` |
| Believed | contrary to the Brin–Sapir conjecture | consistent with the Brin–Sapir conjecture |

Neither is known to imply `A`:
- P2 holds whenever Brin–Sapir holds, and Brin–Sapir does not decide `A`, since `F` contains `F`.
- P1 alone gives a co-amenable subgroup whose amenability is open.

**Named consequences of P1.** Item 5 of the sandwich claim:
- P1 proves `thompson-f-is-sofic`;
- P1 refutes the Brin–Sapir conjecture;
- the coset mean of any P1 witness is mean-free, and the witness is unconfined.

So P1 is at least as hard as refuting Brin–Sapir and proving soficity of `F` simultaneously.

**Literature links.**
- *Juschenko–Monod / JMBMdlS (arXiv:1503.04977).* The (T1) form of the same split, with `P = EA(X)`, has the
  same kernel trichotomy (sandwich claim, items 1–4).
- *Moore's Følner function bounds.* `thompson-f-folner-function-exceeds-every-tower` bounds Følner sets of `F`.
  It says nothing about Følner sets of the Schreier graph `F/K` in P1, nor about the F-free groups in P2.
  Both prerequisites therefore escape the tower barrier as stated.
- *Kaimanovich (arXiv:1602.02971) and `thompson-f-finite-breakpoint-moment-walks-are-not-liouville`.* These
  constrain Liouville measures on `F` itself, so they bear on `A` and not on P1 or P2.

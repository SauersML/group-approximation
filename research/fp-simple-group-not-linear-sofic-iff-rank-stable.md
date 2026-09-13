---
rg: 2
id: fp-simple-group-not-linear-sofic-iff-rank-stable
kind: claim
title: A finitely presented infinite simple group is not linear sofic over a field iff it is rank-stable over that field
distinct_from:
  fp-simple-weak-soficity-is-finite-field-linear-soficity: that identifies weak soficity with linear soficity over finite fields for these groups; this identifies the failure of linear soficity with flexible rank-stability, over one field or uniformly over all finite fields.
  non-weakly-sofic-iff-non-finite-field-linear-sofic-group: that is the existence-level equivalence between the two roots; this is a per-group equivalence between non-approximability and stability.
  amenable-group-algebra-rank-stability-iff-rf: that ties stability to residual finiteness for amenable domains; this ties stability to non-approximability for simple groups, where every exact representation is trivial.
artifacts:
  - research/artifacts/solve-weakly-sofic-2026-09-13.md
---

**ESTABLISHED (2026-09-13, lane `solve-weakly-sofic`, unreviewed)** by
`fp-simple-not-linear-sofic-iff-rank-stable-proof`.

Let `G = <x_1,...,x_d | P_1,...,P_r>` be an infinite finitely presented simple group.

1. **One field.** For every field `F` these are equivalent:
   - (a) `G` is not `F`-linear sofic, i.e. it embeds in no rank ultraproduct `prod_omega GL_(n_k)(F) / d_omega`;
   - (b) `G` is rank-stable over `F`;
   - (c) `F[G]` is rank-stable.
2. **Finite fields, uniformly.** These are equivalent:
   - (a') `G` is not linear sofic over finite fields, i.e. it embeds in no `prod_omega GL_(n_k)(F_(q_k)) / d_omega`
     (definition as on `simple-group-psl-width-is-finite-field-linear-soficity`);
   - (b') `G` is uniformly rank-stable over finite fields: for every `eps > 0` one `delta > 0` works in the stability
     condition for every finite field at once;
   - (c') `G` is not weakly sofic.

Rank-stability is the flexible notion recorded on `fp-group-rank-stability-equals-group-algebra-rank-stability`.

**In words.** Every exact solution of the relators of `G` in `GL_(n')(F)` is the identity, so stability says that
every approximate solution is near the identity. For a simple group that is exactly the absence of a nontrivial, hence
injective, rank-ultraproduct model.

**Consequences.**
- By item 2, one infinite finitely presented simple group that is uniformly rank-stable over finite fields confirms
  Glebsky--Rivera Conjecture 4.5 (`fp-simple-group-uniformly-rank-stable-over-finite-fields-exists`).
- By item 1(c), deciding linear soficity of `R^x` or Thompson's `V` over `F_2` is the same as deciding flexible
  rank-stability of the finitely presented algebras `F_2[R^x]` and `F_2[V]`. So the algebra tools of
  Bauer--Blachar--Greenfeld apply there, e.g. `fp-simple-group-algebra-amenable-quotient-gives-linear-soficity`.

**Credit.** Elementary; the algebra-level analogue for residually finite-dimensional algebras is Bauer--Blachar--Greenfeld
Proposition 2.2 (`research/artifacts/solve-weakly-sofic-2026-09-13.md`, Section 1). No novelty is claimed.

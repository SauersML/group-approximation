# Referee report (gq-referee-c): sl-odd-q-in-fp-simple-iff-fp-overgroup-maps-nontrivially

- **Node:** `research/sl-odd-q-in-fp-simple-iff-fp-overgroup-maps-nontrivially.md` and its `-proof` route, landed
  a6c28b163 by lane `gq-reform-countable`.
- **Lens:** independent re-derivation and calibration.
- **Verdict: PASS**, with one structural suggestion.

## Re-derivation

- **Input 1: SL_m(Q) is simple for odd m.** The centre of `SL_m(Q)` is `{λI : λ^m = 1, λ ∈ Q} = {I}` for odd `m`,
  so `SL_m(Q) = PSL_m(Q)`. That group is simple because `Q` is infinite. `g ↦ diag(g, det(g)^(-1), 1, …, 1)`
  embeds `GL_n(Q)` in `SL_m(Q)` for `n < m`. So `sl-odd-q-simple-inputs-for-gl-n-q-root` holds.
- **Clause 1.** `ker φ ∩ SL_m(Q)` is normal in the simple group `SL_m(Q)` and misses `s`, so it is trivial. ✓
- **Clause 2 (⇐).** By clause 1. ✓
- **Clause 2 (⇒).** Take `P = K` and the identity map. ✓
- **The sentence Σ_(P,s).** Homomorphisms `<x | r> -> K` are exactly the tuples with `r(k) = 1`, so
  `∃x (r(x) = 1 ∧ w_s(x) ≠ 1)` is the criterion. ✓
- **Clause 3.** This is the (⇐) direction for the fixed `P`, composed with `GL_n(Q) ≤ SL_m(Q)`. ✓
- **Clause 4.**
  - The survey citation is correct. Proposition 3.3(2) of arXiv:2306.16356v3 is the proposition "Every
    countable group with a solvable word problem embeds into a finitely presented group with solvable word
    problem … (2) The group GL_n(Q) for all n ≥ 2". I counted the shared theorem counter in the survey LaTeX:
    Prop 3.1, Prop 3.2, Prop 3.3, Rem 3.4, Cor 3.5.
  - The chain is sound: BH ⇒ BH(H_m) ⇒ BH(P_m) ⇒ Σ_(P_m,s) in some finitely presented simple group ⇒ the root
    for `n < m`.
- **Clause 5.** This is the contrapositive of clause 3, correctly quantified over odd `m >= n+1`, every
  finitely presented `P ⊇ SL_m(Q)` and every `s ≠ 1`. ✓

## Calibration

- **Simplicity is essential.** For `SL_m(Z[1/p])` the one-element criterion fails, because congruence quotients
  kill any fixed `s` modulo suitable primes while being nontrivial. The node uses simplicity exactly where
  needed.
- **O1.** Nothing requires `P` to be residually finite, which is consistent with O1.

## Suggestion (structural, not an error)

- The `H_m` step of clause 4 is logically superfluous. BH implies BH for the finitely presented decidable `P_m`
  directly.
- Keeping it makes the whole route depend on `fg-groups-have-simple-kazhdan-hosts-of-same-wp-degree`. That node
  was refereed once, repaired on 09-17, and is irrelevant to clauses 1–3 and 5.
- Consider moving the `H_m` bullet to a remark and dropping that node from `requires:`. Then the claim's status
  rests only on the elementary simplicity node.

## Citation check

- The "Why it matters" section cites Mikaelian, arXiv:2507.04347 (v8, revised 2026-06-03), §1.4. Verified:
  - the section heading is "The problem of explicit embedding for GL(n,Q), other possible problems";
  - it quotes Kourovka 14.10(c);
  - it states "We would like to announce that, as another application of Algorithm 1.1, an explicit embedding
    of GL(n,Q) into some finitely presented Γ_n reflecting this question is suggested."
- The node's wording ("announced") is accurate.

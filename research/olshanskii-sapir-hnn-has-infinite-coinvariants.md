---
rg: 2
id: olshanskii-sapir-hnn-has-infinite-coinvariants
kind: claim
title: Some power of the Ol'shanskii–Sapir endomorphism has an infinite coinvariant group
distinct_from:
  olshanskii-sapir-fp-ascending-hnn-of-exponent-n-group: that imports the finitely presented extension and its data; this asserts that one of its coinvariant groups is infinite, which would give a finitely presented infinite torsion group.
---

**OPEN.** For some sufficiently large odd `n`, with the Ol'shanskii–Sapir data
`𝒢 = H̄*_phi`, `phi(c_i) = w_i(c)`
(`olshanskii-sapir-fp-ascending-hnn-of-exponent-n-group`), some `m >= 1` makes
the coinvariant group

```text
H̄_{phi^m} = < c_1, ..., c_m | ℛ, 𝒱, ℛ^{(1)}, ..., ℛ^{(m-1)}, c_i = w_i^{(m)}(c) >
```

infinite, where `w^{(m)}` is the `m`-fold substitution.

The presentation above is equivalent to `H̄ / << h^-1 phi^m(h) >>`. For the
normal closure, the generators `c_i^-1 phi^m(c_i)` suffice, because
`(xy)^-1 phi^m(xy)` is a conjugate of `x^-1 phi^m(x)` times `y^-1 phi^m(y)`. Once
`c = w^{(m)}(c)` holds, the derived relators satisfy `r^{(j+m)} = r^{(j)}`, so only
`j < m` are needed.

**Consequence.** By `ascending-hnn-torsion-quotients-see-only-coinvariants`,
`𝒢/<<t^m>>` and `H̄_{phi^m}` would be finitely presented infinite torsion
groups, answering Zaremsky Problem 1.11
(`fp-torsion-via-olshanskii-sapir-coinvariants`). `H̄_{phi^m}` has exponent `n`,
so it would also be a finitely presented infinite group of bounded exponent. By
the restricted Burnside theorem it would not be residually finite.

## Attempts

- `m = 1` is exactly Rips' construction with `u_i = w_i`, the words of the
  Ol'shanskii–Sapir CEP chain `B(m,n) <= B(m+2,n) <= B(infinity,n) <= B(s,n) <= ℋ`.
  Ol'shanskii–Sapir (footnote 5) report that "in all known cases the resulting
  group is obviously finite". They do not say whether that covers their own
  words `w_i`. Not attempted yet.
- What deciding it needs: the explicit words `w_i` (their Remark 1.4 and
  Remark 4.3) and the S-machine presentation `Z(𝕊, Λ)` of `ℋ` (§5.1–§5.3,
  read 2026-09-13). The generators are `X = K ∪ A ∪ R` (state, tape and command
  letters). For each rule `τ` and each state letter `z` there is a relation
  `r(τ,z_-)^-1 z(ω) r(τ,z) = v(z_-) z(ω') u(z)`, plus `r(τ,z) b = b r(τ,z)` for
  every `b in A(z)` whenever `τ` does not lock `z`-sectors, plus the hub
  `Λ(0) = 1`. `⟨A(κ(1))⟩` has exponent `n` (Lemma 5.2).
- Conditional first test. Suppose every `b_i` is a word in the tape letters
  `A(κ(1))`. That is likely, since the chain ends in `B(s,n) <= ℋ`, but
  unverified: check that `B(s,n)` of Theorem 1.3 is `⟨A(κ(1))⟩`. Then in
  `H̄_phi` every generator equals a word in `A(κ(1))`, so the image of
  `A(κ(1))` is the whole group. So every command letter `r(τ, κ(1))` of a rule
  that does not lock `κ(1)`-sectors is central there. By Fig. 13 those are the
  working rules of steps `𝕊_2, ..., 𝕊_{2n}`. What remains is to push this
  through the transition relations at `z = κ(1)` and the hub, where a collapse
  to a finite group would show.
- Every torsion quotient of `𝒢` is controlled by these groups (item 1 of
  `ascending-hnn-torsion-quotients-see-only-coinvariants`). So if all of them
  are finite, the Ol'shanskii–Sapir extension is dead for Problem 1.11 in the
  same way as Grigorchuk's
  (`grigorchuk-hnn-extension-has-only-finite-torsion-quotients`).

---
rg: 2
id: aff-n-z-localized-lies-in-fp-self-similar-group
kind: claim
title: For some prime l and every n, the self-similar group Aff_n(Z_(l)) lies in a finitely presented self-similar group
distinct_from:
  rational-iwahori-group-lies-in-fp-self-similar-group: that is the Mobius group Gamma_p on the p-ary tree, which is not finite-state; this is the finite-state affine group Aff_n(Z_(l)) on the l^n-ary tree, for every n.
  aff-n-over-z-localized-at-ell-is-rf-and-self-similar: that is the established finite-state self-similar action of Aff_n(Z_(l)) itself, which is not finitely generated; this asks for a finitely presented self-similar overgroup of it.
  fp-self-similar-groups-embed-in-fp-simple-groups: that is Zaremsky's theorem that finitely presented self-similar groups embed in finitely presented simple groups; this would supply it with an input containing GL_n(Z_(l)).
  sl-2-z-localized-has-fp-hecke-overgroup: that asks for any finitely presented overgroup of SL_2(Z_(l)) together with a Hecke extension; this asks for a self-similar one, without the Hecke condition.
---

**OPEN.** There is a prime `l` such that for every `n >= 1` the group
`Aff_n(Z_(l)) = Z_(l)^n ⋊ GL_n(Z_(l))` embeds in a finitely presented
self-similar group, acting on a regular rooted tree (not necessarily the `l^n`-ary
one of `aff-n-over-z-localized-at-ell-is-rf-and-self-similar`).

**Constraints on a witness `S`.**
- `S` is residually finite (it acts faithfully on a rooted tree).
- `S` is not a finitely generated linear group
  (`infinite-prime-localizations-embed-in-no-fg-linear-group`).
- `S` is not affine: its finitely generated affine subgroups over `Z_(l)` see only
  finitely many primes (part 4 of the established node). So `S` must be a
  genuinely non-linear automaton group containing, for every prime `q != l`,
  elements with `q^j`-th roots for all `j`.

## Attempts

None yet. Taking the Röver--Nekrashevych group `V_{l^n}(Aff_n(Z_(l)))` does not
help: a finitely generated subgroup of it involves only the sections of finitely
many finite-state affine maps, which lie in some `Aff_n(Z[1/m])`.

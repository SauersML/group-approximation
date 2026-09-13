# Complex finitely presented simple groups from Boone–Higman for A_p^2 A (lane solve-bh-complex-wp)

Date: 2026-09-13. Target root: `fp-simple-groups-with-arbitrarily-complex-word-problem` (OPEN).

## Outcome

- **Not solved.** The root stays OPEN.
- **Landed.** A sharper sufficient condition: Boone–Higman for finitely presented
  residually finite groups in the product variety `A_p^2 A` implies the root
  (`complex-fp-simple-groups-from-apapa-rf-boone-higman`). That class sits strictly
  between the metabelian case (`fp-metabelian-groups-satisfy-boone-higman`, easy word
  problems) and Problem 5.3(12) (`fp-residually-finite-boone-higman`).

## New nodes

- `kms-hard-fp-rf-groups-lie-in-apapa-variety` (ESTABLISHED, import) with route
  `kms-hard-fp-rf-groups-lie-in-apapa-variety-citation`.
- `fp-rf-apapa-groups-satisfy-boone-higman` (OPEN), with the specialization route
  `fp-rf-apapa-bh-from-fp-rf-boone-higman`.
- `complex-fp-simple-groups-from-apapa-rf-boone-higman` (route into the root).

## Literature check: is the root already known?

- **Birget's survey.** Birget, arXiv:math/0310335, §1 (seen through a web search
  summary; re-read before citing further): "A consequence of this conjecture would
  be that the word problem of finitely presented simple groups can have arbitrarily
  large time complexity", and "All known finitely presented simple groups have
  word problems with rather low complexity". The root node already quotes Birget's
  coNP-completeness of `nV` (arXiv:1902.03852).
- **Twisted Brin–Thompson papers.**
  - Belk–Zaremsky, arXiv:2001.04579 (abstract read): applications are quasi-isometric
    embeddings into two-generated simple groups and finiteness properties
    `F_(n-1)` but not `F_n`. No word-problem complexity statement.
  - Zaremsky, arXiv:2405.18354 (abstract read): the type (A) criterion and
    Boone–Higman for subgroups. No complexity statement.
- **Large Dehn functions.** Zaremsky, arXiv:2305.15176: finitely presented simple
  groups with at least exponential Dehn function. Their word problems stay easy
  (see `research/artifacts/ideas-2026-09-13/bh/bh-wp-degrees.md`, W1).
- **Other searches.**
  - arXiv:2403.02492 (abstract): the isomorphism problem and ceer degrees of word
    problems for finitely presented groups; nothing about simple groups.
  - arXiv:2402.01882 (abstract): ceer degrees of word problems; nothing about
    finitely presented simple groups.
- **Verdict.** No construction found. Two web searches returned only Birget's
  statement that the question is open.

## Source quotes for the variety statement

Kharlampovich–Myasnikov–Sapir, Bull. Math. Sci. 7 (2017) 309–352, PDF text, and
arXiv:1204.6506v5, PDF text. The verbatim quotes are in
`kms-hard-fp-rf-groups-lie-in-apapa-variety-citation`:
- Theorem 4.21, p. 345: the hard groups exist.
- Theorem 4.18, p. 343: residual finiteness of `G(MM_k)`.
- Theorem 4.3(a), p. 335: the variety `A2p A ∩ ZNk+1 A`.
- Definition 2.2(a), p. 319: the meaning of "as hard as".
- arXiv v5 Theorem 4.19: independent confirmation with the variety in the statement.

The structural sentence from §1.6 of arXiv v5, used in the OPEN node:
"our group is a split extension of an elementary Abelian group of prime exponent by
a metabelian group. Since every metabelian group has easy word problem and is
residually finite, we can concentrate only on the elementary Abelian subgroup".

## Attempts recorded in this lane

1. **Hard groups in the Boone–Higman classes already established.** Dead.
   - Linear groups over fields have logspace word problems. The metabelian chain
     lands in finite products of linear groups.
   - The Röver–Nekrashevych and twisted Brin–Thompson hosts add one exponential:
     `(RN1)` and `(TBO2)`.
   - So all envelopes these chains produce share one recursive bound, and
     `complexity-bounded-host-classes-are-not-universal` excludes them as witnesses.
2. **A type (A) actor over the configuration module.** Not pursued.
   - Faithful actions of solvable groups with finitely many orbits on two-element
     subsets are rare.
   - The Mikhailova-type enlargement is circular: Cornulier's criterion needs an
     action that is already of type [A_2].
   - Both are recorded in `type-a-actors-with-arbitrarily-hard-word-problem`
     (Attempt 4) and the ideas files.
3. **A translation virtual endomorphism on the KMS module.** Dead as stated.
   - Aim: a faithful self-similar action on a finite-index subgroup, then Zaremsky's
     Theorem 1.1.
   - The counter shift on the finite-index normal subgroup `T(V_R)` commutes with add
     and subtract commands. It does not commute with zero tests, which the
     `A`-letters carry (relations G5 and G8 of §4.1).
   - Not examined: machines whose zero tests are invisible to the shift, and
     p-adic or digitwise shifts compatible with `(t-1)^p = t^p - 1` in `F_p[t]`.

## Exact remaining gap

Any one of these closes the root:
- `fp-rf-apapa-groups-satisfy-boone-higman`, or just a finitely presented simple
  overgroup of one `G(MM_k)` per recursive bound;
- `fp-self-similar-groups-with-arbitrarily-hard-word-problem`;
- `type-a-actors-with-arbitrarily-hard-word-problem`.

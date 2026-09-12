---
rg: 2
id: surjunctivity-recognition-dichotomy
kind: claim
title: Recognizing surjunctivity is trivial iff Gottschalk's conjecture holds, and otherwise second-level complete
distinct_from:
  approximation-property-recognition-dichotomy: that is the dichotomy for hyperlinearity among the local approximation properties; this is the row for surjunctivity, which is not a local approximation property, with the seed supplied by the canonical rectangle host.
  gottschalk-surjunctivity-conjecture: that is the conjecture; this is a theorem about decision problems whose two sides are its two possible answers, and it is established whichever answer is true.
  arbitrary-forbidden-seed-hereditary-property-switch: that is the general switch engine; this instantiates it for surjunctivity and adds the membership bound and the finite-presentation consequences.
artifacts:
  - research/artifacts/gottschalk-rectangle-clauses-and-recognition-2026-09-12.md
---

**ESTABLISHED** as a dichotomy by `surjunctivity-recognition-dichotomy-proof`.
Which side holds is exactly Gottschalk's conjecture.

Exactly one of the following holds.

```text
(A)  Every group is surjunctive.  SURJ_fp, SURJ_rec, SURJ_enum are the full
     sets and the negative sets are empty; all are decidable.

(B)  Some group is not surjunctive.  Then
     (B1) some finitely presented group is not surjunctive: the canonical host
          P(D) of any counterexample's rectangle data;
     (B2) SURJ_enum is Pi^0_2-complete and NONSURJ_enum is Sigma^0_2-complete;
     (B3) SURJ_fp is Sigma^0_1-hard and lies in Pi^0_2 \ Pi^0_1, and NONSURJ_fp
          is Pi^0_1-hard and lies in Sigma^0_2 \ Sigma^0_1.
```

So the following are equivalent:

```text
(i)   Gottschalk's conjecture fails;
(ii)  some finitely presented group is not surjunctive;
(iii) SURJ_fp is undecidable;
(iv)  NONSURJ_fp is not recursively enumerable;
(v)   SURJ_enum is Pi^0_2-complete.
```

**Reading.** A complete finite-certificate format that lists every nonsurjunctive
finite presentation exists iff there are none. A search over one host with
decidable word problem, such as the binary Leavitt unit group, is still
`Sigma^0_1`.

**Attribution.**
- For Markov properties, hardness on recursively presented groups is Theorem 3.1
  of Bilanovic--Chubb--Roven, Arch. Math. Logic 59 (2019) 293--312. The
  repository's switch theorem proves it in-house.
- The finite-presentation clause is the Adian--Rabin theorem (Lyndon--Schupp,
  *Combinatorial Group Theory*, Chapter IV, Theorem 4.1), applied to the Markov
  property "surjunctive".

**Not claimed.**
- `Pi^0_2`-completeness of `SURJ_fp`: that needs a surjunctivity-safe
  finite-presentation compiler.
- The two-generator recursive row: the bridge of
  `second-level-rice-theorem-for-local-approximation-properties` was not re-checked
  for this property.
- Nothing here decides the conjecture.

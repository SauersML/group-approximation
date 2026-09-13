---
rg: 2
id: marker-realizations-reduce-to-two-linear-data-writes
kind: claim
title: If the integer marker times the identity is a word of track shears with k ancillas, it is one with k+1 ancillas whose only data writes are two copies of x <- x + y_1
distinct_from:
  one-ancilla-marker-residue-is-supported-on-window-overlaps: that shows the data track is written at least twice in any realization; this shows two linear writes suffice, so the count is sharp and data writes can be taken linear.
  data-exact-read-ancilla-words-realize-only-translations: that closes a class of words; this is a normal form, showing which restrictions on data writes a negative proof cannot use.
  injective-binary-automata-are-stably-formalizable: that is the open hub; this normalizes candidate realizations of its integer test object and decides nothing.
artifacts:
  - research/artifacts/marker-nonlinear-ancilla-words-2026-09-12.md
---

**ESTABLISHED 2026-09-12** by `marker-two-linear-data-writes-reduction-proof` (w7-marker-nonlinear; artifact
Section 2). Verified by w7-vf-nonlinear (`w7-vf-nonlinear-verification-2026-09-12.md`, Section 2).

**Statement.** Suppose `V` realizes `tau x id` on tracks `(t; s_1, ..., s_k)`. Let `V'` be `V` on
`(y_1; y_2, ..., y_(k+1))`. Then the word below realizes `tau x id` with `k + 1` ancillas. It uses
`m(tau x) = m(x)`.

```text
[x += y_1], [y_1 += x], V', [y_1 += x], [x += y_1], [y_1 += m(x)]      (applied left to right)
```

**Consequences.**
- The two data writes are `x += y_1`, so in the normal form the data track has ancilla degree at most
  1 at every time.
- Invariants that count data writes, or that filter by the data track's ancilla degree, cannot obstruct.
- The nonlinear content is `tau` acting on the ancilla combination `x + y_1`.
- The normal form is circular as a construction.

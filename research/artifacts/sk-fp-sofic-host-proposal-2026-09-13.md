# sk-fp-sofic-host: manuscript proposal (2026-09-13)

**Recommendation: no change by default.** One optional sentence is below, in case the Questions paragraph wants to say
why Open problem 6.1 needs a new idea.

## (a) Current text
From main's rev3, blob md5 274f1936…, l.408–415:
```latex
A finitely presented LEF group is residually finite~\cite{VershikGordon},
and the infinite simple group $G_X$ is not, so $G_X$ is not finitely
presented. Finitely presented infinite simple groups with
property~\textup{(T)} exist~\cite{CapraceRemy}. Is there one that is
sofic, or at least hyperlinear? A positive answer would also answer Open
problem~6.1 of Alekseev and Thom~\cite{AlekseevThom}, which asks for
finitely presented sofic groups with property~\textup{(T)} that are not
residually finite.
```
Rev4 decision item 79 (a-U9) already changes "A positive answer" to "A sofic example".

## (b) Optional sentence, appended after "residually finite."
```latex
Every finitely presented Kazhdan group obtained from groups locally
embeddable into amenable groups by subgroups, directed unions, extensions
with amenable quotient, amalgamated products, HNN extensions and finite
products is residually finite, so such an example needs approximations of
a new kind.
```
Proof: `lea-permanence-closure-fp-kazhdan-rf-proof`. It is (T) plus FA plus the standard fact that a finitely
presented LEA Kazhdan group is residually finite (Thom, arXiv:0810.2180, e-print l.263–300).

## (c) Length
+4 source lines, no bibliography change (Thom is already cited).

## (d) Trade-off for the reader
The sentence tells the reader that no known soficity construction can answer the question. It adds one fact to trust,
a routine induction not written in the note, and it does not strengthen any theorem. Under the "short" constraint main
may reasonably omit it.

## (e) Status
- `lea-permanence-closure-fp-kazhdan-groups-are-residually-finite`: established, unreviewed, queued with sk-verify-13.
- Sharpness (Deligne's triple cover) rests on `deligne-covers-of-sp2g-z-have-finite-residual-2z`, established by
  citation.

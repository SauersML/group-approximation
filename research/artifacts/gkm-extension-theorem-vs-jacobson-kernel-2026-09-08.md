# GKM Theorem 1.1 against the Jacobson symbol extension

2026-09-08.  Hypothesis check, not a mathematical advance.

An external continuation reported that it had **not** closed the binary
Jacobson question -- it could neither prove that every corona homomorphism
kills the head root nor construct one retaining it -- and identified one
published extension theorem as the natural thing to reach for, then showed it
does not reach.  That negative check is the whole of the new content, and it
is worth carding, because the shape of the Jacobson symbol sequence invites
exactly this move.

## The theorem, read

Gao, Kunnawalkam Elayavalli and Mj, *Strongly converging unitary
representations for extensions by exact groups*, arXiv:2607.29571v1 (31 July
2026), Theorem 1.1, verbatim from the v1 HTML:

> Let `G` be a finitely generated residually finite amenable group and `L` be
> an exact MF/PMF/PFF group.  Then `G x| L` is MF/PMF/PFF.

Fetched and read 2026-09-08.  The archive had already body-read Definition 2.6,
Theorem 1.2, Theorem 1.5 and Theorem 1.6 of this paper
(`research/artifacts/hyperlinear-q34-literature-2026-08-18.md`); Theorem 1.1
was not previously recorded here.

## The extension it would be applied to

`binary-jacobson-elementary-mark-is-finite-quotient-invisible` establishes,
for `J = F_2<S,T | TS = 1>` and `E = EL_5(J)`, the symbol sequence

```text
1 -> L -> E -> Q_0 -> 1,
L = GL_fin(N x {1,...,5}, F_2),   Q_0 = EL_5(F_2[z,z^-1]),            (JFQ1)
```

with `L` infinite simple locally finite and `Q_0` residually finite.  The
resemblance to Theorem 1.1 is real: an amenable-looking kernel over a
residually finite quotient is exactly the input shape.

## Where it fails, hypothesis by hypothesis

Matching `(JFQ1)` to `G x| L` of the theorem puts the Jacobson kernel `L` in
the role of the theorem's base `G`, and `Q_0` in the role of the theorem's
`L`.  Of the three hypotheses on the base:

- **amenable: SATISFIED.**  `L` is locally finite (a directed union of the
  finite groups `GL_n(F_2)`), and locally finite groups are amenable.  This is
  the hypothesis a reader would expect to be the obstacle, and it is not.
- **residually finite: FAILS.**  `L` is infinite simple, so its only quotients
  are itself and the trivial group; a residually finite group with no proper
  nontrivial quotient embeds in a finite group and is finite.
- **finitely generated: FAILS.**  A finitely generated locally finite group is
  finite, and `L` is infinite.

Both failures are forced by the same two words -- *infinite simple locally
finite* -- so they are not artifacts of the particular model of `L` and cannot
be repaired by changing the rank or the basis.

Independently, Theorem 1.1 is about a **semidirect** product, and no splitting
of `(JFQ1)` is established here.  Nothing in this note asserts that `(JFQ1)`
does not split; the point is only that applying a semidirect-product theorem
to it would require first proving something nobody has proved.

The other side of the theorem is unproblematic and is worth recording so it is
not re-checked: `Q_0 = EL_5(F_2[z,z^-1])` is a finitely generated linear group,
hence residually finite, hence MF, and finitely generated linear groups are
exact.  So the theorem's requirement on its `L` is met.  The mismatch is
entirely on the kernel side.

## Why no theorem of that shape can apply

`binary-jacobson-steinberg-head-root-is-mf-invisible` was established earlier
the same day: `Rad_MF(St_5(J)) = L`, so `E` is **not** operator MF.  Theorem
1.1 concludes MF of the total group.  By the exact dichotomy
`binary-jacobson-mf-radical-dichotomy`, `E` is MF exactly when the head root is
MF-visible, so any theorem concluding MF of `E` would contradict the
established head collapse.

This corollary inherits that node's dependency: the rank-weighted proof uses
property (T) and is not machine-checked, and
`property-t-free-jacobson-head-collapse` is the open obligation to remove it.
So the corollary is conditional.  The hypothesis check of the previous section
is not -- it is a two-line inspection against `(JFQ1)` and stands whatever
happens to the rank-weighted proof.  The two together are the useful reading:
the route is dead by inspection, and it is dead for a reason, not by accident
of one paper's hypotheses.

## What is still open

Everything the continuation was asked about.  It could not prove that every
corona homomorphism kills the head root, and it could not construct one
retaining it; and `binary-jacobson-head-retaining-homomorphisms-are-faithful`
is why the second is so hard -- a retaining homomorphism is automatically a
faithful embedding of the whole elementary group, so there is no partial
target to aim at.  All three of those facts were already established here.  The
continuation's genuinely new contribution is the negative literature check
above.

Note a rank convention difference: the continuation writes the mark as
`e_12(1-st)`, this archive works at rank five and writes `x_13(1-ST)`.  The
faithfulness statement that makes retention all-or-nothing is proved at rank
five.

## Provenance

The continuation reported working from previously screened Cairn material,
Schafhauser's 2023 amalgamation-paper abstract, and the July 2026 version of
the GKM paper, with its supplied fullness theorem left as an assumed input, and
no proof-assistant verification.  Nothing was drawn from the Schafhauser
abstract, which it cites in provenance without using.

Theorem 1.1 was re-fetched and re-read here before landing rather than taken on
the continuation's report; the quotation above is from that read.  The
structural facts about `(JFQ1)` are cited from the established node, not
restated.  No Lean was written or built.

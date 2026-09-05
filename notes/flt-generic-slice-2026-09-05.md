# anthropics/fermats-last-theorem: the generic slice, packed at vendor/flt

Companion to `flt-repo-assessment-2026-09-05.md`, which is right about what
the upstream lacks (no singular cohomology of spaces, characteristic classes,
topological K-theory or Borsuk–Ulam) and records the disk incident.

Below that level the upstream has generic library material this development
can use: bounded double complexes with a Künneth theorem over a field, the
`IsDirectLimit` predicate (already vendored, used by
`Analysis/SequentialGroupColimitDirectLimit.lean`), topological-group shims,
`SU(2)` Euler angles, QR/Iwasawa decompositions, elementary-matrix
factorisation of `SL_n`, Selberg's and Minkowski's lemmas, `SL₂` ping-pong,
Kurosh-rank free bases, Schreier transversals, the argument principle and
residues, compact convolution operators on `L²`, Haar quotient measures,
complete reducibility for compact groups.

A 2,344-module closure of those results is preserved **packed** at
`vendor/flt/flt-slice.tar.gz`, with `INDEX.md` (headlines) and
`STATEMENTS.md` (every statement, greppable). Packed, it is outside every
scanner and rsync stanza; unpack only the closure a lane needs, into
`GroupApproximation/ThirdParty/FLT/` (gitignored; `git add -f` once it
compiles). Recipe and the lane map: `vendor/flt/UPSTREAM.md`.

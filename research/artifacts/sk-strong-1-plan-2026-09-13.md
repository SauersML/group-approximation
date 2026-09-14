# sk-strong-1 plan: a universal simple Kazhdan LEF group

Lane `sk-strong-1` (SK swarm, wave 6), 2026-09-13. Lens: the single strongest theorem about the note's groups that
can be proved this week and changes how people see simple Kazhdan groups.

## Target (Theorem U)
- **U1.** Every countable residually finite group embeds in an infinite, finitely generated, simple group with
  property (T) that is LEF (so sofic and hyperlinear).
- **U2 (universality).** There is ONE infinite finitely generated simple Kazhdan LEF group containing every finitely
  generated residually finite group with solvable word problem. In particular it contains every finitely presented
  residually finite group and every finitely generated linear group.
- **U3 (sharpness).** No finitely generated group contains every finitely generated residually finite group: there are
  continuum many of them, and a finitely generated group has countably many finitely generated subgroups. A group
  that embeds in a simple Kazhdan LEF group is locally LEF.

## Why it matters
Simple Kazhdan groups are usually pictured as rigid objects far from finite groups. U2 says a single finitely
generated simple Kazhdan group, approximable by finite groups, contains every finitely generated linear group.
This is a Higman-type universality inside the Kazhdan world, with the approximation property kept.

## Route
1. **Embedding theorem:** every countable residually finite group embeds in a finitely generated residually finite
   group. First check the literature (J. S. Wilson, "Embedding theorems for residually finite groups", Math. Z. 1980?).
   If no source is found, prove it inside a Cartesian product of finite wreath products.
2. **Overgroup of commutators** (sk-universal-embedding-a, Lemma 2): a f.g. RF `Γ` lies in `[Δ,Δ]` for a f.g. RF `Δ`.
3. **Envelope** (Theorem E, 3bcc003284): `EL_3(LC(X,F_2)⋊Δ)` over a free minimal Toeplitz subshift, and
   `γ ↦ diag(u_γ,1,1)` on `[Δ,Δ]`.
4. **Universality:** free products of residually finite groups are residually finite (Gruenberg 1957). There are
   countably many isomorphism classes of f.g. groups with solvable word problem.
   - Linear case: f.g. linear groups are RF with solvable word problem (Malcev; Rabin).
   - Finitely presented case: fp RF groups have solvable word problem (McKinsey–Malcev).

## Not duplicated
- sk-universal-embedding-a: per-group, finitely generated RF, done.
- sk-universal-embedding-b, sk-lef-embedding-c/d/e: finitely generated LEF.
- sk-wp-embedding: solvable-word-problem iff.
This lane adds countable input, one universal group, and the sharp boundary.

## Risks and fallbacks
- Step 1 might be false, or unavailable in citable form. Fallback: U2 for any countable family of f.g. RF groups
  whose free product embeds in a f.g. RF group by an explicit construction.
- Everything is unreviewed until sk-verify-4 passes it.

## Deliverables
- Claims with complete routes, and an artifact.
- A §6 proposal: at most a two-line corollary sentence for the note, and only after review.

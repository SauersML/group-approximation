# gq-ring-fp-simple: notes (2026-09-17)

Lane `gq-ring-fp-simple` of the GL_n(Q) swarm (root `gl-n-q-embeds-in-fp-simple-group`).
Target: a finitely presented simple ring of characteristic 0
(`fp-simple-ring-of-characteristic-zero-exists`).

## Literature (secondary; nothing re-read at the source)
- **Belyaev**, "Subrings of finitely presented associative rings", Algebra i Logika 17
  (1978), 627–638. It is a Higman embedding theorem: every recursively presented
  associative algebra over a commutative ring, or over a field finitely generated over its
  prime field, embeds in a finitely presented one. Per search summaries, the embeddings are
  unital and undistorted. So `Q` embeds in some finitely presented ring. The explicit ring
  of `q-embeds-in-a-corner-of-a-fp-toeplitz-ring` does this by hand, with 4 relations.
- **Bokut** (1960s): embeddings into simple and into finitely generated simple algebras over
  fields. The statements were not checked at the source. Cairn records the same reading
  (`algebra-boone-higman-conjecture`, Attempt 1).
- **Evans–Mandelberg–Neff** (1975): the weak Boone–Higman theorem for algebras, in
  characteristic `p` according to the BBMZ survey §3.
- A Proc. AMS 100 (1987) paper titled "Embedding countable rings in 2-generator rings" is a
  lead for the finitely generated form. Its PDF returned 403 here.
- No source found asserts or refutes the existence of a finitely presented simple ring of
  characteristic 0.

## Results landed by this lane
1. `integral-form-algebras-have-no-fg-subring-containing-q` (ESTABLISHED, lane proof):
   finitely generated subrings of `M_n(A ⊗ K)` with `A` free abelian never contain `Q`. The
   proof uses a coefficient ring `D`, the Nullstellensatz to find a prime that is not a unit
   of `D`, and Krull intersection. It answers lane `gq-ring-leavitt`'s first step
   negatively for every Leavitt algebra over every field.
2. `q-embeds-in-a-corner-of-a-fp-toeplitz-ring` (ESTABLISHED, lane proof):
   `R_T = Z<S,T,N,A | TS=1, NS=S(N+1), N(1-ST)=0, A(N+1)=1>` has `Q ≅ E R_T E`,
   `E = 1 - ST`, with `1/m = E T^(m-1) A S^(m-1) E`.
3. `gl-n-q-embeds-in-e-n-plus-1-of-a-fp-ring` (ESTABLISHED, lane proof):
   `GL_n(Q) <= E_(n+1)(R_T)`, which is finitely generated. Its concrete model has solvable
   word problem.
4. `fp-simple-ring-of-characteristic-zero-exists` (OPEN), with four recorded attempts.

## The requirement that remains
Characteristic-0 scalars come from an operator that is congruent to the integer `m` on an
idempotent. The Toeplitz vacuum gives this on a *minimal* idempotent, and that forces a
proper finitary ideal. A simple example needs a purely infinite analogue: finitely many
relations forcing, for every `m`, an element `x` and a non-minimal idempotent `f` with
`(x + m)f = mf`, together with a transport of one resolvent to all `m`.

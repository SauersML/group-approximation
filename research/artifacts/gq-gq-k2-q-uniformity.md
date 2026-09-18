# K_2, Steinberg groups and uniform presentations of GL_n(Q) (lane gq-k2-q, 2026-09-17)

Question of the lane: what does a single host for the ascending chain `GL_n(Z[1/m!])` (whose union is `GL_n(Q)`,
root `gl-n-q-embeds-in-fp-simple-group`) need from the presentations, and can the relations be made uniform in m?

Verification key: **[P]** proved here (lane proof, not independently reviewed); **[R]** imported through a landed
repo node; **[C]** cited from the literature and NOT re-read at source in this lane (the Weibel K-book and the arXiv
PDFs did not decode through WebFetch; local PDF reading is forbidden by the swarm rules).

## 1. Generation: the chain is GL_n(Z) plus one commuting element per prime [P]

Node `gl-n-q-generated-by-gl-n-z-and-prime-dilations`: `GL_n(Q) = <GL_n(Z), e_p = diag(p,1,...,1) : p prime>`,
`SL_n(Q) = <SL_n(Z), d_p = diag(p,p^-1,1,...,1)>`, the `e_p` generate `E = ⊕_p Z`, and
`GL_n(Q) = SL_n(Q) ⋊ ({±1} × E)`.

So a single host `H` for the chain is the same as `GL_n(Z) ≤ H` plus pairwise commuting `h_p ∈ H` such that each
finite subfamily generates `GL_n(Z[1/S])` in the standard way. Compatibility along the chain costs nothing extra:
it is built into choosing one `h_p` per prime.

## 2. A presentation with no K_2 at all: the adelic chamber colimit

Node `sl-n-q-is-colimit-of-lattice-stabilizers` (ESTABLISHED after review by gq-referee-b; the imports are read only through secondary transcriptions, see the route):
`SL_n(Q)` is the colimit of the lattice stabilizers `Γ_c = diag(c) SL_n(Z) diag(c)^-1`, `c = (1 | c_2 | ... | c_n)`
squarefree, and their intersections, over the cells of the restricted product `∏'_p Δ_p` of standard Bruhat–Tits
chambers.
- The density and orbit steps are [P], checked by the referee. Contractibility of Euclidean buildings (I2: Kramer
  arXiv:1009.3089 §6.4(a) on ar5iv) and the strict-fundamental-domain theorem (I3: Brown 1984 Thm 1′, as transcribed in
  arXiv:2603.25586 Thm 2.1) are [C]. I3 is simplicial, so it is applied to the staircase triangulation of the product.
- For `n = 2` it is an infinite cube of groups. Vertex groups are the conjugates `diag(1,c) SL_2(Z) diag(1,c)^-1`
  (`c` squarefree), and the cube groups are `Γ_0`-type congruence subgroups. For one prime it is Serre's amalgam
  `SL_2(Z[1/p]) = SL_2(Z) *_{Γ_0(p)} SL_2(Z)^{diag(1,p)}` ([C], Serre, *Trees*, II §1.4).
- For `GL_n(Q)` add `{±1} × E` acting on the diagram, with `e_p` rotating the types of `Δ_p`.

**Uniformity.** Every vertex group is a copy of `SL_n(Z)`. The local diagram at `p` has the same shape for every
`p`: the faces of an `(n-1)`-simplex, with groups cut out by congruences mod `p`. Primes interact only through
intersections of vertex groups. So the relations are computable uniformly in `p`, but `p` enters through
congruence conditions mod `p`, not only as "multiplication by `p`".

## 3. The Steinberg view and where K_2(Q) enters

- `St_n(R)`: generators `x_ij(r)`; relations `x_ij(r)x_ij(s) = x_ij(r+s)`, `[x_ij(r), x_jk(s)] = x_ik(rs)` (`i ≠ k`),
  and `[x_ij(r), x_kl(s)] = 1` (`j ≠ k`, `i ≠ l`). These are finitely many *schemata* in the ring operations, so they
  are uniform in the strongest sense.
- For a field `F` and `n >= 3`, `K_2(n,F) = ker(St_n(F) -> SL_n(F)) -> K_2(F)` is an isomorphism. This is [R]
  through import 2 of `elementary-groups-over-polynomial-s-integers-are-fp-proof` (van der Kallen / Weibel III
  Rem. 5.5.2, `n >= d+3` with `d = 0`). Centrality in `St_n(F)` is [C] (Steinberg, Matsumoto).
- Tate [C] (Milnor, *Introduction to algebraic K-theory*, §11): the tame symbols give
  `K_2(Q) ≅ {±1} ⊕ ⊕_{p odd} F_p^x`, a countable torsion group with a cyclic summand of order `p-1` for every odd
  prime `p`. For a finite set `S`, localization [C] gives `0 -> K_2(Z) = Z/2 -> K_2(Z[1/S]) -> ⊕_{p∈S} F_p^x -> 0`.
  So along the chain the kernel grows by one cyclic group of order `p-1` per new prime.

**Uniformity defect.** The uniform Steinberg schemata over `Q` present `St_n(Q)`, a central extension of
`SL_n(Q)` by `K_2(Q)`, not `SL_n(Q)`. To reach `SL_n(Q)` one adds, for each odd prime `p`, a central relator
killing a symbol whose order is `p-1`. A representative is `{g_p, p}`, with `g_p` a primitive root mod `p`, up to the
bookkeeping of Tate's filtration. That relator depends on the multiplicative arithmetic of `p`, which the additive
schemata do not see.

So there are two uniformly computable schemata (§2 and §3). In neither does `p` enter only as a ring constant.
`SL_n(Q)` itself is not finitely generated, so "uniform" can only mean what §4 lists.

## 4. What a single host needs (for gq-scott-union, gq-steinberg-q, gq-en-ring, gq-union-obstruct)

- **N1 [P].** One copy of `GL_n(Z)` (Scott's groups already contain it) and a free abelian subgroup of infinite
  rank `<h_p>` realizing the primes (§1).
- **N2.** Non-residually-finite: O1 of the root.
- **N3 [P, relative to the node in §2].** Beyond N1, the only relations the host must satisfy are the chamber-colimit
  identifications. For each `p` it must identify `Γ_F ⊂ Γ_c` with `Γ_F ⊂ Γ_c'` for the finitely many local cells.
  - **Locality question (OPEN, not claimed):** is `GL_n(Z[1/S])` presented relative to `GL_n(Z) * ⟨h_p : p∈S⟩` by
    `[h_p, h_q] = 1` and finite sets `R_p` depending on `p` alone? For `n = 2` and `|S| = 1` this is Serre's amalgam.
  - Even with locality, embedding still needs **injectivity** of the colimit into `H`. A host satisfying the
    relations can collapse more.
- **N4, matrix-ring hosts (`E_n(R)` or `GL_n(R)` with `R ⊇ Q`).** `GL_n(Q) ≤ GL_n(R)` is automatic, and `K_2(Q)`
  plays no role in the embedding.
  - `St_n(R)` is finitely presented for finitely presented `R` and `n >= 4` ([R]
    `steinberg-finite-presentation-and-kazhdan-theorem`, Krstić–McCool; primary source not obtained there).
  - The whole K_2 burden is therefore normal finite generation of `K_2(n,R)` in `St_n(R)`. A necessary sign: the
    images of the infinitely many Tate symbols `{g_p, p}` of `K_2(n,Q)` must follow from finitely many relators.
  - **Stable vanishing [R].** `K_*(L_Q(1,2)) = 0`: node `abc-leavitt-path-k-theory-exact-sequence`
    (Ara–Brustenga–Cortiñas Thm 7.6, read at source there) with `1 - N^t = -1`, as recorded by gq-cuntz-cstar in
    `harmonic-cuntz-simple-group-is-finitely-presented`. So for any unital `R ⊇ L_Q(1,2)`, `K_2(Q) -> K_2(R)` is zero:
    all Tate symbols die in the stable `St(R)`. Only the unstable kernel (`St_3`, `St_4`) is at issue, and that is
    open.
- **N5.** Tree hosts see `Ẑ^n = lim (Z/m!)^n`, where `GL_n(Z)` acts. The primes `e_p` do not act on `Ẑ^n` (they are
  not invertible there), but they do act on the finite adeles `A_f^n = ∪_m (1/m!) Ẑ^n`. The chain's natural space is
  this increasing union of compact-open pieces, as `BS(1,2)` lives on `Q_2 = ∪ 2^-k Z_2`. A host needs a
  "germ at infinity" for that union. This agrees with gq-solenoid / gq-adelic.

## 5. Sparks (not pursued here)

- **Commensurator reformulation.** For `n >= 3` the abstract commensurator of `SL_n(Z)` is `PGL_n(Q) ⋊ <transpose
  inverse>` ([C], Margulis/Borel density; to be checked). Also `GL_n(Q) ↪ PGL_{n+1}(Q)` by `g -> diag(g,1)`. So the
  root for all `n` is equivalent to "the abstract commensurators of the `SL_n(Z)` embed in f.p. simple groups",
  given cofinality in `n` (`gl-n-q-targets-are-cofinal-in-n`).
- **Relative Higman for colimits.** Is there a Higman-type theorem embedding a colimit of f.p. groups over a
  *uniformly computable* diagram (§2) into a f.p. simple group, when every vertex group already embeds (Scott)?
  This is the abstract form of N3.

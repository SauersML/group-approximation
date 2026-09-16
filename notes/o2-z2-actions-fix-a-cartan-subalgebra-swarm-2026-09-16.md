# o2-z2-actions-fix-a-cartan-subalgebra --- swarm pass, 2026-09-16

Agent: `swarm-o2-z2-actions-fix-a-cartan-sub`.

Target (OPEN): every outer strongly approximately inner (SAI) action
`α : Z_2 ↷ O_2` leaves some Cartan subalgebra invariant.
- By `barlak-li-two-half-iff-z2-actions-fix-cartan` it is equivalent to the UCT
  for `M_(2^∞)`-absorbing nuclear algebras, the 2-half of STW Problem II.
- It is still open after this pass.

Outcome: **obstruction** (a symmetry-breaking no-go), plus a record of dead
ends. No progress on existence.

## 1. Setup and orientation

**Read this pass.**
- The target and its Attempts.
- `barlak-li-two-half-iff-z2-actions-fix-cartan`,
  `bootstrap-class-zp-actions-on-o2-fix-a-cartan` (+ proof),
  `o2-zp-cartan-fixing-iff-rokhlin-uct-ascent-proof`,
  `z2-o2-actions-anti-inner-and-o3-rokhlin-criterion`,
  `ghs-z2-commuting-rokhlin-dimension-one-dual-sai`,
  `izumi-rokhlin-approximately-representable-duality`,
  `cartan-respecting-o2-automorphisms-proof`,
  `uct-cartan-trivial-k-kirchberg-uct-iff-cartan`, and the `zp-o2-*` KK^G nodes.
- Artifacts `research/artifacts/uct-o2-cyclic-actions-2026-09-12.md`,
  `research/artifacts/uct-cartan-obstruction-2026-09-12.md` and
  `research/artifacts/uct-z2-square-zero-phantoms-2026-09-13.md`.

**Where the problem sits.**
- Barlak--Li Corollary 4.15, as recorded in the repository: for outer SAI
  `α : Z_q ↷ O_2`, "fixes a Cartan" ⟺ `O_2 ⋊_α Z_q` satisfies the UCT.
- Every attack recorded in the 2026-09-12 artifact dies at the same step: no
  coherent choice of masa along the approximation. The target's Attempts call
  this "classification supplies no coherence".
- This pass tries to make that failure precise.

**Duplicate search.** `bin/cairn search` and `--similar` found no node proving
anything like the no-go below. The nearest hits were
`packet-natural-selector-no-go-proof`, a different von Neumann packet program,
and `cartan-respecting-o2-automorphisms-proof`.

## 2. What was proven

New claim `research/no-masa-of-o2-is-normalized-by-fixed-point-unitaries.md`,
with direct route `...-proof.md` (`requires: []`, elementary). Let `p` be
prime and `α ∈ Aut(O_2)` with `α^p = id`. No outerness or SAI is assumed.

1. **Normalizing one-parameter groups lie in the masa.** If `D` is a masa of a
   unital `A` and `e^{ith} D e^{−ith} ⊆ D` for small `t > 0`, then `h ∈ D`.
   *Proof idea:* differentiate to get a derivation `[h,·] : D → D`, then kill it
   on the commutative `D` with `δ(e^{isd}) = is e^{isd} δ(d)` and boundedness.
2. **Commutative fixed points force small representations.** If `β^p = id` and
   `A^β` is commutative, every irreducible representation of `A` has dimension
   `≤ p`. `O_2` has no finite-dimensional representations (trace argument
   `2m = m`), so `O_2^α` is **never commutative**.
   *Proof idea:* the orbit representation `⊕ π∘β^k` with the shift unitary; the
   fixed points of `ρ(A)''` are abelian; two cases, by Schur's lemma.
3. **No-go.** No masa of `O_2` is normalized by all `e^{ih}` with
   `h = h* ∈ O_2^α`, equivalently by `U_0(O_2^α)`. Quantitatively, for each masa
   `D` some such `h` makes `t ↦ e^{ith} D e^{−ith}` injective on `[0, a)`.
4. **Never canonical.**
   - Every `α`-invariant Cartan subalgebra lies in an uncountable
     `U(O_2^α)`-orbit of `α`-invariant Cartan subalgebras, none of which is
     fixed by `U_0(O_2^α)`.
   - No assignment `α ↦ Φ(α)` of masas on a nonempty conjugation-closed class,
     for example the outer SAI `Z/p`-actions when that class is nonempty, can
     satisfy
     `Φ(Ad u∘α∘Ad u*) = u Φ(α) u*` for `u ∈ U_0(O_2)`.
     *Reason:* `Ad e^{ih} ∘ α ∘ Ad e^{−ih} = α` for `h ∈ O_2^α`.
5. **Contrast at `p = 2`.** Zorn gives `α`-invariant abelian subalgebras that
   are maximal, and each of them is a masa (split `y = y_+ + y_-` into
   `±1`-eigenparts).

**Bearing on the target.**
- *Where the difficulty is.* Invariant masas are free (item 5). The whole
  difficulty is regularity together with a faithful conditional expectation.
- *What a proof must use.* Items 3–4 show that any construction must use data
  not determined by `α` up to conjugation by `U_0(O_2^α)`. Examples are a
  choice of Rokhlin-type towers, a groupoid model, or a realization of a
  KK-class.
- *Scope.* This rules out every "canonical/functorial Cartan" strategy. It says
  nothing against existence: `B^G` actions do fix Cartan subalgebras, and by
  item 4 those come in uncountable orbits.

**Honest assessment.** Items 1–5 are folklore-level. No priority is claimed.
Their value is making precise the target's "no coherence" failure.

**`p = 3`.** Items 1–4 are proved for every prime, so they apply verbatim to
`o2-z3-actions-fix-a-cartan-subalgebra`. Item 5 does not transfer. For `p = 3`
the eigenparts `y_ζ = (1/3) Σ ζ^{−j} α^j(y)` are not self-adjoint, and
`y_ζ, y_ζ*` need not commute, so the argument in item 5 breaks. No
counterexample was sought.

## 3. Approaches tried, and exactly where each dies

1. **Zorn invariant masa (item 5).** It always exists at `p = 2`.
   - *Dies at* regularity and the conditional expectation. Nothing in the
     construction produces normalizers, and a masa of `O_2` need not be Cartan.
2. **Pointwise-fixed Cartan subalgebras.** The target records Barlak--Li
   Theorem 1.8: invariant ⟺ pointwise fixed for some Cartan.
   - If `D ⊆ O_2^α` is Cartan, `α` should correspond to a continuous
     `T`-valued 1-cocycle `c` on the Weyl groupoid with `c^2 = 1`, rescaling the
     twist fibres. This is the standard Renault picture, recalled and not
     re-verified this pass.
   - Example: the gauge automorphism `λ_{−1}` (`s_i ↦ −s_i`) fixes `D_2`
     pointwise. Its fixed-point algebra is `C*(s_i s_j) ≅ O_4`, since odd–odd
     monomials `s_μ s_ν*` equal `Σ_i s_{μi} s_{νi}*`, and `K_0(O_4) = Z/3`.
     Whether `λ_{−1}` is SAI was not checked.
   - *Dies at:* the cocycle description presupposes the Cartan subalgebra. It
     gives no way to produce one for a given `α`.
3. **Implementing unitaries normalizing a common masa.** If `α = lim Ad u_n`
   with `u_n ∈ O_2^α` and `u_n D u_n* = D` for all `n`, then `α(D) ⊆ D` by
   norm closure.
   - That is sufficient, but necessity is unknown.
   - Item 3 shows one cannot ask for *all* of `U_0(O_2^α)` to normalize `D`.
     So the strengthening "every implementing sequence in `U_0(O_2^α)` works",
     or "`D` is normalized by the whole fixed-point unitary group", is false. A
     countable, specially chosen sequence is not excluded.
   - *Dies at:* choosing the `u_n` coherently, the same coherence step.
4. **Rokhlin dimension ≤ 1.**
   - Barlak--Enders--Matui--Szabó--Winter (arXiv:1312.6289, abstract-level):
     outer actions on unital Kirchberg algebras have Rokhlin dimension ≤ 1.
     The group and hypothesis details were not re-read.
   - Gardella--Hirshberg--Santiago, repository node
     `ghs-z2-commuting-rokhlin-dimension-one-dual-sai`: commuting towers of
     dimension 1 already force the Rokhlin property on `O_2`. So for a
     non-Rokhlin SAI action the towers cannot commute.
   - The attempt: glue Cartan subalgebras of the two tower algebras.
   - *Dies at* gluing two Cartan subalgebras across non-commuting towers. The
     patching unitaries are exactly the non-canonical data items 3–4 say
     cannot be chosen naturally. No estimate was found that forces them to
     normalize a common masa.
5. **Trivial-K repackaging.**
   - *Forward direction:* the target implies that every outer SAI `α` with
     `K_*(O_2 ⋊_α Z_2) = 0` is Rokhlin. Route: Cor 4.15, then Kirchberg--Phillips
     (a UCT trivial-K unital Kirchberg crossed product is `O_2`), then
     `z2-o2-actions-anti-inner-and-o3-rokhlin-criterion`.
   - *Converse:* it would need a mapping-cone argument plus outerness/SAI of
     `id ⊗ γ` for the Barlak--Szabó `γ`. That was not re-verified.
   - Only a repackaging of `barlak-li-two-half-iff-z2-actions-fix-cartan`, so no
     node was written.
6. **Cocycle perturbation `Ad(w)∘α`.** It has order 2 only if `w α(w) = 1`.
   - A Cartan subalgebra invariant for a perturbed model does not transport
     back without the cocycle conjugacy, which is the unknown.
   - *Dies* immediately.
7. **Tensor square `α ⊗ α`.** Circular: a Cartan subalgebra invariant under
   `α ⊗ α` on `O_2 ⊗ O_2` does not give one for `α`. Compare
   `z2-o2-phantom-tensor-square-is-sai-and-self-dual`.
8. **Stabilizing `α ⊗ id_{O_2}`.** The crossed product is
   `(O_2 ⋊ Z_2) ⊗ O_2 ≅ O_2`, by `O_2`-absorption of unital simple separable
   nuclear algebras (standard; not re-verified). `α ⊗ id` is SAI via
   `u_n ⊗ 1`, and outer (standard; not re-verified). So by
   `z2-o2-actions-anti-inner-and-o3-rokhlin-criterion` it is Rokhlin, and it
   fixes a Cartan subalgebra.
   - *Dies at:* `α ⊗ id` is not conjugate to `α`, and a Cartan subalgebra of the
     tensor product does not restrict to the first factor.
9. **Finite-stage approximate conjugacy to a model.** Approximate conjugacy on
   finite sets gives only approximately invariant masas.
   - *Dies at:* a norm limit of approximately invariant masas along finite
     sets need not be a masa, or even exist. No stability theorem for Cartan
     subalgebras under small perturbations of the automorphism is known to
     this pass.
10. **Product-type actions `⊗_n Ad(1 − 2p_n)`.**
    - These preserve product diagonals and so fix Cartan subalgebras.
    - They are very likely already in `B^G` (covered by
      `bootstrap-class-zp-actions-on-o2-fix-a-cartan`). The tensor-limit step
      identifying them with models was not checked.
    - *Dies at:* no information about phantoms.
11. **The induced involution on the Cartan spectrum as an invariant.** It does
    not detect the Rokhlin property.
    - Take the model `⊗^∞ Ad diag(1,−1) ⊗ id` on `M_(2^∞) ⊗ O_2 ≅ O_2`
      (the isomorphism is standard, not re-verified). It fixes the product
      diagonal `(⊗ diagonal of M_2) ⊗ D_2` pointwise. The action is Rokhlin,
      with towers `(1/2)[[1,1],[1,1]]` in late tensor factors.
    - Conjugating by the Hadamard unitaries turns it into `⊗ Ad(flip) ⊗ id`,
      which preserves a diagonal and acts freely on its spectrum.
    - *Dies at:* the same action carries invariant Cartan subalgebras with free
      and with trivial induced involution, so this involution is not an
      invariant of the action.

## 4. Literature gate (2026-09-16)

arXiv API metadata was re-fetched this session. Abstract/listing level only
unless stated.
- C. Schafhauser, A. Tikuisis, S. White, *Nuclear C\*-algebras: 99 problems*,
  arXiv:2506.10902. v1 published 2025-06-12, last updated 2026-05-08. Problem
  II (UCT) is listed as open. The in-text wording was checked in an earlier
  session, not re-read now.
- F. Komura, *Cartan-preserving \*-automorphism groups: realization and
  obstructions for compact abelian groups*, arXiv:2607.18844 (2026-07-21). It
  concerns compact abelian groups and UCT Kirchberg algebras. From the
  abstract, nothing on SAI `Z_2`-actions on `O_2`. Full text not read.
- S. Evington, P. Sibbel, *Principal groupoid models for stable UCT Kirchberg
  algebras*, arXiv:2605.30147 (v1 2026-05-28, updated 2026-06-11). It gives
  models under UCT, which does not help for non-UCT candidates. Abstract level.
- K. Matsumoto, T. Sogabe, *Ergodic automorphisms on Kirchberg algebras*,
  arXiv:2505.23168 (2025-05-29). Not relevant to finite-order actions. Title
  level.
- arXiv:2607.16755 (2026-07-18), *Homotopy of inner automorphism groups of
  Cuntz algebras*: homotopy groups of `Inn(O_n)`, not relevant. Abstract level.
- Barlak--Enders--Matui--Szabó--Winter, arXiv:1312.6289 (v3 2015-12-21):
  outer actions on unital Kirchberg algebras have Rokhlin dimension ≤ 1.
  Abstract level only.
- S. Barlak, X. Li, arXiv:1511.02697 and arXiv:1704.04939v2. Used only
  through repository nodes and the 2026-09-12 artifacts. Not re-fetched this
  pass, so the theorem numbers quoted above (4.12, 4.14(2), 4.15, 4.16, 1.8)
  are as recorded in the repository.
- A further arXiv keyword search (Cartan + UCT, sorted by date) was
  rate-limited (HTTP 429) and not completed this session.

**No 2024–2026 source found** resolves the target, or gives a Cartan
subalgebra for arbitrary outer SAI `Z_2`-actions on `O_2`.

## 5. What remains open

- The target itself, and its `p = 3` sibling.
- Whether "implementing unitaries normalizing a common masa" (Section 3.3) is
  necessary for an invariant Cartan subalgebra.
- A quantitative stability theorem for Cartan subalgebras of `O_2` under
  approximately equal automorphisms. That would bypass Section 3.9, but
  items 3–4 show it cannot be canonical.

Files written: the claim and route above, and this note. Nothing committed.

## Referee (2026-09-16)

**What was checked.**
- I read the claim, the route and this note in full, plus the target's
  context (`bin/cairn context`). `git status` showed no unlisted solver files.
  `research/subshift-ring-flip-rigidity-from-cartan-uniqueness.md` belongs to
  another agent.
- I checked every step of the direct route line by line:
  - (M1)/(M2);
  - the derivative and derivation-killing argument of item 1;
  - the orbit-representation argument of item 2. This covers the shift
    identity `Uρ(a)U* = ρ(β(a))`, the WOT argument that `N^θ` is abelian, the
    inequivalence of the `σ_k` via invertibility of `m mod p`, the Schur
    off-diagonal step, and case (ii): `W^p ∈ C1` normalization, the unitary
    `V`, `N = Ψ(B(H))`, `θ∘Ψ = Ψ∘Ad W` (the wrap-around at `k = p−1` is
    consistent because `W^p = 1`) and `{W}' = ⊕ B(P_ζ H)`;
  - the trace argument that `O_2` has no finite-dimensional representations;
  - the closed-subgroup argument of item 3;
  - the naturality contradiction of item 4, which uses
    `Ad u∘α∘Ad u* = α` for `u = e^{ih}`, `h ∈ O_2^α`;
  - the eigenpart splitting of item 5.
- No gaps or hidden assumptions were found. Unitality of `O_2` is used and
  holds, and no separability, simplicity or outerness is needed.
- Duplicate search: `bin/cairn search --similar` and keyword searches for
  masa and fixed-point algebra found no duplicate. The `distinct_from`
  targets exist.
- Citations: I re-fetched arXiv API metadata for 2506.10902, 2607.18844,
  2605.30147, 2505.23168, 2607.16755 and 1312.6289. Titles, authors and dates
  match the note. I also completed the date-sorted arXiv search
  `abs:Cartan AND abs:UCT` that was rate-limited in the solver's session.
  Nothing newer than Komura (2026-07-21) came up, and nothing resolves the
  target.

**What was changed.**
- *Route, item 4, conjugation-closedness of outer SAI actions.* The solver
  had used a variant definition (honest unitaries `u_n ∈ O_2^α`). The
  argument is now written for Izumi's definition, as quoted in
  `ghs-z2-commuting-rokhlin-dimension-one-dual-sai-citation`: unitaries in
  `(O_2^α)_∞`. It uses `O_2^β = u O_2^α u*`, and the variant is kept as a
  remark. The conclusion is unchanged.
- *Claim, "Bearing" section.*
  - "Maximality is free" is now restricted to `p = 2`, since item 5 is not
    proved for `p = 3`.
  - "Makes precise the failure" was softened to "one precise form of" it.
    The node now says explicitly that non-equivariant choices along a
    specially chosen approximation are not ruled out.

**Verdict.** The route is sound as a complete direct proof, and I landed it
with the small fixes above. The result is elementary and folklore-level, and
the node correctly claims no priority. It is an obstruction only to canonical
or conjugation-natural choices of invariant Cartan subalgebras. It does not
touch existence, so the target stays OPEN. The dead-end remarks in Section 3
that rest on standard facts marked "not re-verified" (Renault cocycle
picture, `O_2`-absorption, Rokhlin models) remain unverified. They feed no
node.

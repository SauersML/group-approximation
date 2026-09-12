# Cantor hosts for SL_3(Z[t]): number-field local groups are excluded, and the cellular-automaton candidate lives on a product lattice

Lane `bh-full-cantor-ca-host`, swarm 6, 2026-09-12. Root:
`char-zero-linear-groups-satisfy-boone-higman`. Builds on
`research/artifacts/bh-char-zero-transcendental-2026-09-12.md`, Section 4.

**Outcome.** No finitely presented full Cantor host was built. Two obstructions
are established. Together they fix what the local maps of any eventually similar
host must carry, and the cellular-automaton candidate is placed against them.

## 1. `SL_3(Z[t])` is not linear over a number field

Node: `el3-of-infinite-rank-rings-not-linear-over-number-fields`, with route
`el3-infinite-rank-not-number-field-linear-proof`.
- **Statement.** For a finitely generated ring `R` with `R ⊗ Q`
  infinite-dimensional and `n >= 3`, no finite-index subgroup of `EL_n(R)` embeds
  in any `GL_N(Qbar)`.
- **Mechanism.** `E_12(q^2 m^2 a) = [E_13(q a)^m, E_32(q)^m]` gives word length
  `O(sqrt k)` for the `k`-th power of a root element. Sublinear growth puts every
  eigenvalue on the unit circle at every place of the field of definition. By
  Kronecker a bounded power of the element is unipotent. Logarithms then embed
  the infinite-rank group `E_12(e q^2 R)` in `M_N(K) ≅ Q^(N^2 [K:Q])`, which is
  impossible.
- **Why record it.** Zaremsky's `GL_n(Q)` theorem and restriction of scalars
  handle transcendence degree zero. This shows the transcendental inputs admit no
  abstract embedding into that setting. It is classical in shape, and no novelty
  is claimed.

## 2. Eventually similar hosts need non-number-field local groups

Node: `el3-z-t-embeds-in-no-host-with-number-field-local-groups`, with route
`el3-z-t-no-number-field-local-host-proof`. It requires Section 1,
`fw-subgroups-of-eventually-similar-groups-virtually-embed`,
`kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf`, and the (T) import
`elementary-groups-over-fg-rings-have-property-t`.
- **Excluded hosts.** A finite-index subgroup of `EL_n(R)` embeds in no eventually
  `H`-similar group on a shift of finite type whose vertex groups are linear over
  `Qbar`. This covers:
  - Higman--Thompson groups;
  - topological full groups of one-sided SFT groupoids (Matui);
  - `V_d(H)` for number-field-linear self-similar `H`, including Zaremsky's affine
    hosts.
- **Answer to the Matui question in the lane directive.** No action of
  `SL_3(Z[t])` lies in the topological full group of any one-sided SFT groupoid on
  a graph with out-degrees at least two. The elements of such a full group are
  canonical similarities on deep cones, and part 2 of the transfixing theorem
  makes FW subgroups finite.
- **The product groupoid (heuristic, not proved).** The product of a shift
  groupoid with the `p`-adic odometer groupoid is not evidently an SFT groupoid.
  After interleaving the two digit streams, asynchronous prefix replacement in
  one factor misaligns the interleaving, so Matui's finite presentation theorem
  does not obviously apply to its full group. Nothing in the graph uses this.

## 3. The cellular-automaton candidate

Action: `SL_3(Z[t^(+-1)])` on `Y = (Z_p^3)^Z`, with `t` acting as the shift.
- **Faithful.** A matrix `M` sends `e_i` placed at coordinate 0 to column `i`
  of `M`.
- **Cylinder images.** Let a rectangular cylinder fix `x_j` (mod `p^k`) for
  `j in [a,b]`, and `y_j`, `z_j` (mod `p^k`) for `j in [a',b']`. Now
  `E_12(t)(x,y,z)_j = (x_j + y_(j-1), y_j, z_j)`.
  - If `[a'+1, b'+1]` contains `[a,b]`, the image is a rectangular cylinder of the
    same shape with shifted constants, and the restricted map is again an affine
    Laurent map with the same linear part.
  - Otherwise the image couples `x'_j` with a free coordinate `y_(j-1)`, so it is
    a sheared clopen set rather than a rectangular cylinder. It still becomes
    rectangular after refining the `y`-window.

  `E_12(t^m)` needs the `y`-window to cover the `x`-window shifted by `m`. That
  depth depends on the element, which eventual similarity allows. So cylinder
  shapes give no obstruction.
- **Not a path space.** The natural refinements split one digit of one
  coordinate `j in Z` at a time, and those splittings commute. So the cylinders
  form a product lattice over infinitely many directions, not the cone tree of a
  finite graph. The candidate is therefore outside
  `el3-z-t-embeds-in-no-host-with-number-field-local-groups` as it stands. Whether
  some other coding makes it eventually similar on a shift of finite type is
  open.
- **What the local maps carry.** The restriction of a Laurent matrix to a cylinder
  is an affine Laurent map with the same linear part. So the local groupoid
  contains `EL_3(Z[t^(+-1)])`, which is not linear over `Qbar` by Section 1.
  That is consistent with Section 2: the candidate escapes the obstruction in both
  ways.
- **The directions.** In the `p`-adic direction each coordinate `j in Z` is its own
  digit stream, with bounded carries. So the natural full group is Brin--Thompson
  in shape with infinitely many directions. The known finite presentation
  theorems do not apply: Scott and Nekrashevych for `V_d(H)`, Matui for SFT
  groupoids, Brin and Hennig--Matucci for `nV`, and the type (A) criterion for
  twisted Brin--Thompson groups. Each needs finitely many directions or cone
  types.

## 4. Open target

Find a finitely presented group `D <= Homeo(C)`, full, containing standard `V`,
with a faithful copy of `SL_3(Z[t])`. By Section 2, if `D` is eventually similar
on a shift of finite type, its local vertex groups must include groups that are
not linear over any number field. By
`fp-full-binary-cantor-groups-have-type-a-actions`, such a `D` gives Boone--Higman
for `SL_3(Z[t])`.

Two directions not attempted here:
- a two-direction coding of `Y`, one shift direction and one digit direction,
  where the shift acts by a finite-memory transducer across coordinates. That is a
  2V-type full group with transducer local maps, and its finite presentation is
  open;
- abandoning cylinder cones for the coordinates of a non-SFT expanding system.

## 5. Verification record

- **Property (T) import.** Ershov--Jaikin-Zapirain, arXiv:0809.4095v2, fetched to
  MSI (`/scratch.global/sauer354/fcah/ejz.pdf`). The quoted theorem is in the
  citation node.
- **Imported, not re-read.** Suslin's `SL_n(Z[t]) = EL_n(Z[t])`; Matui's finite
  presentation theorem, used only as a description of the host family; Scott,
  Nekrashevych, Brin and Hennig--Matucci, cited only for scope.
- **Nekrashevych's theorem that contracting groups have no free subgroups.** It
  would exclude contracting `H` for this input, but it was not re-read, so it is
  not used in the graph.

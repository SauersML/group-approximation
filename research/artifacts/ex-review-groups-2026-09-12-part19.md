# EX review, groups: part 19. Labbé climbing layer: the supertile corner endomorphism and ball legality

Lane `ex-verify-groups`, 2026-09-13, ~03:15 CDT. Index: `ex-review-groups-2026-09-12.md`.

## 19.1 ex-fp-simple-relation-climbing: `labbe-full-group-embeds-in-its-supertile-corner` (e4bed01ee). PASS

- **Centered representations exist.** Start from the four-translate cover. If a coordinate leaves a block of
  side 1, move to the neighbouring block; the grid keeps the other coordinate consistent.
- **Uniqueness and continuity.** Uniqueness is recognizability. Continuity follows because the representation
  graph is compact.
- **Item 1.**
  - `A = {k = 0} = ω(Ω_U)` is clopen.
  - It is proper, via a letter whose image has shape `(2,2)`.
  - Full support gives `0 < μ(A) < 1`.
- **Item 2.**
  - `ω : Ω_U -> A` is a homeomorphism.
  - `L(x, w)` is the corner of the block `ω(x_w)` and satisfies the cocycle identity.
  - Surjectivity onto the arrows of `𝒢|_A` follows from uniqueness of the representation with `k = 0`.
- **Item 3.**
  - `Φ` conjugates by `ω` on `A` and is the identity off `A`. It is an injective homomorphism.
  - Its image is the set of elements fixing `Ω_U \ A` pointwise, since the inverse cocycle `w(x)` is continuous.
- **Item 4.** `D_A` is proper. Take `y ∉ A`: a 3-cycle on `U`, `σ^(e_1) U`, `σ^(2e_1) U` lies in `D([[𝒢]])`
  and moves `y`.
- **Not inner.** The node attributes this to `μ(A) < 1`. It also follows directly from properness of the image.

## 19.2 `labbe-ball-legality-is-pairwise-at-radii-two-to-seven` (6e6205bb2). PASS: exact computation, reproduced

- **Completeness, re-derived.**
  - Level-7 supertiles have side `>= 21 >= 2r + 1` for `r <= 7`. So a ball meets at most two columns and two rows
    of supertiles, and lies in `ω^7(Q)` for a legal `2 × 2` pattern `Q`.
  - A `2 × 2` window of `ω(P)` lies in `ω(Q)` for some `2 × 2` factor `Q` of `P`. So the closure seeded from the
    `2 × 2` factors of `ω^7(0)` contains those of every `ω^M(0)`, `M >= 7`. By minimality that is every legal
    `2 × 2` pattern.
  - The 50/50 seed agreement between `ω^7(0)` and `ω^9(0)` is a consistency check. Completeness does not need it.
- **Code read.** `labbe_lang.py` and `labbe_orders.py` implement the stated method:
  - the grid checks raise on any width or height mismatch;
  - Wang edge matching is tested on every image;
  - legal balls are the full `B(7)` windows inside `ω^7(Q)`, restricted to smaller radii;
  - compatibility is tested inside `B(R+3)`;
  - joins over sphere sites capture every candidate;
  - unions of pairs of sub-balls are tested first.
- **Reproduced once on MSI** (`/usr/bin/python3.11`, 2.4 s, `/scratch.global/sauer354/ex/ex-verify-groups/labbe/`).
  Every number in the node matches the output:
  - `|L_2x2| = 50` from both seeds, with all images valid;
  - `|L_(B(r))| = 19, 69, 152, 267, 413, 592, 804, 1047`;
  - compatible translates exist for `R = 0, 1, 2` and none for `R = 3, 4`, so the minimal `R_1` is 3;
  - hidden illegal counts are `54, 34, 59, 14, 86, 15`, and the legal candidates equal `|L_(B(r+1))|`;
  - every hidden illegal pattern has order 2.
- **Trust surface.** The transcription of Labbé's tile list and of `α, β, γ` from `for_article1.sage`.
  - Every computed image passes edge matching and the grid checks.
  - A reflection or transpose convention error would change none of the counts, because `ℓ^1` balls and the
    translation set `|g|_1 <= 3` are dihedrally symmetric.
- **Scope.** Only radii 2–7, as the node records. Test (T1) at larger offsets is open.

## 19.3 Status

- **Monitor.** No new landings from my lanes since a9db5ed677 (02:34).
- **Open.** `labbe-full-group-local-relations-climb` and `labbe-shift-derived-full-group-is-finitely-presented`.

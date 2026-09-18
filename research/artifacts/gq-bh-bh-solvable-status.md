# Boone--Higman for soluble groups: status on main (lane bh-solvable, 2026-09-18)

Read from node texts on `origin/main`. "Reviewed" means the node records an
independent PASS in the repo. Nothing here is refereed externally.

## 1. The three questions asked

1. **All finitely generated metabelian groups: YES, in `B_A`.**
   - `fp-metabelian-groups-satisfy-boone-higman` is ESTABLISHED and reviewed PASS
     (`review-metabelian-bh-2026-09-13.md`). Its route
     `fp-metabelian-bh-via-quasi-linear-pbh` works for every *finitely generated*
     metabelian group: Wehrfritz, CJM 27 (1975), Cor. 1.2 (quasi-linearity), then
     `quasi-linear-groups-satisfy-permutational-boone-higman` (reviewed PASS).
   - This settles BBMZ Problem 5.3(7) (finitely presented metabelian groups) and more.
2. **Center-by-metabelian: OPEN.**
   - `free-centre-by-metabelian-groups-satisfy-boone-higman` (OPEN) is the first
     uncovered named case: `F_r/[F_r'', F_r]`.
   - General finitely generated center-by-metabelian groups can have unsolvable word
     problem, so only those with solvable word problem are Boone--Higman instances.
     For derived length three, BBMZ footnote 9 cites a failure of solvable word
     problem, as quoted in `free-solvable-groups-satisfy-permutational-boone-higman`.
3. **Finitely generated soluble groups of derived length 3 with solvable word problem:
   OPEN in general.** Covered subclasses on main:
   - quasi-linear ones (`quasi-linear-groups-satisfy-permutational-boone-higman`);
   - free soluble groups of every derived length and their subgroups
     (`free-solvable-groups-satisfy-permutational-boone-higman`, lane proof);
   - **new:** residually finite ones of finite rank, of any derived length (below).

## 2. New landing

- `rf-soluble-finite-rank-groups-are-char-zero-linear`:
  Pyber--Segal, arXiv:0711.0687, Theorem 1.1 (fg RF virtually soluble: PIG ⟺ finite
  rank) and Corollary 1.3 (fg residually finite-soluble with PIG ⟹ linear in
  characteristic 0), read in the TeX. Induction handles the virtually soluble case.
- `rf-soluble-minimax-groups-satisfy-permutational-bh`
  with its `-proof` route: such groups are linear over a field of characteristic 0,
  hence in `B_A` by the reviewed quasi-linear node. No priority is claimed: this is a
  direct corollary and may be folklore.
- `fg-soluble-minimax-groups-satisfy-boone-higman` (OPEN): the non-residually-finite
  case, with Abels' quotient `A_p/⟨e_14(1)⟩` as the calibration. It is a unit group of a
  generalized triangular ring with a `Z[1/p]/Z` corner. No `B_A` producer on main
  applies, because all are residually finite.

## 3. What was checked against Zaremsky

Zaremsky, arXiv:2405.09722 (abstract read): every finitely presented self-similar group
embeds in a finitely presented simple group, and every finitely generated subgroup of
`GL_n(Q)` satisfies Boone--Higman. Pyber--Segal give linearity over *some*
characteristic-0 field, not `Q`. So the landing uses the repository's
characteristic-zero and quasi-linear nodes, not Zaremsky's `GL_n(Q)` corollary
directly.

## 4. Sharpest open items for soluble groups

1. `free-centre-by-metabelian-groups-satisfy-boone-higman`.
2. `fg-soluble-minimax-groups-satisfy-boone-higman`, the non-residually-finite part:
   quotients of linear groups by infinite central subgroups.
3. Finitely generated abelian-by-polycyclic groups. They are residually finite
   (Jategaonkar, Roseblade; not read), but Wehrfritz's faithful-representation theorem
   for them is over *division rings* (QJM 35 (1984); title only via Crossref). So
   quasi-linearity over fields is not available on main, and no node covers them.

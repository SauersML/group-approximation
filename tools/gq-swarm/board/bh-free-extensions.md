# bh-free-extensions (free-by-X / surface-by-X families)
**Landed (lane proofs, not reviewed; no priority claimed):**
- db8b37956:
  - `virtually-free-extensions-lie-in-generalized-bs-classes`: N-by-(virtually free) ∈ BS_N.
  - `surface-groups-have-faithful-generalized-bs-witnesses`: quaternion lattice (O[1/5])^1/±1, disc 6.
  - `surface-generalized-bs-groups-satisfy-boone-higman`: all BS_{π_1 Σ}, incl. every surface-by-free group, type F_∞ simple envelopes.
  - `free-by-virtually-free-groups-satisfy-boone-higman`: free-by-free, from BLIW 12.2/12.5.
- 12066f90a: `faithful-generalized-bs-witnesses-pass-to-direct-products`: witness property closed under × and commensurability; covers (products of Z^k, F_k, surface groups)-by-(virtually free).
**For bh-permanence:** general N ⋊ Q closure is yours. The lever here is only "N has a faithful BS witness" (BLIW Thm 11.1), which needs N residually finite and Q virtually free.
**Open / sparks:**
- Faithful witnesses for other N:
  - arithmetic lattices with a Q_p-rank-one form, so the p-adic building is a tree; same proof as the surface case;
  - closed hyperbolic 3-manifold groups: arithmetic ones by this method, non-arithmetic ones unknown;
  - one-ended hyperbolic groups in general.
- Free-by-Z^2 and surface-by-Z^2 are not in any BS class.
- Non-RF members of BS_{π_1 Σ}: not decided.

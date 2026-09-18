---
rg: 2
id: fg-semiprime-pi-q-algebras-embed-in-fp-simple-rings
kind: claim
title: Every finitely generated semiprime PI Q-algebra, in particular every semiprime one of GK dimension at most one, embeds in a simple ring finitely presented over Z
distinct_from:
  char-zero-representable-rings-embed-in-fp-simple-rings: that is the input class of subrings of M_D(C ⊗ Q<x>); this identifies a ring-theoretic class inside it, the semiprime PI algebras, which are shown to be representable over finitely generated commutative Q-algebras.
  char-zero-ring-boone-higman: that is every finitely generated decidable Q-algebra; this settles its semiprime PI part, including the semiprime part of GK dimension at most one.
  algebra-boone-higman-conjecture: that is the conjecture over every computable field; this is a special class at K = Q, with finite presentation even over Z.
---

**ESTABLISHED** through `fg-semiprime-pi-q-algebras-embed-in-fp-simple-rings-proof` (lane
proof from classical PI theory, not independently reviewed; referee requests sent). No
novelty is claimed for the representability step, which is classical. The new input is the
host, from `char-zero-representable-rings-embed-in-fp-simple-rings`.

**Statement.** Let `A` be a finitely generated `Q`-algebra that satisfies a polynomial
identity and is semiprime, meaning it has no nonzero nilpotent ideal. Then:
1. `A` embeds unitally in `M_N(C_0)` for some `N` and some finitely generated commutative
   `Q`-algebra `C_0`;
2. hence `A` embeds in a simple ring that is finitely presented as a ring (over `Z`).

**Covered classes.**
- **Prime PI algebras.** Every finitely generated prime PI `Q`-algebra.
- **GK dimension at most one.** Every finitely generated semiprime `Q`-algebra of
  Gelfand--Kirillov dimension at most `1`. By Small--Stafford--Warfield, *Affine algebras of
  Gelfand--Kirillov dimension one are PI*, Math. Proc. Cambridge Philos. Soc. 97 (1985),
  407--414, such an algebra is PI. The statement comes from secondary summaries and was
  not re-read at the source. GK dimension `0` means finite-dimensional, which is trivial.
- **Consequence for the conjecture.** It follows that `char-zero-ring-boone-higman`, and so
  the case `K = Q` of `algebra-boone-higman-conjecture`, holds for all these inputs.

**What is not covered.**
- *Non-semiprime PI algebras.* Finitely generated PI algebras need not be representable,
  and this route needs representability.
- *Noetherian case.* A literature lead for this case is Anan'in's theorem (Arch. Math.,
  1992): a finitely generated right Noetherian PI algebra over a field is representable.
  Its exact hypotheses were not checked, and that theorem is not used here.
- *GK dimension one.* It is open here whether every finitely generated `Q`-algebra of GK
  dimension `1` is representable. The example `Q<x,y>/(yx, y^2)` is not right Noetherian
  but is representable: `x ↦ diag(t, 0)` and `y ↦ e_12` over `Q[t]`.

# Boone–Higman for Artin groups: status map and new classes, 2026-09-12

Lane `bh-artin-solvable-wp`. Target: item (13) of Problem 5.3 in
Belk–Bleak–Matucci–Zaremsky, "Artin groups with solvable word problem". Sources
were fetched on MSI into `/scratch.global/sauer354/bh-artin` and extracted to
text with pypdf. Quotes below are verbatim up to the extractor's spacing.

## 1. Sources read

| Source | Version | Read for |
|---|---|---|
| Belk–Fournier-Facio–Hyde–Zaremsky (BFFHZ), arXiv:2503.21882 | v2, 16 Apr 2025 | Corollary B, the open-types sentence after it, proof of Corollary B (§4) |
| Belk–Bleak–Matucci–Zaremsky, *Progress around the Boone–Higman Conjecture*, arXiv:2306.16356 | v3 | Problem 5.3(13), footnote 10, Remark 5.4 |
| Bux–Llosa Isenrich–Wu (BLIW), arXiv:2408.05673 | v2 | Theorem 12.5, Remark 12.7, Corollary 12.8 |
| D. Allcock, *Braid pictures for Artin groups*, arXiv:math/9907194 | v1, 30 Jul 1999 | abstract, Table 1.1, Theorem 3.1, §4 |
| L. Paris, *Braid groups and Artin groups*, arXiv:0711.2372 | v1 | §6 (Corollary 6.5 and the surrounding notes), §7.1 |
| K. Jankiewicz, *Residual finiteness of certain 2-dimensional Artin groups*, arXiv:2006.04717 | v2 | Theorem B, Definition 4.2, Theorem 4.3, Corollary 4.13, Example 4.14 |
| K. Jankiewicz, *Splittings of triangle Artin groups*, arXiv:2103.01343 | v1 | abstract, Theorem A |
| J. Flechsig, *Braid groups and mapping class groups for 2-orbifolds*, arXiv:2305.04273 | v1 | abstract, introduction |
| L. Li, S. K. Roushon, arXiv:2403.09533 | v2 | abstract (type B̃_n virtually poly-free) |
| arXiv API, `abs:"Boone-Higman"` | 12 Sep 2026 | 14 hits, newest arXiv:2609.01868; none treats Artin groups beyond BFFHZ and BLIW |

## 2. What the literature settles

**BFFHZ, Corollary B:** "Artin groups of types Bn = Cn, Dn, I2(m), and ~An, for
all n (braid groups are Artin groups of type An)." The next sentence: "For
spherical and Euclidean Artin groups, the Boone–Higman conjecture remains open
for the exceptional type spherical Artin groups, and the Euclidean Artin groups
other than type ~An; in rank 3 it is also known for type ~C2 and ~G2 (and ~A2,
which we recover) [BLIW]."

**BFFHZ, proof of Corollary B (§4):**
- Braid groups satisfy PBH through "embeddings Bn → LB n → LB ext n → Aut(Fn)".
- "those of type Bn = Cn are the 'annular braid groups', i.e., the mapping
  class groups of punctured annuli, and the Artin groups of type ~An embed into
  these [KP02]."
- "The Artin groups of type Dn embed into the mapping class groups of certain
  finite type surfaces with nonempty boundary [PV92, Theorem 1]."
- "the Artin groups of type I2(m) are all commensurable to the braid group on
  three strands [CP22, Theorem 5] and thus satisfy PBH [Zarb, Proposition 5.6]."

**Survey, Remark 5.4:** "item (13) remains open for many classes of Artin
groups, including those of exceptional spherical type and those of Euclidean
type other than the ~An and triangle cases (~C2 and ~G2)."

**Survey, footnote 10:** "It is an open question whether all Artin groups have
solvable word problem [45, Problem 10], but this is known for several large
classes, such as right-angled Artin groups (see Theorem 5.1) and Artin groups of
spherical [54] or Euclidean [85] type."

**BLIW:**
- "Squier proved in [Squ87] that all the Euclidean triangle Artin groups also
  lie in BS F2, hence we have the following: Corollary 12.8. All Euclidean
  triangle Artin groups embed in finitely presented simple groups of type F∞."
- Remark 12.7: "for every group in BS Fk the permutational Boone–Higman
  Conjecture holds".

**Survey, Theorem 5.1(3):** right-angled Artin groups.

## 3. New in this lane: type C̃_n

**Allcock, Table 1.1, row C̃_n:** "˜Cn 2 punctures 1 n > 1". The caption says
that for each row the Artin group "is a normal subgroup of the n-strand braid
group of the orbifold which is the plane equipped with the given features", with
quotient given in the third column. For C̃_n that quotient is trivial.

**Allcock, §4, the diagram C̃_n:**
- "W is the group Zn : 2n : Sn".
- "V0 = { (x1, . . . , xn) ∈ Cn | xj ± xk /∈ Z for j ⁄= k and xj /∈ 1/2 Z for
  all j }".
- "this identifies V0/ (Zn : 2n) with the pure braid space of C − {0, 1/2}".

§4 opens with "The Artin group itself is the fundamental group of the quotient
of V0 by the Weyl group". For affine Weyl groups this is Nguyễn Viết Dũng,
*The fundamental groups of the spaces of regular orbits of the affine Weyl
groups*, Topology 22 (1983) 425–435 (Allcock's [10], used in his Theorem 3.1).

**Check of the identification.**
- **The quotient.** `Z^n : 2^n` acts coordinatewise through the infinite
  dihedral group `<x ↦ x+1, x ↦ -x>`. It acts freely on `C - ½Z`. The quotient
  map `x ↦ e^{2πix} + e^{-2πix}` identifies `(C - ½Z)/D_∞` with `C - {2, -2}`.
- **The conditions.** Two coordinates satisfy `x_j ± x_k ∉ Z` exactly when
  their images differ.
- **Result.** `V0/W` is the unordered configuration space of `n` points in the
  twice-punctured plane.

**Embedding.** With that identification, the Fadell–Neuwirth fibration puts
`A(C̃_n)` inside the braid group `B_(n+2)`:
- the fibration `Conf_(n+2)(C)/S_n → Conf_2(C)` has fibre `UConf_n(C - 2 pts)`;
- its base is aspherical, so the fibre's fundamental group injects;
- the total space finitely covers `UConf_(n+2)(C)`.

Braid groups satisfy PBH (BFFHZ). So every `A(C̃_n)` satisfies PBH and embeds in
a finitely presented simple group. Nodes:
- `c-tilde-artin-groups-are-punctured-plane-braid-groups` (import);
- `c-tilde-artin-groups-satisfy-permutational-boone-higman` (derivation).

**Priority.** BFFHZ v2 and survey v3 both list the Euclidean types other than
Ã_n, C̃_2 and G̃_2 as open, which includes C̃_n for n ≥ 3. The bounded search
in §1 found nothing later. All inputs are older published or arXiv results, and
the combination is short. No priority is claimed beyond that search.

## 4. Status by type after this lane

| Type | Status | Source |
|---|---|---|
| A_n, B_n = C_n, D_n, I_2(m) | PBH | BFFHZ Cor. B |
| Ã_n | PBH | BFFHZ Cor. B (Kent–Peifer) |
| C̃_n, all n | PBH | this lane |
| Ã_2, C̃_2, G̃_2 (Euclidean triangles) | PBH | BLIW Cor. 12.8, Remark 12.7 |
| right-angled | BH | survey Thm 5.1(3) |
| E_6, E_7, E_8 | open | all spherical types reduce to these three, in PBH form (`spherical-artin-boone-higman-reduces-to-e6-e7-e8`) |
| F_4, H_3, H_4 | open as stated by BFFHZ | covered by that reduction once E_6–E_8 are done |
| B̃_n (n ≥ 3), D̃_n (n ≥ 4), F̃_4, Ẽ_6, Ẽ_7, Ẽ_8 | open | |
| large type, 2-dimensional, FC | open | §5 |

## 5. Where the methods stop

1. **Orbifold cone points.**
   - Allcock realizes B̃_n with index 2 in the braid group of the plane with one
     puncture and one cone point of order 2, and D̃_n with index 4 in the braid
     group of the plane with two cone points (Table 1.1).
   - The Fadell–Neuwirth argument needs punctures. A braid around a cone point
     has finite order (Flechsig, introduction), so orbifold braid groups are not
     subgroups of ordinary braid groups in the obvious way.
   - Flechsig also corrects a theorem of Roushon on pure orbifold braid groups
     ("This corrects Theorem 2.14 in [12]"). Any use of orbifold braid groups
     needs that correction.
2. **Geometric monodromy.** Paris §7.1: "the representation ρPV is faithful if
   and only if either Γ = An for some n≥ 1, or Γ = Dn for some n≥ 4". So the
   E types are not reached through mapping class groups this way.
3. **Linearity.**
   - Paris, Corollary 6.5: the LKB representation over "K = Q(x,y)" is
     injective for spherical types. It is defined for small type without
     triangle, which covers A_n, D_n, E_k.
   - Paris says "any spherical type Artin group embeds in a direct product of
     Artin groups of type An (n≥ 1), Dn (n≥ 4), and Ek (k = 6, 7, 8) (see
     [57])". So spherical Artin groups are finitely generated linear groups over
     a field of transcendence degree 2.
   - That lands them in the open root `char-zero-linear-groups-satisfy-boone-higman`,
     beyond Zaremsky's `GL_n(Q)` theorem.
4. **Locally finite trees.**
   - BLIW's theorems need finite-index edge groups. Squier's splittings have
     them for the Euclidean triangles.
   - Jankiewicz, Theorem 4.3: under an admissible partial orientation,
     "ArtΓ splits as a free product with amalgamation A∗C B where A,B,C are
     finite rank free groups. Moreover, rk A =|E(Γ)|, rkB = 1−|V (Γ)| + 2|E(Γ)|,
     and C is an index 2 subgroup of B".
   - For a large-type triangle this gives F_3 ∗_(F_7) F_4 (Corollary 4.13). A
     subgroup of rank 7 in F_3 has finite index only if the index is 3.
     Jankiewicz states a degree-3 covering only for (3,3,3) (Example 4.14). For
     the other triples finite index in A is not established, and BLIW does not
     apply as it stands.
   - Every f.g. subgroup of a free group has decidable membership (Stallings).
     So these splittings reduce the admissibly oriented Artin groups to
     Boone–Higman permanence under HNN extensions over f.g. free edges,
     `bh-embeddability-survives-decidable-edge-hnn` (via `A ∗_C B <= (A ∗ B)∗_C`).

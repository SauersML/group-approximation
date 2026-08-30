import GroupApproximation.Sofic.LiteralP13HodgeReplay

/-!
# Sparse support-pair fibers for the exact P13 certificate

The explicit list is only a fast representation of the replayed
product-class table.  Each fiber is proved equal to the definitional
filter below, so no generated equality is trusted.
-/

namespace GroupApproximation
namespace LiteralP13HodgePairTable

open LiteralP13HodgeReplay
open scoped BigOperators

/-- Read an exact finite table; the length proof rules out defaults. -/
private def exactTable {A : Type*} {n : ℕ} (entries : List A)
    (h : entries.length = n) : Fin n → A :=
  fun i ↦ entries.get (h ▸ i)

private def classPairListChunk0 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(1, 16)],
  [(1, 17)],
  [(2, 8)],
  [(1, 20)],
  [(1, 21)],
  [(1, 19)],
  [(1, 15)],
  [(1, 18)],
] (by decide)

private def classPairListChunk1 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(1, 10)],
  [(1, 11)],
  [(0, 20), (1, 12), (2, 4), (5, 3), (6, 0)],
  [(0, 21), (1, 13)],
  [(1, 14)],
  [(21, 3)],
  [(4, 16), (20, 3)],
  [(4, 17)],
] (by decide)

private def classPairListChunk2 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(1, 7)],
  [(1, 9)],
  [(0, 19), (19, 0)],
  [(0, 18), (18, 0)],
  [(0, 16), (2, 20), (8, 0)],
  [(2, 21)],
  [(0, 17)],
  [(0, 15), (15, 0)],
] (by decide)

private def classPairListChunk3 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(0, 10), (10, 0)],
  [(0, 11), (11, 0)],
  [(0, 12), (1, 6), (2, 5), (3, 4), (4, 3), (5, 2), (6, 1), (12, 0)],
  [(0, 13), (13, 0)],
  [(0, 14), (14, 0)],
  [(0, 9), (9, 0)],
  [(21, 2)],
  [(0, 8), (16, 0), (20, 2)],
] (by decide)

private def classPairListChunk4 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(17, 0)],
  [(0, 7), (7, 0)],
  [(2, 18)],
  [(2, 9)],
  [(19, 1)],
  [(18, 1)],
  [(2, 19)],
  [(2, 10)],
] (by decide)

private def classPairListChunk5 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(2, 11)],
  [(1, 3), (2, 12), (3, 8), (5, 0), (6, 4), (8, 1)],
  [(2, 13)],
  [(2, 14)],
  [(15, 1)],
  [(10, 1)],
  [(11, 1)],
  [(0, 6), (3, 5), (4, 2), (12, 1), (20, 0)],
] (by decide)

private def classPairListChunk6 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(13, 1), (21, 0)],
  [(14, 1)],
  [(9, 1)],
  [(16, 1)],
  [(17, 1)],
  [(2, 15)],
  [(2, 7)],
  [(7, 1)],
] (by decide)

private def classPairListChunk7 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(1, 2), (2, 6), (5, 1), (6, 5)],
  [(20, 1)],
  [(21, 1)],
  [(19, 2)],
  [(18, 2)],
  [(19, 3)],
  [(4, 15), (18, 3)],
  [(4, 19)],
] (by decide)

private def classPairListChunk8 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(8, 2)],
  [(15, 2)],
  [(13, 2)],
  [(10, 2)],
  [(0, 5), (1, 8), (3, 1), (4, 6), (8, 3), (12, 2)],
  [(14, 2)],
  [(11, 2)],
  [(9, 2)],
] (by decide)

private def classPairListChunk9 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(4, 7), (15, 3)],
  [(4, 10), (13, 3)],
  [(4, 11), (10, 3)],
  [(0, 4), (3, 0), (4, 12), (5, 16), (12, 3), (16, 2)],
  [(4, 13), (14, 3), (17, 2)],
  [(4, 14), (5, 17), (11, 3)],
  [(4, 18), (9, 3)],
  [(21, 16)],
] (by decide)

private def classPairListChunk10 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(21, 17)],
  [(4, 20), (16, 3), (20, 16)],
  [(4, 21), (17, 3)],
  [(20, 17)],
  [(7, 2)],
  [(4, 9), (7, 3)],
  [(19, 14)],
  [(19, 17)],
] (by decide)

private def classPairListChunk11 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(18, 14)],
  [(18, 17)],
  [(7, 10)],
  [(19, 4)],
  [(3, 9), (18, 4)],
  [(19, 5)],
  [(18, 5)],
  [(17, 4)],
] (by decide)

private def classPairListChunk12 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(3, 20), (16, 4)],
  [(3, 21)],
  [(3, 18), (15, 4)],
  [(3, 10), (11, 4)],
  [(3, 11), (14, 4), (17, 5)],
  [(0, 3), (2, 16), (3, 12), (4, 0), (12, 4), (16, 5)],
  [(3, 13), (10, 4)],
  [(2, 17), (3, 14), (13, 4)],
] (by decide)

private def classPairListChunk13 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(3, 7), (9, 4)],
  [(15, 5)],
  [(11, 5)],
  [(14, 5)],
  [(0, 2), (3, 6), (4, 1), (6, 8), (8, 4), (12, 5)],
  [(10, 5)],
  [(13, 5)],
  [(9, 5)],
] (by decide)

private def classPairListChunk14 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(8, 5)],
  [(3, 19)],
  [(3, 15), (7, 4)],
  [(7, 5)],
  [(21, 6)],
  [(20, 6)],
  [(1, 5), (2, 1), (5, 6), (6, 2)],
  [(19, 13)],
] (by decide)

private def classPairListChunk15 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(19, 6)],
  [(21, 7)],
  [(18, 6), (20, 7)],
  [(18, 13)],
  [(21, 15)],
  [(20, 15)],
  [(5, 7)],
  [(5, 15)],
] (by decide)

private def classPairListChunk16 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(17, 6)],
  [(16, 6)],
  [(15, 6)],
  [(21, 10)],
  [(20, 10)],
  [(14, 6)],
  [(21, 11)],
  [(13, 6), (20, 11), (21, 12)],
] (by decide)

private def classPairListChunk17 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(0, 1), (3, 2), (4, 5), (12, 6), (20, 12), (21, 13)],
  [(11, 6), (20, 13)],
  [(10, 6), (21, 14)],
  [(20, 14)],
  [(21, 19)],
  [(9, 6), (20, 19)],
  [(5, 10)],
  [(5, 11)],
] (by decide)

private def classPairListChunk18 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(1, 4), (2, 0), (4, 8), (5, 12), (6, 3), (8, 6)],
  [(5, 13)],
  [(5, 14)],
  [(5, 19)],
  [(21, 9)],
  [(20, 9)],
  [(7, 11), (21, 18)],
  [(7, 6), (20, 18)],
] (by decide)

private def classPairListChunk19 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(5, 9)],
  [(5, 18)],
  [(19, 7)],
  [(18, 7)],
  [(19, 8)],
  [(18, 8)],
  [(17, 7)],
  [(16, 7)],
] (by decide)

private def classPairListChunk20 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(19, 21)],
  [(19, 9)],
  [(15, 7), (18, 9), (19, 12)],
  [(14, 7)],
  [(13, 7)],
  [(12, 7), (18, 12), (19, 15)],
  [(11, 7), (18, 21)],
  [(10, 7)],
] (by decide)

private def classPairListChunk21 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(9, 7), (18, 15)],
  [(8, 7), (19, 16)],
  [(18, 16)],
  [(17, 8)],
  [(16, 8)],
  [(17, 9)],
  [(15, 8), (16, 9)],
  [(15, 14)],
] (by decide)

private def classPairListChunk22 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(17, 10)],
  [(17, 11)],
  [(14, 8), (16, 10), (17, 12)],
  [(11, 8), (17, 13)],
  [(16, 11)],
  [(12, 8), (16, 12), (17, 14), (20, 5)],
  [(16, 13)],
  [(13, 8), (21, 5)],
] (by decide)

private def classPairListChunk23 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(10, 8), (16, 14)],
  [(9, 10), (17, 15)],
  [(9, 8), (16, 15)],
  [(15, 13)],
  [(9, 11)],
  [(15, 9)],
  [(14, 9)],
  [(13, 9)],
] (by decide)

private def classPairListChunk24 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(12, 9), (15, 12), (19, 18)],
  [(11, 9)],
  [(10, 9), (15, 17)],
  [(14, 10)],
  [(13, 10), (14, 11)],
  [(12, 10), (14, 12), (17, 16)],
  [(11, 10), (14, 13)],
  [(13, 11)],
] (by decide)

private def classPairListChunk25 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(12, 11), (13, 12), (21, 20)],
  [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 16), (17, 17), (18, 18), (19, 19), (20, 20), (21, 21)],
  [(11, 12), (12, 13), (20, 21)],
  [(11, 13)],
  [(10, 11), (13, 14)],
  [(10, 12), (12, 14), (16, 17)],
  [(10, 13), (11, 14)],
  [(10, 14)],
] (by decide)

private def classPairListChunk26 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(14, 15)],
  [(13, 15)],
  [(9, 12), (12, 15), (18, 19)],
  [(11, 15)],
  [(10, 15)],
  [(9, 15)],
  [(15, 11)],
  [(9, 13)],
] (by decide)

private def classPairListChunk27 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(15, 10)],
  [(8, 9), (15, 16)],
  [(13, 16)],
  [(8, 10), (14, 16)],
  [(8, 11), (13, 17)],
  [(5, 20), (8, 12), (12, 16), (14, 17)],
  [(5, 21), (8, 13)],
  [(8, 14), (10, 16), (12, 17)],
] (by decide)

private def classPairListChunk28 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(11, 16)],
  [(10, 17)],
  [(11, 17)],
  [(8, 15), (9, 16)],
  [(9, 14)],
  [(8, 16)],
  [(8, 17)],
  [(9, 17)],
] (by decide)

private def classPairListChunk29 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(17, 18)],
  [(16, 18)],
  [(17, 19)],
  [(7, 8), (16, 19)],
  [(7, 9), (15, 18)],
  [(14, 18)],
  [(13, 18)],
  [(7, 12), (12, 18), (15, 19)],
] (by decide)

private def classPairListChunk30 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(11, 18)],
  [(10, 18)],
  [(14, 19)],
  [(13, 19)],
  [(7, 15), (9, 18), (12, 19)],
  [(11, 19)],
  [(10, 19)],
  [(9, 19)],
] (by decide)

private def classPairListChunk31 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(7, 16)],
  [(8, 18)],
  [(8, 19)],
  [(7, 18)],
  [(7, 19)],
  [(6, 9), (19, 20)],
  [(18, 11)],
  [(6, 7), (18, 20)],
] (by decide)

private def classPairListChunk32 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(19, 11)],
  [(17, 20)],
  [(17, 21)],
  [(3, 16), (16, 20), (20, 4)],
  [(16, 21)],
  [(3, 17), (21, 4)],
  [(15, 21)],
  [(15, 20)],
] (by decide)

private def classPairListChunk33 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(14, 20)],
  [(6, 10), (14, 21)],
  [(6, 11), (13, 20)],
  [(1, 0), (2, 3), (5, 4), (6, 12), (12, 20), (13, 21)],
  [(6, 13), (11, 20), (12, 21)],
  [(11, 21)],
  [(6, 14)],
  [(10, 20)],
] (by decide)

private def classPairListChunk34 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(10, 21)],
  [(9, 20)],
  [(9, 21)],
  [(8, 20)],
  [(8, 21)],
  [(6, 18), (7, 20)],
  [(7, 13)],
  [(6, 15)],
] (by decide)

private def classPairListChunk35 : Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  [(6, 19)],
  [(6, 20)],
  [(6, 21)],
  [(7, 21)],
  [(20, 8)],
  [(21, 8)],
  [(5, 8)],
  [(18, 10)],
] (by decide)

private def classPairListChunks : Fin 36 → Fin 8 → List (Fin 22 × Fin 22) := exactTable [
  classPairListChunk0,
  classPairListChunk1,
  classPairListChunk2,
  classPairListChunk3,
  classPairListChunk4,
  classPairListChunk5,
  classPairListChunk6,
  classPairListChunk7,
  classPairListChunk8,
  classPairListChunk9,
  classPairListChunk10,
  classPairListChunk11,
  classPairListChunk12,
  classPairListChunk13,
  classPairListChunk14,
  classPairListChunk15,
  classPairListChunk16,
  classPairListChunk17,
  classPairListChunk18,
  classPairListChunk19,
  classPairListChunk20,
  classPairListChunk21,
  classPairListChunk22,
  classPairListChunk23,
  classPairListChunk24,
  classPairListChunk25,
  classPairListChunk26,
  classPairListChunk27,
  classPairListChunk28,
  classPairListChunk29,
  classPairListChunk30,
  classPairListChunk31,
  classPairListChunk32,
  classPairListChunk33,
  classPairListChunk34,
  classPairListChunk35,
] (by decide)

private def classPairListFinal : Fin 5 → List (Fin 22 × Fin 22) := exactTable [
  [(19, 10)],
  [(7, 14)],
  [(7, 17)],
  [(6, 16)],
  [(6, 17)],
] (by decide)

/-- Sparse support-pair list for one coefficient class. -/
def classPairList (c : Fin 293) : List (Fin 22 × Fin 22) :=
  if h : c.1 < 288 then
    classPairListChunks ⟨c.1 / 8, by lia⟩ ⟨c.1 % 8, Nat.mod_lt _ (by lia)⟩
  else
    classPairListFinal ⟨c.1 - 288, by lia⟩

/-- Finset form of the sparse fiber. -/
def classPairs (c : Fin 293) : Finset (Fin 22 × Fin 22) :=
  (classPairList c).toFinset

/-- Every pair stored in sparse fiber 0 has class 0. -/
private theorem classPairList_sound_0 :
    (classPairList 0).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 0) := by
  decide

/-- Every pair stored in sparse fiber 1 has class 1. -/
private theorem classPairList_sound_1 :
    (classPairList 1).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 1) := by
  decide

/-- Every pair stored in sparse fiber 2 has class 2. -/
private theorem classPairList_sound_2 :
    (classPairList 2).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 2) := by
  decide

/-- Every pair stored in sparse fiber 3 has class 3. -/
private theorem classPairList_sound_3 :
    (classPairList 3).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 3) := by
  decide

/-- Every pair stored in sparse fiber 4 has class 4. -/
private theorem classPairList_sound_4 :
    (classPairList 4).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 4) := by
  decide

/-- Every pair stored in sparse fiber 5 has class 5. -/
private theorem classPairList_sound_5 :
    (classPairList 5).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 5) := by
  decide

/-- Every pair stored in sparse fiber 6 has class 6. -/
private theorem classPairList_sound_6 :
    (classPairList 6).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 6) := by
  decide

/-- Every pair stored in sparse fiber 7 has class 7. -/
private theorem classPairList_sound_7 :
    (classPairList 7).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 7) := by
  decide

/-- Every pair stored in sparse fiber 8 has class 8. -/
private theorem classPairList_sound_8 :
    (classPairList 8).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 8) := by
  decide

/-- Every pair stored in sparse fiber 9 has class 9. -/
private theorem classPairList_sound_9 :
    (classPairList 9).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 9) := by
  decide

/-- Every pair stored in sparse fiber 10 has class 10. -/
private theorem classPairList_sound_10 :
    (classPairList 10).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 10) := by
  decide

/-- Every pair stored in sparse fiber 11 has class 11. -/
private theorem classPairList_sound_11 :
    (classPairList 11).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 11) := by
  decide

/-- Every pair stored in sparse fiber 12 has class 12. -/
private theorem classPairList_sound_12 :
    (classPairList 12).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 12) := by
  decide

/-- Every pair stored in sparse fiber 13 has class 13. -/
private theorem classPairList_sound_13 :
    (classPairList 13).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 13) := by
  decide

/-- Every pair stored in sparse fiber 14 has class 14. -/
private theorem classPairList_sound_14 :
    (classPairList 14).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 14) := by
  decide

/-- Every pair stored in sparse fiber 15 has class 15. -/
private theorem classPairList_sound_15 :
    (classPairList 15).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 15) := by
  decide

/-- Every pair stored in sparse fiber 16 has class 16. -/
private theorem classPairList_sound_16 :
    (classPairList 16).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 16) := by
  decide

/-- Every pair stored in sparse fiber 17 has class 17. -/
private theorem classPairList_sound_17 :
    (classPairList 17).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 17) := by
  decide

/-- Every pair stored in sparse fiber 18 has class 18. -/
private theorem classPairList_sound_18 :
    (classPairList 18).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 18) := by
  decide

/-- Every pair stored in sparse fiber 19 has class 19. -/
private theorem classPairList_sound_19 :
    (classPairList 19).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 19) := by
  decide

/-- Every pair stored in sparse fiber 20 has class 20. -/
private theorem classPairList_sound_20 :
    (classPairList 20).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 20) := by
  decide

/-- Every pair stored in sparse fiber 21 has class 21. -/
private theorem classPairList_sound_21 :
    (classPairList 21).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 21) := by
  decide

/-- Every pair stored in sparse fiber 22 has class 22. -/
private theorem classPairList_sound_22 :
    (classPairList 22).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 22) := by
  decide

/-- Every pair stored in sparse fiber 23 has class 23. -/
private theorem classPairList_sound_23 :
    (classPairList 23).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 23) := by
  decide

/-- Every pair stored in sparse fiber 24 has class 24. -/
private theorem classPairList_sound_24 :
    (classPairList 24).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 24) := by
  decide

/-- Every pair stored in sparse fiber 25 has class 25. -/
private theorem classPairList_sound_25 :
    (classPairList 25).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 25) := by
  decide

/-- Every pair stored in sparse fiber 26 has class 26. -/
private theorem classPairList_sound_26 :
    (classPairList 26).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 26) := by
  decide

/-- Every pair stored in sparse fiber 27 has class 27. -/
private theorem classPairList_sound_27 :
    (classPairList 27).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 27) := by
  decide

/-- Every pair stored in sparse fiber 28 has class 28. -/
private theorem classPairList_sound_28 :
    (classPairList 28).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 28) := by
  decide

/-- Every pair stored in sparse fiber 29 has class 29. -/
private theorem classPairList_sound_29 :
    (classPairList 29).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 29) := by
  decide

/-- Every pair stored in sparse fiber 30 has class 30. -/
private theorem classPairList_sound_30 :
    (classPairList 30).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 30) := by
  decide

/-- Every pair stored in sparse fiber 31 has class 31. -/
private theorem classPairList_sound_31 :
    (classPairList 31).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 31) := by
  decide

/-- Every pair stored in sparse fiber 32 has class 32. -/
private theorem classPairList_sound_32 :
    (classPairList 32).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 32) := by
  decide

/-- Every pair stored in sparse fiber 33 has class 33. -/
private theorem classPairList_sound_33 :
    (classPairList 33).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 33) := by
  decide

/-- Every pair stored in sparse fiber 34 has class 34. -/
private theorem classPairList_sound_34 :
    (classPairList 34).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 34) := by
  decide

/-- Every pair stored in sparse fiber 35 has class 35. -/
private theorem classPairList_sound_35 :
    (classPairList 35).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 35) := by
  decide

/-- Every pair stored in sparse fiber 36 has class 36. -/
private theorem classPairList_sound_36 :
    (classPairList 36).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 36) := by
  decide

/-- Every pair stored in sparse fiber 37 has class 37. -/
private theorem classPairList_sound_37 :
    (classPairList 37).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 37) := by
  decide

/-- Every pair stored in sparse fiber 38 has class 38. -/
private theorem classPairList_sound_38 :
    (classPairList 38).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 38) := by
  decide

/-- Every pair stored in sparse fiber 39 has class 39. -/
private theorem classPairList_sound_39 :
    (classPairList 39).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 39) := by
  decide

/-- Every pair stored in sparse fiber 40 has class 40. -/
private theorem classPairList_sound_40 :
    (classPairList 40).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 40) := by
  decide

/-- Every pair stored in sparse fiber 41 has class 41. -/
private theorem classPairList_sound_41 :
    (classPairList 41).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 41) := by
  decide

/-- Every pair stored in sparse fiber 42 has class 42. -/
private theorem classPairList_sound_42 :
    (classPairList 42).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 42) := by
  decide

/-- Every pair stored in sparse fiber 43 has class 43. -/
private theorem classPairList_sound_43 :
    (classPairList 43).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 43) := by
  decide

/-- Every pair stored in sparse fiber 44 has class 44. -/
private theorem classPairList_sound_44 :
    (classPairList 44).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 44) := by
  decide

/-- Every pair stored in sparse fiber 45 has class 45. -/
private theorem classPairList_sound_45 :
    (classPairList 45).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 45) := by
  decide

/-- Every pair stored in sparse fiber 46 has class 46. -/
private theorem classPairList_sound_46 :
    (classPairList 46).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 46) := by
  decide

/-- Every pair stored in sparse fiber 47 has class 47. -/
private theorem classPairList_sound_47 :
    (classPairList 47).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 47) := by
  decide

/-- Every pair stored in sparse fiber 48 has class 48. -/
private theorem classPairList_sound_48 :
    (classPairList 48).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 48) := by
  decide

/-- Every pair stored in sparse fiber 49 has class 49. -/
private theorem classPairList_sound_49 :
    (classPairList 49).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 49) := by
  decide

/-- Every pair stored in sparse fiber 50 has class 50. -/
private theorem classPairList_sound_50 :
    (classPairList 50).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 50) := by
  decide

/-- Every pair stored in sparse fiber 51 has class 51. -/
private theorem classPairList_sound_51 :
    (classPairList 51).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 51) := by
  decide

/-- Every pair stored in sparse fiber 52 has class 52. -/
private theorem classPairList_sound_52 :
    (classPairList 52).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 52) := by
  decide

/-- Every pair stored in sparse fiber 53 has class 53. -/
private theorem classPairList_sound_53 :
    (classPairList 53).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 53) := by
  decide

/-- Every pair stored in sparse fiber 54 has class 54. -/
private theorem classPairList_sound_54 :
    (classPairList 54).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 54) := by
  decide

/-- Every pair stored in sparse fiber 55 has class 55. -/
private theorem classPairList_sound_55 :
    (classPairList 55).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 55) := by
  decide

/-- Every pair stored in sparse fiber 56 has class 56. -/
private theorem classPairList_sound_56 :
    (classPairList 56).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 56) := by
  decide

/-- Every pair stored in sparse fiber 57 has class 57. -/
private theorem classPairList_sound_57 :
    (classPairList 57).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 57) := by
  decide

/-- Every pair stored in sparse fiber 58 has class 58. -/
private theorem classPairList_sound_58 :
    (classPairList 58).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 58) := by
  decide

/-- Every pair stored in sparse fiber 59 has class 59. -/
private theorem classPairList_sound_59 :
    (classPairList 59).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 59) := by
  decide

/-- Every pair stored in sparse fiber 60 has class 60. -/
private theorem classPairList_sound_60 :
    (classPairList 60).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 60) := by
  decide

/-- Every pair stored in sparse fiber 61 has class 61. -/
private theorem classPairList_sound_61 :
    (classPairList 61).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 61) := by
  decide

/-- Every pair stored in sparse fiber 62 has class 62. -/
private theorem classPairList_sound_62 :
    (classPairList 62).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 62) := by
  decide

/-- Every pair stored in sparse fiber 63 has class 63. -/
private theorem classPairList_sound_63 :
    (classPairList 63).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 63) := by
  decide

/-- Every pair stored in sparse fiber 64 has class 64. -/
private theorem classPairList_sound_64 :
    (classPairList 64).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 64) := by
  decide

/-- Every pair stored in sparse fiber 65 has class 65. -/
private theorem classPairList_sound_65 :
    (classPairList 65).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 65) := by
  decide

/-- Every pair stored in sparse fiber 66 has class 66. -/
private theorem classPairList_sound_66 :
    (classPairList 66).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 66) := by
  decide

/-- Every pair stored in sparse fiber 67 has class 67. -/
private theorem classPairList_sound_67 :
    (classPairList 67).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 67) := by
  decide

/-- Every pair stored in sparse fiber 68 has class 68. -/
private theorem classPairList_sound_68 :
    (classPairList 68).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 68) := by
  decide

/-- Every pair stored in sparse fiber 69 has class 69. -/
private theorem classPairList_sound_69 :
    (classPairList 69).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 69) := by
  decide

/-- Every pair stored in sparse fiber 70 has class 70. -/
private theorem classPairList_sound_70 :
    (classPairList 70).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 70) := by
  decide

/-- Every pair stored in sparse fiber 71 has class 71. -/
private theorem classPairList_sound_71 :
    (classPairList 71).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 71) := by
  decide

/-- Every pair stored in sparse fiber 72 has class 72. -/
private theorem classPairList_sound_72 :
    (classPairList 72).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 72) := by
  decide

/-- Every pair stored in sparse fiber 73 has class 73. -/
private theorem classPairList_sound_73 :
    (classPairList 73).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 73) := by
  decide

/-- Every pair stored in sparse fiber 74 has class 74. -/
private theorem classPairList_sound_74 :
    (classPairList 74).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 74) := by
  decide

/-- Every pair stored in sparse fiber 75 has class 75. -/
private theorem classPairList_sound_75 :
    (classPairList 75).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 75) := by
  decide

/-- Every pair stored in sparse fiber 76 has class 76. -/
private theorem classPairList_sound_76 :
    (classPairList 76).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 76) := by
  decide

/-- Every pair stored in sparse fiber 77 has class 77. -/
private theorem classPairList_sound_77 :
    (classPairList 77).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 77) := by
  decide

/-- Every pair stored in sparse fiber 78 has class 78. -/
private theorem classPairList_sound_78 :
    (classPairList 78).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 78) := by
  decide

/-- Every pair stored in sparse fiber 79 has class 79. -/
private theorem classPairList_sound_79 :
    (classPairList 79).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 79) := by
  decide

/-- Every pair stored in sparse fiber 80 has class 80. -/
private theorem classPairList_sound_80 :
    (classPairList 80).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 80) := by
  decide

/-- Every pair stored in sparse fiber 81 has class 81. -/
private theorem classPairList_sound_81 :
    (classPairList 81).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 81) := by
  decide

/-- Every pair stored in sparse fiber 82 has class 82. -/
private theorem classPairList_sound_82 :
    (classPairList 82).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 82) := by
  decide

/-- Every pair stored in sparse fiber 83 has class 83. -/
private theorem classPairList_sound_83 :
    (classPairList 83).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 83) := by
  decide

/-- Every pair stored in sparse fiber 84 has class 84. -/
private theorem classPairList_sound_84 :
    (classPairList 84).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 84) := by
  decide

/-- Every pair stored in sparse fiber 85 has class 85. -/
private theorem classPairList_sound_85 :
    (classPairList 85).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 85) := by
  decide

/-- Every pair stored in sparse fiber 86 has class 86. -/
private theorem classPairList_sound_86 :
    (classPairList 86).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 86) := by
  decide

/-- Every pair stored in sparse fiber 87 has class 87. -/
private theorem classPairList_sound_87 :
    (classPairList 87).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 87) := by
  decide

/-- Every pair stored in sparse fiber 88 has class 88. -/
private theorem classPairList_sound_88 :
    (classPairList 88).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 88) := by
  decide

/-- Every pair stored in sparse fiber 89 has class 89. -/
private theorem classPairList_sound_89 :
    (classPairList 89).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 89) := by
  decide

/-- Every pair stored in sparse fiber 90 has class 90. -/
private theorem classPairList_sound_90 :
    (classPairList 90).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 90) := by
  decide

/-- Every pair stored in sparse fiber 91 has class 91. -/
private theorem classPairList_sound_91 :
    (classPairList 91).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 91) := by
  decide

/-- Every pair stored in sparse fiber 92 has class 92. -/
private theorem classPairList_sound_92 :
    (classPairList 92).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 92) := by
  decide

/-- Every pair stored in sparse fiber 93 has class 93. -/
private theorem classPairList_sound_93 :
    (classPairList 93).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 93) := by
  decide

/-- Every pair stored in sparse fiber 94 has class 94. -/
private theorem classPairList_sound_94 :
    (classPairList 94).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 94) := by
  decide

/-- Every pair stored in sparse fiber 95 has class 95. -/
private theorem classPairList_sound_95 :
    (classPairList 95).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 95) := by
  decide

/-- Every pair stored in sparse fiber 96 has class 96. -/
private theorem classPairList_sound_96 :
    (classPairList 96).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 96) := by
  decide

/-- Every pair stored in sparse fiber 97 has class 97. -/
private theorem classPairList_sound_97 :
    (classPairList 97).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 97) := by
  decide

/-- Every pair stored in sparse fiber 98 has class 98. -/
private theorem classPairList_sound_98 :
    (classPairList 98).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 98) := by
  decide

/-- Every pair stored in sparse fiber 99 has class 99. -/
private theorem classPairList_sound_99 :
    (classPairList 99).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 99) := by
  decide

/-- Every pair stored in sparse fiber 100 has class 100. -/
private theorem classPairList_sound_100 :
    (classPairList 100).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 100) := by
  decide

/-- Every pair stored in sparse fiber 101 has class 101. -/
private theorem classPairList_sound_101 :
    (classPairList 101).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 101) := by
  decide

/-- Every pair stored in sparse fiber 102 has class 102. -/
private theorem classPairList_sound_102 :
    (classPairList 102).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 102) := by
  decide

/-- Every pair stored in sparse fiber 103 has class 103. -/
private theorem classPairList_sound_103 :
    (classPairList 103).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 103) := by
  decide

/-- Every pair stored in sparse fiber 104 has class 104. -/
private theorem classPairList_sound_104 :
    (classPairList 104).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 104) := by
  decide

/-- Every pair stored in sparse fiber 105 has class 105. -/
private theorem classPairList_sound_105 :
    (classPairList 105).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 105) := by
  decide

/-- Every pair stored in sparse fiber 106 has class 106. -/
private theorem classPairList_sound_106 :
    (classPairList 106).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 106) := by
  decide

/-- Every pair stored in sparse fiber 107 has class 107. -/
private theorem classPairList_sound_107 :
    (classPairList 107).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 107) := by
  decide

/-- Every pair stored in sparse fiber 108 has class 108. -/
private theorem classPairList_sound_108 :
    (classPairList 108).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 108) := by
  decide

/-- Every pair stored in sparse fiber 109 has class 109. -/
private theorem classPairList_sound_109 :
    (classPairList 109).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 109) := by
  decide

/-- Every pair stored in sparse fiber 110 has class 110. -/
private theorem classPairList_sound_110 :
    (classPairList 110).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 110) := by
  decide

/-- Every pair stored in sparse fiber 111 has class 111. -/
private theorem classPairList_sound_111 :
    (classPairList 111).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 111) := by
  decide

/-- Every pair stored in sparse fiber 112 has class 112. -/
private theorem classPairList_sound_112 :
    (classPairList 112).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 112) := by
  decide

/-- Every pair stored in sparse fiber 113 has class 113. -/
private theorem classPairList_sound_113 :
    (classPairList 113).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 113) := by
  decide

/-- Every pair stored in sparse fiber 114 has class 114. -/
private theorem classPairList_sound_114 :
    (classPairList 114).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 114) := by
  decide

/-- Every pair stored in sparse fiber 115 has class 115. -/
private theorem classPairList_sound_115 :
    (classPairList 115).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 115) := by
  decide

/-- Every pair stored in sparse fiber 116 has class 116. -/
private theorem classPairList_sound_116 :
    (classPairList 116).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 116) := by
  decide

/-- Every pair stored in sparse fiber 117 has class 117. -/
private theorem classPairList_sound_117 :
    (classPairList 117).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 117) := by
  decide

/-- Every pair stored in sparse fiber 118 has class 118. -/
private theorem classPairList_sound_118 :
    (classPairList 118).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 118) := by
  decide

/-- Every pair stored in sparse fiber 119 has class 119. -/
private theorem classPairList_sound_119 :
    (classPairList 119).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 119) := by
  decide

/-- Every pair stored in sparse fiber 120 has class 120. -/
private theorem classPairList_sound_120 :
    (classPairList 120).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 120) := by
  decide

/-- Every pair stored in sparse fiber 121 has class 121. -/
private theorem classPairList_sound_121 :
    (classPairList 121).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 121) := by
  decide

/-- Every pair stored in sparse fiber 122 has class 122. -/
private theorem classPairList_sound_122 :
    (classPairList 122).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 122) := by
  decide

/-- Every pair stored in sparse fiber 123 has class 123. -/
private theorem classPairList_sound_123 :
    (classPairList 123).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 123) := by
  decide

/-- Every pair stored in sparse fiber 124 has class 124. -/
private theorem classPairList_sound_124 :
    (classPairList 124).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 124) := by
  decide

/-- Every pair stored in sparse fiber 125 has class 125. -/
private theorem classPairList_sound_125 :
    (classPairList 125).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 125) := by
  decide

/-- Every pair stored in sparse fiber 126 has class 126. -/
private theorem classPairList_sound_126 :
    (classPairList 126).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 126) := by
  decide

/-- Every pair stored in sparse fiber 127 has class 127. -/
private theorem classPairList_sound_127 :
    (classPairList 127).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 127) := by
  decide

/-- Every pair stored in sparse fiber 128 has class 128. -/
private theorem classPairList_sound_128 :
    (classPairList 128).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 128) := by
  decide

/-- Every pair stored in sparse fiber 129 has class 129. -/
private theorem classPairList_sound_129 :
    (classPairList 129).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 129) := by
  decide

/-- Every pair stored in sparse fiber 130 has class 130. -/
private theorem classPairList_sound_130 :
    (classPairList 130).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 130) := by
  decide

/-- Every pair stored in sparse fiber 131 has class 131. -/
private theorem classPairList_sound_131 :
    (classPairList 131).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 131) := by
  decide

/-- Every pair stored in sparse fiber 132 has class 132. -/
private theorem classPairList_sound_132 :
    (classPairList 132).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 132) := by
  decide

/-- Every pair stored in sparse fiber 133 has class 133. -/
private theorem classPairList_sound_133 :
    (classPairList 133).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 133) := by
  decide

/-- Every pair stored in sparse fiber 134 has class 134. -/
private theorem classPairList_sound_134 :
    (classPairList 134).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 134) := by
  decide

/-- Every pair stored in sparse fiber 135 has class 135. -/
private theorem classPairList_sound_135 :
    (classPairList 135).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 135) := by
  decide

/-- Every pair stored in sparse fiber 136 has class 136. -/
private theorem classPairList_sound_136 :
    (classPairList 136).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 136) := by
  decide

/-- Every pair stored in sparse fiber 137 has class 137. -/
private theorem classPairList_sound_137 :
    (classPairList 137).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 137) := by
  decide

/-- Every pair stored in sparse fiber 138 has class 138. -/
private theorem classPairList_sound_138 :
    (classPairList 138).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 138) := by
  decide

/-- Every pair stored in sparse fiber 139 has class 139. -/
private theorem classPairList_sound_139 :
    (classPairList 139).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 139) := by
  decide

/-- Every pair stored in sparse fiber 140 has class 140. -/
private theorem classPairList_sound_140 :
    (classPairList 140).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 140) := by
  decide

/-- Every pair stored in sparse fiber 141 has class 141. -/
private theorem classPairList_sound_141 :
    (classPairList 141).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 141) := by
  decide

/-- Every pair stored in sparse fiber 142 has class 142. -/
private theorem classPairList_sound_142 :
    (classPairList 142).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 142) := by
  decide

/-- Every pair stored in sparse fiber 143 has class 143. -/
private theorem classPairList_sound_143 :
    (classPairList 143).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 143) := by
  decide

/-- Every pair stored in sparse fiber 144 has class 144. -/
private theorem classPairList_sound_144 :
    (classPairList 144).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 144) := by
  decide

/-- Every pair stored in sparse fiber 145 has class 145. -/
private theorem classPairList_sound_145 :
    (classPairList 145).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 145) := by
  decide

/-- Every pair stored in sparse fiber 146 has class 146. -/
private theorem classPairList_sound_146 :
    (classPairList 146).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 146) := by
  decide

/-- Every pair stored in sparse fiber 147 has class 147. -/
private theorem classPairList_sound_147 :
    (classPairList 147).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 147) := by
  decide

/-- Every pair stored in sparse fiber 148 has class 148. -/
private theorem classPairList_sound_148 :
    (classPairList 148).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 148) := by
  decide

/-- Every pair stored in sparse fiber 149 has class 149. -/
private theorem classPairList_sound_149 :
    (classPairList 149).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 149) := by
  decide

/-- Every pair stored in sparse fiber 150 has class 150. -/
private theorem classPairList_sound_150 :
    (classPairList 150).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 150) := by
  decide

/-- Every pair stored in sparse fiber 151 has class 151. -/
private theorem classPairList_sound_151 :
    (classPairList 151).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 151) := by
  decide

/-- Every pair stored in sparse fiber 152 has class 152. -/
private theorem classPairList_sound_152 :
    (classPairList 152).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 152) := by
  decide

/-- Every pair stored in sparse fiber 153 has class 153. -/
private theorem classPairList_sound_153 :
    (classPairList 153).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 153) := by
  decide

/-- Every pair stored in sparse fiber 154 has class 154. -/
private theorem classPairList_sound_154 :
    (classPairList 154).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 154) := by
  decide

/-- Every pair stored in sparse fiber 155 has class 155. -/
private theorem classPairList_sound_155 :
    (classPairList 155).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 155) := by
  decide

/-- Every pair stored in sparse fiber 156 has class 156. -/
private theorem classPairList_sound_156 :
    (classPairList 156).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 156) := by
  decide

/-- Every pair stored in sparse fiber 157 has class 157. -/
private theorem classPairList_sound_157 :
    (classPairList 157).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 157) := by
  decide

/-- Every pair stored in sparse fiber 158 has class 158. -/
private theorem classPairList_sound_158 :
    (classPairList 158).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 158) := by
  decide

/-- Every pair stored in sparse fiber 159 has class 159. -/
private theorem classPairList_sound_159 :
    (classPairList 159).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 159) := by
  decide

/-- Every pair stored in sparse fiber 160 has class 160. -/
private theorem classPairList_sound_160 :
    (classPairList 160).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 160) := by
  decide

/-- Every pair stored in sparse fiber 161 has class 161. -/
private theorem classPairList_sound_161 :
    (classPairList 161).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 161) := by
  decide

/-- Every pair stored in sparse fiber 162 has class 162. -/
private theorem classPairList_sound_162 :
    (classPairList 162).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 162) := by
  decide

/-- Every pair stored in sparse fiber 163 has class 163. -/
private theorem classPairList_sound_163 :
    (classPairList 163).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 163) := by
  decide

/-- Every pair stored in sparse fiber 164 has class 164. -/
private theorem classPairList_sound_164 :
    (classPairList 164).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 164) := by
  decide

/-- Every pair stored in sparse fiber 165 has class 165. -/
private theorem classPairList_sound_165 :
    (classPairList 165).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 165) := by
  decide

/-- Every pair stored in sparse fiber 166 has class 166. -/
private theorem classPairList_sound_166 :
    (classPairList 166).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 166) := by
  decide

/-- Every pair stored in sparse fiber 167 has class 167. -/
private theorem classPairList_sound_167 :
    (classPairList 167).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 167) := by
  decide

/-- Every pair stored in sparse fiber 168 has class 168. -/
private theorem classPairList_sound_168 :
    (classPairList 168).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 168) := by
  decide

/-- Every pair stored in sparse fiber 169 has class 169. -/
private theorem classPairList_sound_169 :
    (classPairList 169).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 169) := by
  decide

/-- Every pair stored in sparse fiber 170 has class 170. -/
private theorem classPairList_sound_170 :
    (classPairList 170).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 170) := by
  decide

/-- Every pair stored in sparse fiber 171 has class 171. -/
private theorem classPairList_sound_171 :
    (classPairList 171).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 171) := by
  decide

/-- Every pair stored in sparse fiber 172 has class 172. -/
private theorem classPairList_sound_172 :
    (classPairList 172).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 172) := by
  decide

/-- Every pair stored in sparse fiber 173 has class 173. -/
private theorem classPairList_sound_173 :
    (classPairList 173).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 173) := by
  decide

/-- Every pair stored in sparse fiber 174 has class 174. -/
private theorem classPairList_sound_174 :
    (classPairList 174).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 174) := by
  decide

/-- Every pair stored in sparse fiber 175 has class 175. -/
private theorem classPairList_sound_175 :
    (classPairList 175).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 175) := by
  decide

/-- Every pair stored in sparse fiber 176 has class 176. -/
private theorem classPairList_sound_176 :
    (classPairList 176).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 176) := by
  decide

/-- Every pair stored in sparse fiber 177 has class 177. -/
private theorem classPairList_sound_177 :
    (classPairList 177).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 177) := by
  decide

/-- Every pair stored in sparse fiber 178 has class 178. -/
private theorem classPairList_sound_178 :
    (classPairList 178).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 178) := by
  decide

/-- Every pair stored in sparse fiber 179 has class 179. -/
private theorem classPairList_sound_179 :
    (classPairList 179).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 179) := by
  decide

/-- Every pair stored in sparse fiber 180 has class 180. -/
private theorem classPairList_sound_180 :
    (classPairList 180).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 180) := by
  decide

/-- Every pair stored in sparse fiber 181 has class 181. -/
private theorem classPairList_sound_181 :
    (classPairList 181).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 181) := by
  decide

/-- Every pair stored in sparse fiber 182 has class 182. -/
private theorem classPairList_sound_182 :
    (classPairList 182).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 182) := by
  decide

/-- Every pair stored in sparse fiber 183 has class 183. -/
private theorem classPairList_sound_183 :
    (classPairList 183).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 183) := by
  decide

/-- Every pair stored in sparse fiber 184 has class 184. -/
private theorem classPairList_sound_184 :
    (classPairList 184).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 184) := by
  decide

/-- Every pair stored in sparse fiber 185 has class 185. -/
private theorem classPairList_sound_185 :
    (classPairList 185).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 185) := by
  decide

/-- Every pair stored in sparse fiber 186 has class 186. -/
private theorem classPairList_sound_186 :
    (classPairList 186).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 186) := by
  decide

/-- Every pair stored in sparse fiber 187 has class 187. -/
private theorem classPairList_sound_187 :
    (classPairList 187).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 187) := by
  decide

/-- Every pair stored in sparse fiber 188 has class 188. -/
private theorem classPairList_sound_188 :
    (classPairList 188).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 188) := by
  decide

/-- Every pair stored in sparse fiber 189 has class 189. -/
private theorem classPairList_sound_189 :
    (classPairList 189).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 189) := by
  decide

/-- Every pair stored in sparse fiber 190 has class 190. -/
private theorem classPairList_sound_190 :
    (classPairList 190).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 190) := by
  decide

/-- Every pair stored in sparse fiber 191 has class 191. -/
private theorem classPairList_sound_191 :
    (classPairList 191).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 191) := by
  decide

/-- Every pair stored in sparse fiber 192 has class 192. -/
private theorem classPairList_sound_192 :
    (classPairList 192).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 192) := by
  decide

/-- Every pair stored in sparse fiber 193 has class 193. -/
private theorem classPairList_sound_193 :
    (classPairList 193).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 193) := by
  decide

/-- Every pair stored in sparse fiber 194 has class 194. -/
private theorem classPairList_sound_194 :
    (classPairList 194).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 194) := by
  decide

/-- Every pair stored in sparse fiber 195 has class 195. -/
private theorem classPairList_sound_195 :
    (classPairList 195).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 195) := by
  decide

/-- Every pair stored in sparse fiber 196 has class 196. -/
private theorem classPairList_sound_196 :
    (classPairList 196).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 196) := by
  decide

/-- Every pair stored in sparse fiber 197 has class 197. -/
private theorem classPairList_sound_197 :
    (classPairList 197).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 197) := by
  decide

/-- Every pair stored in sparse fiber 198 has class 198. -/
private theorem classPairList_sound_198 :
    (classPairList 198).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 198) := by
  decide

/-- Every pair stored in sparse fiber 199 has class 199. -/
private theorem classPairList_sound_199 :
    (classPairList 199).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 199) := by
  decide

/-- Every pair stored in sparse fiber 200 has class 200. -/
private theorem classPairList_sound_200 :
    (classPairList 200).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 200) := by
  decide

/-- Every pair stored in sparse fiber 201 has class 201. -/
private theorem classPairList_sound_201 :
    (classPairList 201).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 201) := by
  decide

/-- Every pair stored in sparse fiber 202 has class 202. -/
private theorem classPairList_sound_202 :
    (classPairList 202).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 202) := by
  decide

/-- Every pair stored in sparse fiber 203 has class 203. -/
private theorem classPairList_sound_203 :
    (classPairList 203).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 203) := by
  decide

/-- Every pair stored in sparse fiber 204 has class 204. -/
private theorem classPairList_sound_204 :
    (classPairList 204).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 204) := by
  decide

/-- Every pair stored in sparse fiber 205 has class 205. -/
private theorem classPairList_sound_205 :
    (classPairList 205).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 205) := by
  decide

/-- Every pair stored in sparse fiber 206 has class 206. -/
private theorem classPairList_sound_206 :
    (classPairList 206).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 206) := by
  decide

/-- Every pair stored in sparse fiber 207 has class 207. -/
private theorem classPairList_sound_207 :
    (classPairList 207).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 207) := by
  decide

/-- Every pair stored in sparse fiber 208 has class 208. -/
private theorem classPairList_sound_208 :
    (classPairList 208).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 208) := by
  decide

/-- Every pair stored in sparse fiber 209 has class 209. -/
private theorem classPairList_sound_209 :
    (classPairList 209).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 209) := by
  decide

/-- Every pair stored in sparse fiber 210 has class 210. -/
private theorem classPairList_sound_210 :
    (classPairList 210).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 210) := by
  decide

/-- Every pair stored in sparse fiber 211 has class 211. -/
private theorem classPairList_sound_211 :
    (classPairList 211).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 211) := by
  decide

/-- Every pair stored in sparse fiber 212 has class 212. -/
private theorem classPairList_sound_212 :
    (classPairList 212).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 212) := by
  decide

/-- Every pair stored in sparse fiber 213 has class 213. -/
private theorem classPairList_sound_213 :
    (classPairList 213).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 213) := by
  decide

/-- Every pair stored in sparse fiber 214 has class 214. -/
private theorem classPairList_sound_214 :
    (classPairList 214).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 214) := by
  decide

/-- Every pair stored in sparse fiber 215 has class 215. -/
private theorem classPairList_sound_215 :
    (classPairList 215).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 215) := by
  decide

/-- Every pair stored in sparse fiber 216 has class 216. -/
private theorem classPairList_sound_216 :
    (classPairList 216).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 216) := by
  decide

/-- Every pair stored in sparse fiber 217 has class 217. -/
private theorem classPairList_sound_217 :
    (classPairList 217).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 217) := by
  decide

/-- Every pair stored in sparse fiber 218 has class 218. -/
private theorem classPairList_sound_218 :
    (classPairList 218).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 218) := by
  decide

/-- Every pair stored in sparse fiber 219 has class 219. -/
private theorem classPairList_sound_219 :
    (classPairList 219).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 219) := by
  decide

/-- Every pair stored in sparse fiber 220 has class 220. -/
private theorem classPairList_sound_220 :
    (classPairList 220).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 220) := by
  decide

/-- Every pair stored in sparse fiber 221 has class 221. -/
private theorem classPairList_sound_221 :
    (classPairList 221).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 221) := by
  decide

/-- Every pair stored in sparse fiber 222 has class 222. -/
private theorem classPairList_sound_222 :
    (classPairList 222).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 222) := by
  decide

/-- Every pair stored in sparse fiber 223 has class 223. -/
private theorem classPairList_sound_223 :
    (classPairList 223).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 223) := by
  decide

/-- Every pair stored in sparse fiber 224 has class 224. -/
private theorem classPairList_sound_224 :
    (classPairList 224).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 224) := by
  decide

/-- Every pair stored in sparse fiber 225 has class 225. -/
private theorem classPairList_sound_225 :
    (classPairList 225).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 225) := by
  decide

/-- Every pair stored in sparse fiber 226 has class 226. -/
private theorem classPairList_sound_226 :
    (classPairList 226).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 226) := by
  decide

/-- Every pair stored in sparse fiber 227 has class 227. -/
private theorem classPairList_sound_227 :
    (classPairList 227).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 227) := by
  decide

/-- Every pair stored in sparse fiber 228 has class 228. -/
private theorem classPairList_sound_228 :
    (classPairList 228).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 228) := by
  decide

/-- Every pair stored in sparse fiber 229 has class 229. -/
private theorem classPairList_sound_229 :
    (classPairList 229).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 229) := by
  decide

/-- Every pair stored in sparse fiber 230 has class 230. -/
private theorem classPairList_sound_230 :
    (classPairList 230).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 230) := by
  decide

/-- Every pair stored in sparse fiber 231 has class 231. -/
private theorem classPairList_sound_231 :
    (classPairList 231).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 231) := by
  decide

/-- Every pair stored in sparse fiber 232 has class 232. -/
private theorem classPairList_sound_232 :
    (classPairList 232).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 232) := by
  decide

/-- Every pair stored in sparse fiber 233 has class 233. -/
private theorem classPairList_sound_233 :
    (classPairList 233).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 233) := by
  decide

/-- Every pair stored in sparse fiber 234 has class 234. -/
private theorem classPairList_sound_234 :
    (classPairList 234).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 234) := by
  decide

/-- Every pair stored in sparse fiber 235 has class 235. -/
private theorem classPairList_sound_235 :
    (classPairList 235).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 235) := by
  decide

/-- Every pair stored in sparse fiber 236 has class 236. -/
private theorem classPairList_sound_236 :
    (classPairList 236).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 236) := by
  decide

/-- Every pair stored in sparse fiber 237 has class 237. -/
private theorem classPairList_sound_237 :
    (classPairList 237).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 237) := by
  decide

/-- Every pair stored in sparse fiber 238 has class 238. -/
private theorem classPairList_sound_238 :
    (classPairList 238).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 238) := by
  decide

/-- Every pair stored in sparse fiber 239 has class 239. -/
private theorem classPairList_sound_239 :
    (classPairList 239).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 239) := by
  decide

/-- Every pair stored in sparse fiber 240 has class 240. -/
private theorem classPairList_sound_240 :
    (classPairList 240).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 240) := by
  decide

/-- Every pair stored in sparse fiber 241 has class 241. -/
private theorem classPairList_sound_241 :
    (classPairList 241).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 241) := by
  decide

/-- Every pair stored in sparse fiber 242 has class 242. -/
private theorem classPairList_sound_242 :
    (classPairList 242).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 242) := by
  decide

/-- Every pair stored in sparse fiber 243 has class 243. -/
private theorem classPairList_sound_243 :
    (classPairList 243).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 243) := by
  decide

/-- Every pair stored in sparse fiber 244 has class 244. -/
private theorem classPairList_sound_244 :
    (classPairList 244).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 244) := by
  decide

/-- Every pair stored in sparse fiber 245 has class 245. -/
private theorem classPairList_sound_245 :
    (classPairList 245).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 245) := by
  decide

/-- Every pair stored in sparse fiber 246 has class 246. -/
private theorem classPairList_sound_246 :
    (classPairList 246).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 246) := by
  decide

/-- Every pair stored in sparse fiber 247 has class 247. -/
private theorem classPairList_sound_247 :
    (classPairList 247).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 247) := by
  decide

/-- Every pair stored in sparse fiber 248 has class 248. -/
private theorem classPairList_sound_248 :
    (classPairList 248).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 248) := by
  decide

/-- Every pair stored in sparse fiber 249 has class 249. -/
private theorem classPairList_sound_249 :
    (classPairList 249).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 249) := by
  decide

/-- Every pair stored in sparse fiber 250 has class 250. -/
private theorem classPairList_sound_250 :
    (classPairList 250).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 250) := by
  decide

/-- Every pair stored in sparse fiber 251 has class 251. -/
private theorem classPairList_sound_251 :
    (classPairList 251).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 251) := by
  decide

/-- Every pair stored in sparse fiber 252 has class 252. -/
private theorem classPairList_sound_252 :
    (classPairList 252).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 252) := by
  decide

/-- Every pair stored in sparse fiber 253 has class 253. -/
private theorem classPairList_sound_253 :
    (classPairList 253).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 253) := by
  decide

/-- Every pair stored in sparse fiber 254 has class 254. -/
private theorem classPairList_sound_254 :
    (classPairList 254).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 254) := by
  decide

/-- Every pair stored in sparse fiber 255 has class 255. -/
private theorem classPairList_sound_255 :
    (classPairList 255).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 255) := by
  decide

/-- Every pair stored in sparse fiber 256 has class 256. -/
private theorem classPairList_sound_256 :
    (classPairList 256).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 256) := by
  decide

/-- Every pair stored in sparse fiber 257 has class 257. -/
private theorem classPairList_sound_257 :
    (classPairList 257).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 257) := by
  decide

/-- Every pair stored in sparse fiber 258 has class 258. -/
private theorem classPairList_sound_258 :
    (classPairList 258).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 258) := by
  decide

/-- Every pair stored in sparse fiber 259 has class 259. -/
private theorem classPairList_sound_259 :
    (classPairList 259).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 259) := by
  decide

/-- Every pair stored in sparse fiber 260 has class 260. -/
private theorem classPairList_sound_260 :
    (classPairList 260).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 260) := by
  decide

/-- Every pair stored in sparse fiber 261 has class 261. -/
private theorem classPairList_sound_261 :
    (classPairList 261).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 261) := by
  decide

/-- Every pair stored in sparse fiber 262 has class 262. -/
private theorem classPairList_sound_262 :
    (classPairList 262).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 262) := by
  decide

/-- Every pair stored in sparse fiber 263 has class 263. -/
private theorem classPairList_sound_263 :
    (classPairList 263).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 263) := by
  decide

/-- Every pair stored in sparse fiber 264 has class 264. -/
private theorem classPairList_sound_264 :
    (classPairList 264).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 264) := by
  decide

/-- Every pair stored in sparse fiber 265 has class 265. -/
private theorem classPairList_sound_265 :
    (classPairList 265).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 265) := by
  decide

/-- Every pair stored in sparse fiber 266 has class 266. -/
private theorem classPairList_sound_266 :
    (classPairList 266).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 266) := by
  decide

/-- Every pair stored in sparse fiber 267 has class 267. -/
private theorem classPairList_sound_267 :
    (classPairList 267).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 267) := by
  decide

/-- Every pair stored in sparse fiber 268 has class 268. -/
private theorem classPairList_sound_268 :
    (classPairList 268).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 268) := by
  decide

/-- Every pair stored in sparse fiber 269 has class 269. -/
private theorem classPairList_sound_269 :
    (classPairList 269).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 269) := by
  decide

/-- Every pair stored in sparse fiber 270 has class 270. -/
private theorem classPairList_sound_270 :
    (classPairList 270).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 270) := by
  decide

/-- Every pair stored in sparse fiber 271 has class 271. -/
private theorem classPairList_sound_271 :
    (classPairList 271).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 271) := by
  decide

/-- Every pair stored in sparse fiber 272 has class 272. -/
private theorem classPairList_sound_272 :
    (classPairList 272).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 272) := by
  decide

/-- Every pair stored in sparse fiber 273 has class 273. -/
private theorem classPairList_sound_273 :
    (classPairList 273).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 273) := by
  decide

/-- Every pair stored in sparse fiber 274 has class 274. -/
private theorem classPairList_sound_274 :
    (classPairList 274).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 274) := by
  decide

/-- Every pair stored in sparse fiber 275 has class 275. -/
private theorem classPairList_sound_275 :
    (classPairList 275).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 275) := by
  decide

/-- Every pair stored in sparse fiber 276 has class 276. -/
private theorem classPairList_sound_276 :
    (classPairList 276).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 276) := by
  decide

/-- Every pair stored in sparse fiber 277 has class 277. -/
private theorem classPairList_sound_277 :
    (classPairList 277).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 277) := by
  decide

/-- Every pair stored in sparse fiber 278 has class 278. -/
private theorem classPairList_sound_278 :
    (classPairList 278).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 278) := by
  decide

/-- Every pair stored in sparse fiber 279 has class 279. -/
private theorem classPairList_sound_279 :
    (classPairList 279).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 279) := by
  decide

/-- Every pair stored in sparse fiber 280 has class 280. -/
private theorem classPairList_sound_280 :
    (classPairList 280).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 280) := by
  decide

/-- Every pair stored in sparse fiber 281 has class 281. -/
private theorem classPairList_sound_281 :
    (classPairList 281).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 281) := by
  decide

/-- Every pair stored in sparse fiber 282 has class 282. -/
private theorem classPairList_sound_282 :
    (classPairList 282).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 282) := by
  decide

/-- Every pair stored in sparse fiber 283 has class 283. -/
private theorem classPairList_sound_283 :
    (classPairList 283).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 283) := by
  decide

/-- Every pair stored in sparse fiber 284 has class 284. -/
private theorem classPairList_sound_284 :
    (classPairList 284).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 284) := by
  decide

/-- Every pair stored in sparse fiber 285 has class 285. -/
private theorem classPairList_sound_285 :
    (classPairList 285).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 285) := by
  decide

/-- Every pair stored in sparse fiber 286 has class 286. -/
private theorem classPairList_sound_286 :
    (classPairList 286).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 286) := by
  decide

/-- Every pair stored in sparse fiber 287 has class 287. -/
private theorem classPairList_sound_287 :
    (classPairList 287).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 287) := by
  decide

/-- Every pair stored in sparse fiber 288 has class 288. -/
private theorem classPairList_sound_288 :
    (classPairList 288).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 288) := by
  decide

/-- Every pair stored in sparse fiber 289 has class 289. -/
private theorem classPairList_sound_289 :
    (classPairList 289).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 289) := by
  decide

/-- Every pair stored in sparse fiber 290 has class 290. -/
private theorem classPairList_sound_290 :
    (classPairList 290).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 290) := by
  decide

/-- Every pair stored in sparse fiber 291 has class 291. -/
private theorem classPairList_sound_291 :
    (classPairList 291).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 291) := by
  decide

/-- Every pair stored in sparse fiber 292 has class 292. -/
private theorem classPairList_sound_292 :
    (classPairList 292).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = 292) := by
  decide

private theorem classPairList_sound_0_32 (c : Fin 293)
    (hlo : 0 ≤ c.1) (hhi : c.1 < 32) :
    (classPairList c).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = c) := by
  by_cases h0 : c.1 = 0
  · have hc : c = (0 : Fin 293) := Fin.ext h0
    subst c
    exact classPairList_sound_0
  by_cases h1 : c.1 = 1
  · have hc : c = (1 : Fin 293) := Fin.ext h1
    subst c
    exact classPairList_sound_1
  by_cases h2 : c.1 = 2
  · have hc : c = (2 : Fin 293) := Fin.ext h2
    subst c
    exact classPairList_sound_2
  by_cases h3 : c.1 = 3
  · have hc : c = (3 : Fin 293) := Fin.ext h3
    subst c
    exact classPairList_sound_3
  by_cases h4 : c.1 = 4
  · have hc : c = (4 : Fin 293) := Fin.ext h4
    subst c
    exact classPairList_sound_4
  by_cases h5 : c.1 = 5
  · have hc : c = (5 : Fin 293) := Fin.ext h5
    subst c
    exact classPairList_sound_5
  by_cases h6 : c.1 = 6
  · have hc : c = (6 : Fin 293) := Fin.ext h6
    subst c
    exact classPairList_sound_6
  by_cases h7 : c.1 = 7
  · have hc : c = (7 : Fin 293) := Fin.ext h7
    subst c
    exact classPairList_sound_7
  by_cases h8 : c.1 = 8
  · have hc : c = (8 : Fin 293) := Fin.ext h8
    subst c
    exact classPairList_sound_8
  by_cases h9 : c.1 = 9
  · have hc : c = (9 : Fin 293) := Fin.ext h9
    subst c
    exact classPairList_sound_9
  by_cases h10 : c.1 = 10
  · have hc : c = (10 : Fin 293) := Fin.ext h10
    subst c
    exact classPairList_sound_10
  by_cases h11 : c.1 = 11
  · have hc : c = (11 : Fin 293) := Fin.ext h11
    subst c
    exact classPairList_sound_11
  by_cases h12 : c.1 = 12
  · have hc : c = (12 : Fin 293) := Fin.ext h12
    subst c
    exact classPairList_sound_12
  by_cases h13 : c.1 = 13
  · have hc : c = (13 : Fin 293) := Fin.ext h13
    subst c
    exact classPairList_sound_13
  by_cases h14 : c.1 = 14
  · have hc : c = (14 : Fin 293) := Fin.ext h14
    subst c
    exact classPairList_sound_14
  by_cases h15 : c.1 = 15
  · have hc : c = (15 : Fin 293) := Fin.ext h15
    subst c
    exact classPairList_sound_15
  by_cases h16 : c.1 = 16
  · have hc : c = (16 : Fin 293) := Fin.ext h16
    subst c
    exact classPairList_sound_16
  by_cases h17 : c.1 = 17
  · have hc : c = (17 : Fin 293) := Fin.ext h17
    subst c
    exact classPairList_sound_17
  by_cases h18 : c.1 = 18
  · have hc : c = (18 : Fin 293) := Fin.ext h18
    subst c
    exact classPairList_sound_18
  by_cases h19 : c.1 = 19
  · have hc : c = (19 : Fin 293) := Fin.ext h19
    subst c
    exact classPairList_sound_19
  by_cases h20 : c.1 = 20
  · have hc : c = (20 : Fin 293) := Fin.ext h20
    subst c
    exact classPairList_sound_20
  by_cases h21 : c.1 = 21
  · have hc : c = (21 : Fin 293) := Fin.ext h21
    subst c
    exact classPairList_sound_21
  by_cases h22 : c.1 = 22
  · have hc : c = (22 : Fin 293) := Fin.ext h22
    subst c
    exact classPairList_sound_22
  by_cases h23 : c.1 = 23
  · have hc : c = (23 : Fin 293) := Fin.ext h23
    subst c
    exact classPairList_sound_23
  by_cases h24 : c.1 = 24
  · have hc : c = (24 : Fin 293) := Fin.ext h24
    subst c
    exact classPairList_sound_24
  by_cases h25 : c.1 = 25
  · have hc : c = (25 : Fin 293) := Fin.ext h25
    subst c
    exact classPairList_sound_25
  by_cases h26 : c.1 = 26
  · have hc : c = (26 : Fin 293) := Fin.ext h26
    subst c
    exact classPairList_sound_26
  by_cases h27 : c.1 = 27
  · have hc : c = (27 : Fin 293) := Fin.ext h27
    subst c
    exact classPairList_sound_27
  by_cases h28 : c.1 = 28
  · have hc : c = (28 : Fin 293) := Fin.ext h28
    subst c
    exact classPairList_sound_28
  by_cases h29 : c.1 = 29
  · have hc : c = (29 : Fin 293) := Fin.ext h29
    subst c
    exact classPairList_sound_29
  by_cases h30 : c.1 = 30
  · have hc : c = (30 : Fin 293) := Fin.ext h30
    subst c
    exact classPairList_sound_30
  have hc : c = (31 : Fin 293) := Fin.ext (by lia)
  subst c
  exact classPairList_sound_31

private theorem classPairList_sound_32_64 (c : Fin 293)
    (hlo : 32 ≤ c.1) (hhi : c.1 < 64) :
    (classPairList c).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = c) := by
  by_cases h32 : c.1 = 32
  · have hc : c = (32 : Fin 293) := Fin.ext h32
    subst c
    exact classPairList_sound_32
  by_cases h33 : c.1 = 33
  · have hc : c = (33 : Fin 293) := Fin.ext h33
    subst c
    exact classPairList_sound_33
  by_cases h34 : c.1 = 34
  · have hc : c = (34 : Fin 293) := Fin.ext h34
    subst c
    exact classPairList_sound_34
  by_cases h35 : c.1 = 35
  · have hc : c = (35 : Fin 293) := Fin.ext h35
    subst c
    exact classPairList_sound_35
  by_cases h36 : c.1 = 36
  · have hc : c = (36 : Fin 293) := Fin.ext h36
    subst c
    exact classPairList_sound_36
  by_cases h37 : c.1 = 37
  · have hc : c = (37 : Fin 293) := Fin.ext h37
    subst c
    exact classPairList_sound_37
  by_cases h38 : c.1 = 38
  · have hc : c = (38 : Fin 293) := Fin.ext h38
    subst c
    exact classPairList_sound_38
  by_cases h39 : c.1 = 39
  · have hc : c = (39 : Fin 293) := Fin.ext h39
    subst c
    exact classPairList_sound_39
  by_cases h40 : c.1 = 40
  · have hc : c = (40 : Fin 293) := Fin.ext h40
    subst c
    exact classPairList_sound_40
  by_cases h41 : c.1 = 41
  · have hc : c = (41 : Fin 293) := Fin.ext h41
    subst c
    exact classPairList_sound_41
  by_cases h42 : c.1 = 42
  · have hc : c = (42 : Fin 293) := Fin.ext h42
    subst c
    exact classPairList_sound_42
  by_cases h43 : c.1 = 43
  · have hc : c = (43 : Fin 293) := Fin.ext h43
    subst c
    exact classPairList_sound_43
  by_cases h44 : c.1 = 44
  · have hc : c = (44 : Fin 293) := Fin.ext h44
    subst c
    exact classPairList_sound_44
  by_cases h45 : c.1 = 45
  · have hc : c = (45 : Fin 293) := Fin.ext h45
    subst c
    exact classPairList_sound_45
  by_cases h46 : c.1 = 46
  · have hc : c = (46 : Fin 293) := Fin.ext h46
    subst c
    exact classPairList_sound_46
  by_cases h47 : c.1 = 47
  · have hc : c = (47 : Fin 293) := Fin.ext h47
    subst c
    exact classPairList_sound_47
  by_cases h48 : c.1 = 48
  · have hc : c = (48 : Fin 293) := Fin.ext h48
    subst c
    exact classPairList_sound_48
  by_cases h49 : c.1 = 49
  · have hc : c = (49 : Fin 293) := Fin.ext h49
    subst c
    exact classPairList_sound_49
  by_cases h50 : c.1 = 50
  · have hc : c = (50 : Fin 293) := Fin.ext h50
    subst c
    exact classPairList_sound_50
  by_cases h51 : c.1 = 51
  · have hc : c = (51 : Fin 293) := Fin.ext h51
    subst c
    exact classPairList_sound_51
  by_cases h52 : c.1 = 52
  · have hc : c = (52 : Fin 293) := Fin.ext h52
    subst c
    exact classPairList_sound_52
  by_cases h53 : c.1 = 53
  · have hc : c = (53 : Fin 293) := Fin.ext h53
    subst c
    exact classPairList_sound_53
  by_cases h54 : c.1 = 54
  · have hc : c = (54 : Fin 293) := Fin.ext h54
    subst c
    exact classPairList_sound_54
  by_cases h55 : c.1 = 55
  · have hc : c = (55 : Fin 293) := Fin.ext h55
    subst c
    exact classPairList_sound_55
  by_cases h56 : c.1 = 56
  · have hc : c = (56 : Fin 293) := Fin.ext h56
    subst c
    exact classPairList_sound_56
  by_cases h57 : c.1 = 57
  · have hc : c = (57 : Fin 293) := Fin.ext h57
    subst c
    exact classPairList_sound_57
  by_cases h58 : c.1 = 58
  · have hc : c = (58 : Fin 293) := Fin.ext h58
    subst c
    exact classPairList_sound_58
  by_cases h59 : c.1 = 59
  · have hc : c = (59 : Fin 293) := Fin.ext h59
    subst c
    exact classPairList_sound_59
  by_cases h60 : c.1 = 60
  · have hc : c = (60 : Fin 293) := Fin.ext h60
    subst c
    exact classPairList_sound_60
  by_cases h61 : c.1 = 61
  · have hc : c = (61 : Fin 293) := Fin.ext h61
    subst c
    exact classPairList_sound_61
  by_cases h62 : c.1 = 62
  · have hc : c = (62 : Fin 293) := Fin.ext h62
    subst c
    exact classPairList_sound_62
  have hc : c = (63 : Fin 293) := Fin.ext (by lia)
  subst c
  exact classPairList_sound_63

private theorem classPairList_sound_64_96 (c : Fin 293)
    (hlo : 64 ≤ c.1) (hhi : c.1 < 96) :
    (classPairList c).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = c) := by
  by_cases h64 : c.1 = 64
  · have hc : c = (64 : Fin 293) := Fin.ext h64
    subst c
    exact classPairList_sound_64
  by_cases h65 : c.1 = 65
  · have hc : c = (65 : Fin 293) := Fin.ext h65
    subst c
    exact classPairList_sound_65
  by_cases h66 : c.1 = 66
  · have hc : c = (66 : Fin 293) := Fin.ext h66
    subst c
    exact classPairList_sound_66
  by_cases h67 : c.1 = 67
  · have hc : c = (67 : Fin 293) := Fin.ext h67
    subst c
    exact classPairList_sound_67
  by_cases h68 : c.1 = 68
  · have hc : c = (68 : Fin 293) := Fin.ext h68
    subst c
    exact classPairList_sound_68
  by_cases h69 : c.1 = 69
  · have hc : c = (69 : Fin 293) := Fin.ext h69
    subst c
    exact classPairList_sound_69
  by_cases h70 : c.1 = 70
  · have hc : c = (70 : Fin 293) := Fin.ext h70
    subst c
    exact classPairList_sound_70
  by_cases h71 : c.1 = 71
  · have hc : c = (71 : Fin 293) := Fin.ext h71
    subst c
    exact classPairList_sound_71
  by_cases h72 : c.1 = 72
  · have hc : c = (72 : Fin 293) := Fin.ext h72
    subst c
    exact classPairList_sound_72
  by_cases h73 : c.1 = 73
  · have hc : c = (73 : Fin 293) := Fin.ext h73
    subst c
    exact classPairList_sound_73
  by_cases h74 : c.1 = 74
  · have hc : c = (74 : Fin 293) := Fin.ext h74
    subst c
    exact classPairList_sound_74
  by_cases h75 : c.1 = 75
  · have hc : c = (75 : Fin 293) := Fin.ext h75
    subst c
    exact classPairList_sound_75
  by_cases h76 : c.1 = 76
  · have hc : c = (76 : Fin 293) := Fin.ext h76
    subst c
    exact classPairList_sound_76
  by_cases h77 : c.1 = 77
  · have hc : c = (77 : Fin 293) := Fin.ext h77
    subst c
    exact classPairList_sound_77
  by_cases h78 : c.1 = 78
  · have hc : c = (78 : Fin 293) := Fin.ext h78
    subst c
    exact classPairList_sound_78
  by_cases h79 : c.1 = 79
  · have hc : c = (79 : Fin 293) := Fin.ext h79
    subst c
    exact classPairList_sound_79
  by_cases h80 : c.1 = 80
  · have hc : c = (80 : Fin 293) := Fin.ext h80
    subst c
    exact classPairList_sound_80
  by_cases h81 : c.1 = 81
  · have hc : c = (81 : Fin 293) := Fin.ext h81
    subst c
    exact classPairList_sound_81
  by_cases h82 : c.1 = 82
  · have hc : c = (82 : Fin 293) := Fin.ext h82
    subst c
    exact classPairList_sound_82
  by_cases h83 : c.1 = 83
  · have hc : c = (83 : Fin 293) := Fin.ext h83
    subst c
    exact classPairList_sound_83
  by_cases h84 : c.1 = 84
  · have hc : c = (84 : Fin 293) := Fin.ext h84
    subst c
    exact classPairList_sound_84
  by_cases h85 : c.1 = 85
  · have hc : c = (85 : Fin 293) := Fin.ext h85
    subst c
    exact classPairList_sound_85
  by_cases h86 : c.1 = 86
  · have hc : c = (86 : Fin 293) := Fin.ext h86
    subst c
    exact classPairList_sound_86
  by_cases h87 : c.1 = 87
  · have hc : c = (87 : Fin 293) := Fin.ext h87
    subst c
    exact classPairList_sound_87
  by_cases h88 : c.1 = 88
  · have hc : c = (88 : Fin 293) := Fin.ext h88
    subst c
    exact classPairList_sound_88
  by_cases h89 : c.1 = 89
  · have hc : c = (89 : Fin 293) := Fin.ext h89
    subst c
    exact classPairList_sound_89
  by_cases h90 : c.1 = 90
  · have hc : c = (90 : Fin 293) := Fin.ext h90
    subst c
    exact classPairList_sound_90
  by_cases h91 : c.1 = 91
  · have hc : c = (91 : Fin 293) := Fin.ext h91
    subst c
    exact classPairList_sound_91
  by_cases h92 : c.1 = 92
  · have hc : c = (92 : Fin 293) := Fin.ext h92
    subst c
    exact classPairList_sound_92
  by_cases h93 : c.1 = 93
  · have hc : c = (93 : Fin 293) := Fin.ext h93
    subst c
    exact classPairList_sound_93
  by_cases h94 : c.1 = 94
  · have hc : c = (94 : Fin 293) := Fin.ext h94
    subst c
    exact classPairList_sound_94
  have hc : c = (95 : Fin 293) := Fin.ext (by lia)
  subst c
  exact classPairList_sound_95

private theorem classPairList_sound_96_128 (c : Fin 293)
    (hlo : 96 ≤ c.1) (hhi : c.1 < 128) :
    (classPairList c).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = c) := by
  by_cases h96 : c.1 = 96
  · have hc : c = (96 : Fin 293) := Fin.ext h96
    subst c
    exact classPairList_sound_96
  by_cases h97 : c.1 = 97
  · have hc : c = (97 : Fin 293) := Fin.ext h97
    subst c
    exact classPairList_sound_97
  by_cases h98 : c.1 = 98
  · have hc : c = (98 : Fin 293) := Fin.ext h98
    subst c
    exact classPairList_sound_98
  by_cases h99 : c.1 = 99
  · have hc : c = (99 : Fin 293) := Fin.ext h99
    subst c
    exact classPairList_sound_99
  by_cases h100 : c.1 = 100
  · have hc : c = (100 : Fin 293) := Fin.ext h100
    subst c
    exact classPairList_sound_100
  by_cases h101 : c.1 = 101
  · have hc : c = (101 : Fin 293) := Fin.ext h101
    subst c
    exact classPairList_sound_101
  by_cases h102 : c.1 = 102
  · have hc : c = (102 : Fin 293) := Fin.ext h102
    subst c
    exact classPairList_sound_102
  by_cases h103 : c.1 = 103
  · have hc : c = (103 : Fin 293) := Fin.ext h103
    subst c
    exact classPairList_sound_103
  by_cases h104 : c.1 = 104
  · have hc : c = (104 : Fin 293) := Fin.ext h104
    subst c
    exact classPairList_sound_104
  by_cases h105 : c.1 = 105
  · have hc : c = (105 : Fin 293) := Fin.ext h105
    subst c
    exact classPairList_sound_105
  by_cases h106 : c.1 = 106
  · have hc : c = (106 : Fin 293) := Fin.ext h106
    subst c
    exact classPairList_sound_106
  by_cases h107 : c.1 = 107
  · have hc : c = (107 : Fin 293) := Fin.ext h107
    subst c
    exact classPairList_sound_107
  by_cases h108 : c.1 = 108
  · have hc : c = (108 : Fin 293) := Fin.ext h108
    subst c
    exact classPairList_sound_108
  by_cases h109 : c.1 = 109
  · have hc : c = (109 : Fin 293) := Fin.ext h109
    subst c
    exact classPairList_sound_109
  by_cases h110 : c.1 = 110
  · have hc : c = (110 : Fin 293) := Fin.ext h110
    subst c
    exact classPairList_sound_110
  by_cases h111 : c.1 = 111
  · have hc : c = (111 : Fin 293) := Fin.ext h111
    subst c
    exact classPairList_sound_111
  by_cases h112 : c.1 = 112
  · have hc : c = (112 : Fin 293) := Fin.ext h112
    subst c
    exact classPairList_sound_112
  by_cases h113 : c.1 = 113
  · have hc : c = (113 : Fin 293) := Fin.ext h113
    subst c
    exact classPairList_sound_113
  by_cases h114 : c.1 = 114
  · have hc : c = (114 : Fin 293) := Fin.ext h114
    subst c
    exact classPairList_sound_114
  by_cases h115 : c.1 = 115
  · have hc : c = (115 : Fin 293) := Fin.ext h115
    subst c
    exact classPairList_sound_115
  by_cases h116 : c.1 = 116
  · have hc : c = (116 : Fin 293) := Fin.ext h116
    subst c
    exact classPairList_sound_116
  by_cases h117 : c.1 = 117
  · have hc : c = (117 : Fin 293) := Fin.ext h117
    subst c
    exact classPairList_sound_117
  by_cases h118 : c.1 = 118
  · have hc : c = (118 : Fin 293) := Fin.ext h118
    subst c
    exact classPairList_sound_118
  by_cases h119 : c.1 = 119
  · have hc : c = (119 : Fin 293) := Fin.ext h119
    subst c
    exact classPairList_sound_119
  by_cases h120 : c.1 = 120
  · have hc : c = (120 : Fin 293) := Fin.ext h120
    subst c
    exact classPairList_sound_120
  by_cases h121 : c.1 = 121
  · have hc : c = (121 : Fin 293) := Fin.ext h121
    subst c
    exact classPairList_sound_121
  by_cases h122 : c.1 = 122
  · have hc : c = (122 : Fin 293) := Fin.ext h122
    subst c
    exact classPairList_sound_122
  by_cases h123 : c.1 = 123
  · have hc : c = (123 : Fin 293) := Fin.ext h123
    subst c
    exact classPairList_sound_123
  by_cases h124 : c.1 = 124
  · have hc : c = (124 : Fin 293) := Fin.ext h124
    subst c
    exact classPairList_sound_124
  by_cases h125 : c.1 = 125
  · have hc : c = (125 : Fin 293) := Fin.ext h125
    subst c
    exact classPairList_sound_125
  by_cases h126 : c.1 = 126
  · have hc : c = (126 : Fin 293) := Fin.ext h126
    subst c
    exact classPairList_sound_126
  have hc : c = (127 : Fin 293) := Fin.ext (by lia)
  subst c
  exact classPairList_sound_127

private theorem classPairList_sound_128_160 (c : Fin 293)
    (hlo : 128 ≤ c.1) (hhi : c.1 < 160) :
    (classPairList c).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = c) := by
  by_cases h128 : c.1 = 128
  · have hc : c = (128 : Fin 293) := Fin.ext h128
    subst c
    exact classPairList_sound_128
  by_cases h129 : c.1 = 129
  · have hc : c = (129 : Fin 293) := Fin.ext h129
    subst c
    exact classPairList_sound_129
  by_cases h130 : c.1 = 130
  · have hc : c = (130 : Fin 293) := Fin.ext h130
    subst c
    exact classPairList_sound_130
  by_cases h131 : c.1 = 131
  · have hc : c = (131 : Fin 293) := Fin.ext h131
    subst c
    exact classPairList_sound_131
  by_cases h132 : c.1 = 132
  · have hc : c = (132 : Fin 293) := Fin.ext h132
    subst c
    exact classPairList_sound_132
  by_cases h133 : c.1 = 133
  · have hc : c = (133 : Fin 293) := Fin.ext h133
    subst c
    exact classPairList_sound_133
  by_cases h134 : c.1 = 134
  · have hc : c = (134 : Fin 293) := Fin.ext h134
    subst c
    exact classPairList_sound_134
  by_cases h135 : c.1 = 135
  · have hc : c = (135 : Fin 293) := Fin.ext h135
    subst c
    exact classPairList_sound_135
  by_cases h136 : c.1 = 136
  · have hc : c = (136 : Fin 293) := Fin.ext h136
    subst c
    exact classPairList_sound_136
  by_cases h137 : c.1 = 137
  · have hc : c = (137 : Fin 293) := Fin.ext h137
    subst c
    exact classPairList_sound_137
  by_cases h138 : c.1 = 138
  · have hc : c = (138 : Fin 293) := Fin.ext h138
    subst c
    exact classPairList_sound_138
  by_cases h139 : c.1 = 139
  · have hc : c = (139 : Fin 293) := Fin.ext h139
    subst c
    exact classPairList_sound_139
  by_cases h140 : c.1 = 140
  · have hc : c = (140 : Fin 293) := Fin.ext h140
    subst c
    exact classPairList_sound_140
  by_cases h141 : c.1 = 141
  · have hc : c = (141 : Fin 293) := Fin.ext h141
    subst c
    exact classPairList_sound_141
  by_cases h142 : c.1 = 142
  · have hc : c = (142 : Fin 293) := Fin.ext h142
    subst c
    exact classPairList_sound_142
  by_cases h143 : c.1 = 143
  · have hc : c = (143 : Fin 293) := Fin.ext h143
    subst c
    exact classPairList_sound_143
  by_cases h144 : c.1 = 144
  · have hc : c = (144 : Fin 293) := Fin.ext h144
    subst c
    exact classPairList_sound_144
  by_cases h145 : c.1 = 145
  · have hc : c = (145 : Fin 293) := Fin.ext h145
    subst c
    exact classPairList_sound_145
  by_cases h146 : c.1 = 146
  · have hc : c = (146 : Fin 293) := Fin.ext h146
    subst c
    exact classPairList_sound_146
  by_cases h147 : c.1 = 147
  · have hc : c = (147 : Fin 293) := Fin.ext h147
    subst c
    exact classPairList_sound_147
  by_cases h148 : c.1 = 148
  · have hc : c = (148 : Fin 293) := Fin.ext h148
    subst c
    exact classPairList_sound_148
  by_cases h149 : c.1 = 149
  · have hc : c = (149 : Fin 293) := Fin.ext h149
    subst c
    exact classPairList_sound_149
  by_cases h150 : c.1 = 150
  · have hc : c = (150 : Fin 293) := Fin.ext h150
    subst c
    exact classPairList_sound_150
  by_cases h151 : c.1 = 151
  · have hc : c = (151 : Fin 293) := Fin.ext h151
    subst c
    exact classPairList_sound_151
  by_cases h152 : c.1 = 152
  · have hc : c = (152 : Fin 293) := Fin.ext h152
    subst c
    exact classPairList_sound_152
  by_cases h153 : c.1 = 153
  · have hc : c = (153 : Fin 293) := Fin.ext h153
    subst c
    exact classPairList_sound_153
  by_cases h154 : c.1 = 154
  · have hc : c = (154 : Fin 293) := Fin.ext h154
    subst c
    exact classPairList_sound_154
  by_cases h155 : c.1 = 155
  · have hc : c = (155 : Fin 293) := Fin.ext h155
    subst c
    exact classPairList_sound_155
  by_cases h156 : c.1 = 156
  · have hc : c = (156 : Fin 293) := Fin.ext h156
    subst c
    exact classPairList_sound_156
  by_cases h157 : c.1 = 157
  · have hc : c = (157 : Fin 293) := Fin.ext h157
    subst c
    exact classPairList_sound_157
  by_cases h158 : c.1 = 158
  · have hc : c = (158 : Fin 293) := Fin.ext h158
    subst c
    exact classPairList_sound_158
  have hc : c = (159 : Fin 293) := Fin.ext (by lia)
  subst c
  exact classPairList_sound_159

private theorem classPairList_sound_160_192 (c : Fin 293)
    (hlo : 160 ≤ c.1) (hhi : c.1 < 192) :
    (classPairList c).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = c) := by
  by_cases h160 : c.1 = 160
  · have hc : c = (160 : Fin 293) := Fin.ext h160
    subst c
    exact classPairList_sound_160
  by_cases h161 : c.1 = 161
  · have hc : c = (161 : Fin 293) := Fin.ext h161
    subst c
    exact classPairList_sound_161
  by_cases h162 : c.1 = 162
  · have hc : c = (162 : Fin 293) := Fin.ext h162
    subst c
    exact classPairList_sound_162
  by_cases h163 : c.1 = 163
  · have hc : c = (163 : Fin 293) := Fin.ext h163
    subst c
    exact classPairList_sound_163
  by_cases h164 : c.1 = 164
  · have hc : c = (164 : Fin 293) := Fin.ext h164
    subst c
    exact classPairList_sound_164
  by_cases h165 : c.1 = 165
  · have hc : c = (165 : Fin 293) := Fin.ext h165
    subst c
    exact classPairList_sound_165
  by_cases h166 : c.1 = 166
  · have hc : c = (166 : Fin 293) := Fin.ext h166
    subst c
    exact classPairList_sound_166
  by_cases h167 : c.1 = 167
  · have hc : c = (167 : Fin 293) := Fin.ext h167
    subst c
    exact classPairList_sound_167
  by_cases h168 : c.1 = 168
  · have hc : c = (168 : Fin 293) := Fin.ext h168
    subst c
    exact classPairList_sound_168
  by_cases h169 : c.1 = 169
  · have hc : c = (169 : Fin 293) := Fin.ext h169
    subst c
    exact classPairList_sound_169
  by_cases h170 : c.1 = 170
  · have hc : c = (170 : Fin 293) := Fin.ext h170
    subst c
    exact classPairList_sound_170
  by_cases h171 : c.1 = 171
  · have hc : c = (171 : Fin 293) := Fin.ext h171
    subst c
    exact classPairList_sound_171
  by_cases h172 : c.1 = 172
  · have hc : c = (172 : Fin 293) := Fin.ext h172
    subst c
    exact classPairList_sound_172
  by_cases h173 : c.1 = 173
  · have hc : c = (173 : Fin 293) := Fin.ext h173
    subst c
    exact classPairList_sound_173
  by_cases h174 : c.1 = 174
  · have hc : c = (174 : Fin 293) := Fin.ext h174
    subst c
    exact classPairList_sound_174
  by_cases h175 : c.1 = 175
  · have hc : c = (175 : Fin 293) := Fin.ext h175
    subst c
    exact classPairList_sound_175
  by_cases h176 : c.1 = 176
  · have hc : c = (176 : Fin 293) := Fin.ext h176
    subst c
    exact classPairList_sound_176
  by_cases h177 : c.1 = 177
  · have hc : c = (177 : Fin 293) := Fin.ext h177
    subst c
    exact classPairList_sound_177
  by_cases h178 : c.1 = 178
  · have hc : c = (178 : Fin 293) := Fin.ext h178
    subst c
    exact classPairList_sound_178
  by_cases h179 : c.1 = 179
  · have hc : c = (179 : Fin 293) := Fin.ext h179
    subst c
    exact classPairList_sound_179
  by_cases h180 : c.1 = 180
  · have hc : c = (180 : Fin 293) := Fin.ext h180
    subst c
    exact classPairList_sound_180
  by_cases h181 : c.1 = 181
  · have hc : c = (181 : Fin 293) := Fin.ext h181
    subst c
    exact classPairList_sound_181
  by_cases h182 : c.1 = 182
  · have hc : c = (182 : Fin 293) := Fin.ext h182
    subst c
    exact classPairList_sound_182
  by_cases h183 : c.1 = 183
  · have hc : c = (183 : Fin 293) := Fin.ext h183
    subst c
    exact classPairList_sound_183
  by_cases h184 : c.1 = 184
  · have hc : c = (184 : Fin 293) := Fin.ext h184
    subst c
    exact classPairList_sound_184
  by_cases h185 : c.1 = 185
  · have hc : c = (185 : Fin 293) := Fin.ext h185
    subst c
    exact classPairList_sound_185
  by_cases h186 : c.1 = 186
  · have hc : c = (186 : Fin 293) := Fin.ext h186
    subst c
    exact classPairList_sound_186
  by_cases h187 : c.1 = 187
  · have hc : c = (187 : Fin 293) := Fin.ext h187
    subst c
    exact classPairList_sound_187
  by_cases h188 : c.1 = 188
  · have hc : c = (188 : Fin 293) := Fin.ext h188
    subst c
    exact classPairList_sound_188
  by_cases h189 : c.1 = 189
  · have hc : c = (189 : Fin 293) := Fin.ext h189
    subst c
    exact classPairList_sound_189
  by_cases h190 : c.1 = 190
  · have hc : c = (190 : Fin 293) := Fin.ext h190
    subst c
    exact classPairList_sound_190
  have hc : c = (191 : Fin 293) := Fin.ext (by lia)
  subst c
  exact classPairList_sound_191

private theorem classPairList_sound_192_224 (c : Fin 293)
    (hlo : 192 ≤ c.1) (hhi : c.1 < 224) :
    (classPairList c).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = c) := by
  by_cases h192 : c.1 = 192
  · have hc : c = (192 : Fin 293) := Fin.ext h192
    subst c
    exact classPairList_sound_192
  by_cases h193 : c.1 = 193
  · have hc : c = (193 : Fin 293) := Fin.ext h193
    subst c
    exact classPairList_sound_193
  by_cases h194 : c.1 = 194
  · have hc : c = (194 : Fin 293) := Fin.ext h194
    subst c
    exact classPairList_sound_194
  by_cases h195 : c.1 = 195
  · have hc : c = (195 : Fin 293) := Fin.ext h195
    subst c
    exact classPairList_sound_195
  by_cases h196 : c.1 = 196
  · have hc : c = (196 : Fin 293) := Fin.ext h196
    subst c
    exact classPairList_sound_196
  by_cases h197 : c.1 = 197
  · have hc : c = (197 : Fin 293) := Fin.ext h197
    subst c
    exact classPairList_sound_197
  by_cases h198 : c.1 = 198
  · have hc : c = (198 : Fin 293) := Fin.ext h198
    subst c
    exact classPairList_sound_198
  by_cases h199 : c.1 = 199
  · have hc : c = (199 : Fin 293) := Fin.ext h199
    subst c
    exact classPairList_sound_199
  by_cases h200 : c.1 = 200
  · have hc : c = (200 : Fin 293) := Fin.ext h200
    subst c
    exact classPairList_sound_200
  by_cases h201 : c.1 = 201
  · have hc : c = (201 : Fin 293) := Fin.ext h201
    subst c
    exact classPairList_sound_201
  by_cases h202 : c.1 = 202
  · have hc : c = (202 : Fin 293) := Fin.ext h202
    subst c
    exact classPairList_sound_202
  by_cases h203 : c.1 = 203
  · have hc : c = (203 : Fin 293) := Fin.ext h203
    subst c
    exact classPairList_sound_203
  by_cases h204 : c.1 = 204
  · have hc : c = (204 : Fin 293) := Fin.ext h204
    subst c
    exact classPairList_sound_204
  by_cases h205 : c.1 = 205
  · have hc : c = (205 : Fin 293) := Fin.ext h205
    subst c
    exact classPairList_sound_205
  by_cases h206 : c.1 = 206
  · have hc : c = (206 : Fin 293) := Fin.ext h206
    subst c
    exact classPairList_sound_206
  by_cases h207 : c.1 = 207
  · have hc : c = (207 : Fin 293) := Fin.ext h207
    subst c
    exact classPairList_sound_207
  by_cases h208 : c.1 = 208
  · have hc : c = (208 : Fin 293) := Fin.ext h208
    subst c
    exact classPairList_sound_208
  by_cases h209 : c.1 = 209
  · have hc : c = (209 : Fin 293) := Fin.ext h209
    subst c
    exact classPairList_sound_209
  by_cases h210 : c.1 = 210
  · have hc : c = (210 : Fin 293) := Fin.ext h210
    subst c
    exact classPairList_sound_210
  by_cases h211 : c.1 = 211
  · have hc : c = (211 : Fin 293) := Fin.ext h211
    subst c
    exact classPairList_sound_211
  by_cases h212 : c.1 = 212
  · have hc : c = (212 : Fin 293) := Fin.ext h212
    subst c
    exact classPairList_sound_212
  by_cases h213 : c.1 = 213
  · have hc : c = (213 : Fin 293) := Fin.ext h213
    subst c
    exact classPairList_sound_213
  by_cases h214 : c.1 = 214
  · have hc : c = (214 : Fin 293) := Fin.ext h214
    subst c
    exact classPairList_sound_214
  by_cases h215 : c.1 = 215
  · have hc : c = (215 : Fin 293) := Fin.ext h215
    subst c
    exact classPairList_sound_215
  by_cases h216 : c.1 = 216
  · have hc : c = (216 : Fin 293) := Fin.ext h216
    subst c
    exact classPairList_sound_216
  by_cases h217 : c.1 = 217
  · have hc : c = (217 : Fin 293) := Fin.ext h217
    subst c
    exact classPairList_sound_217
  by_cases h218 : c.1 = 218
  · have hc : c = (218 : Fin 293) := Fin.ext h218
    subst c
    exact classPairList_sound_218
  by_cases h219 : c.1 = 219
  · have hc : c = (219 : Fin 293) := Fin.ext h219
    subst c
    exact classPairList_sound_219
  by_cases h220 : c.1 = 220
  · have hc : c = (220 : Fin 293) := Fin.ext h220
    subst c
    exact classPairList_sound_220
  by_cases h221 : c.1 = 221
  · have hc : c = (221 : Fin 293) := Fin.ext h221
    subst c
    exact classPairList_sound_221
  by_cases h222 : c.1 = 222
  · have hc : c = (222 : Fin 293) := Fin.ext h222
    subst c
    exact classPairList_sound_222
  have hc : c = (223 : Fin 293) := Fin.ext (by lia)
  subst c
  exact classPairList_sound_223

private theorem classPairList_sound_224_256 (c : Fin 293)
    (hlo : 224 ≤ c.1) (hhi : c.1 < 256) :
    (classPairList c).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = c) := by
  by_cases h224 : c.1 = 224
  · have hc : c = (224 : Fin 293) := Fin.ext h224
    subst c
    exact classPairList_sound_224
  by_cases h225 : c.1 = 225
  · have hc : c = (225 : Fin 293) := Fin.ext h225
    subst c
    exact classPairList_sound_225
  by_cases h226 : c.1 = 226
  · have hc : c = (226 : Fin 293) := Fin.ext h226
    subst c
    exact classPairList_sound_226
  by_cases h227 : c.1 = 227
  · have hc : c = (227 : Fin 293) := Fin.ext h227
    subst c
    exact classPairList_sound_227
  by_cases h228 : c.1 = 228
  · have hc : c = (228 : Fin 293) := Fin.ext h228
    subst c
    exact classPairList_sound_228
  by_cases h229 : c.1 = 229
  · have hc : c = (229 : Fin 293) := Fin.ext h229
    subst c
    exact classPairList_sound_229
  by_cases h230 : c.1 = 230
  · have hc : c = (230 : Fin 293) := Fin.ext h230
    subst c
    exact classPairList_sound_230
  by_cases h231 : c.1 = 231
  · have hc : c = (231 : Fin 293) := Fin.ext h231
    subst c
    exact classPairList_sound_231
  by_cases h232 : c.1 = 232
  · have hc : c = (232 : Fin 293) := Fin.ext h232
    subst c
    exact classPairList_sound_232
  by_cases h233 : c.1 = 233
  · have hc : c = (233 : Fin 293) := Fin.ext h233
    subst c
    exact classPairList_sound_233
  by_cases h234 : c.1 = 234
  · have hc : c = (234 : Fin 293) := Fin.ext h234
    subst c
    exact classPairList_sound_234
  by_cases h235 : c.1 = 235
  · have hc : c = (235 : Fin 293) := Fin.ext h235
    subst c
    exact classPairList_sound_235
  by_cases h236 : c.1 = 236
  · have hc : c = (236 : Fin 293) := Fin.ext h236
    subst c
    exact classPairList_sound_236
  by_cases h237 : c.1 = 237
  · have hc : c = (237 : Fin 293) := Fin.ext h237
    subst c
    exact classPairList_sound_237
  by_cases h238 : c.1 = 238
  · have hc : c = (238 : Fin 293) := Fin.ext h238
    subst c
    exact classPairList_sound_238
  by_cases h239 : c.1 = 239
  · have hc : c = (239 : Fin 293) := Fin.ext h239
    subst c
    exact classPairList_sound_239
  by_cases h240 : c.1 = 240
  · have hc : c = (240 : Fin 293) := Fin.ext h240
    subst c
    exact classPairList_sound_240
  by_cases h241 : c.1 = 241
  · have hc : c = (241 : Fin 293) := Fin.ext h241
    subst c
    exact classPairList_sound_241
  by_cases h242 : c.1 = 242
  · have hc : c = (242 : Fin 293) := Fin.ext h242
    subst c
    exact classPairList_sound_242
  by_cases h243 : c.1 = 243
  · have hc : c = (243 : Fin 293) := Fin.ext h243
    subst c
    exact classPairList_sound_243
  by_cases h244 : c.1 = 244
  · have hc : c = (244 : Fin 293) := Fin.ext h244
    subst c
    exact classPairList_sound_244
  by_cases h245 : c.1 = 245
  · have hc : c = (245 : Fin 293) := Fin.ext h245
    subst c
    exact classPairList_sound_245
  by_cases h246 : c.1 = 246
  · have hc : c = (246 : Fin 293) := Fin.ext h246
    subst c
    exact classPairList_sound_246
  by_cases h247 : c.1 = 247
  · have hc : c = (247 : Fin 293) := Fin.ext h247
    subst c
    exact classPairList_sound_247
  by_cases h248 : c.1 = 248
  · have hc : c = (248 : Fin 293) := Fin.ext h248
    subst c
    exact classPairList_sound_248
  by_cases h249 : c.1 = 249
  · have hc : c = (249 : Fin 293) := Fin.ext h249
    subst c
    exact classPairList_sound_249
  by_cases h250 : c.1 = 250
  · have hc : c = (250 : Fin 293) := Fin.ext h250
    subst c
    exact classPairList_sound_250
  by_cases h251 : c.1 = 251
  · have hc : c = (251 : Fin 293) := Fin.ext h251
    subst c
    exact classPairList_sound_251
  by_cases h252 : c.1 = 252
  · have hc : c = (252 : Fin 293) := Fin.ext h252
    subst c
    exact classPairList_sound_252
  by_cases h253 : c.1 = 253
  · have hc : c = (253 : Fin 293) := Fin.ext h253
    subst c
    exact classPairList_sound_253
  by_cases h254 : c.1 = 254
  · have hc : c = (254 : Fin 293) := Fin.ext h254
    subst c
    exact classPairList_sound_254
  have hc : c = (255 : Fin 293) := Fin.ext (by lia)
  subst c
  exact classPairList_sound_255

private theorem classPairList_sound_256_288 (c : Fin 293)
    (hlo : 256 ≤ c.1) (hhi : c.1 < 288) :
    (classPairList c).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = c) := by
  by_cases h256 : c.1 = 256
  · have hc : c = (256 : Fin 293) := Fin.ext h256
    subst c
    exact classPairList_sound_256
  by_cases h257 : c.1 = 257
  · have hc : c = (257 : Fin 293) := Fin.ext h257
    subst c
    exact classPairList_sound_257
  by_cases h258 : c.1 = 258
  · have hc : c = (258 : Fin 293) := Fin.ext h258
    subst c
    exact classPairList_sound_258
  by_cases h259 : c.1 = 259
  · have hc : c = (259 : Fin 293) := Fin.ext h259
    subst c
    exact classPairList_sound_259
  by_cases h260 : c.1 = 260
  · have hc : c = (260 : Fin 293) := Fin.ext h260
    subst c
    exact classPairList_sound_260
  by_cases h261 : c.1 = 261
  · have hc : c = (261 : Fin 293) := Fin.ext h261
    subst c
    exact classPairList_sound_261
  by_cases h262 : c.1 = 262
  · have hc : c = (262 : Fin 293) := Fin.ext h262
    subst c
    exact classPairList_sound_262
  by_cases h263 : c.1 = 263
  · have hc : c = (263 : Fin 293) := Fin.ext h263
    subst c
    exact classPairList_sound_263
  by_cases h264 : c.1 = 264
  · have hc : c = (264 : Fin 293) := Fin.ext h264
    subst c
    exact classPairList_sound_264
  by_cases h265 : c.1 = 265
  · have hc : c = (265 : Fin 293) := Fin.ext h265
    subst c
    exact classPairList_sound_265
  by_cases h266 : c.1 = 266
  · have hc : c = (266 : Fin 293) := Fin.ext h266
    subst c
    exact classPairList_sound_266
  by_cases h267 : c.1 = 267
  · have hc : c = (267 : Fin 293) := Fin.ext h267
    subst c
    exact classPairList_sound_267
  by_cases h268 : c.1 = 268
  · have hc : c = (268 : Fin 293) := Fin.ext h268
    subst c
    exact classPairList_sound_268
  by_cases h269 : c.1 = 269
  · have hc : c = (269 : Fin 293) := Fin.ext h269
    subst c
    exact classPairList_sound_269
  by_cases h270 : c.1 = 270
  · have hc : c = (270 : Fin 293) := Fin.ext h270
    subst c
    exact classPairList_sound_270
  by_cases h271 : c.1 = 271
  · have hc : c = (271 : Fin 293) := Fin.ext h271
    subst c
    exact classPairList_sound_271
  by_cases h272 : c.1 = 272
  · have hc : c = (272 : Fin 293) := Fin.ext h272
    subst c
    exact classPairList_sound_272
  by_cases h273 : c.1 = 273
  · have hc : c = (273 : Fin 293) := Fin.ext h273
    subst c
    exact classPairList_sound_273
  by_cases h274 : c.1 = 274
  · have hc : c = (274 : Fin 293) := Fin.ext h274
    subst c
    exact classPairList_sound_274
  by_cases h275 : c.1 = 275
  · have hc : c = (275 : Fin 293) := Fin.ext h275
    subst c
    exact classPairList_sound_275
  by_cases h276 : c.1 = 276
  · have hc : c = (276 : Fin 293) := Fin.ext h276
    subst c
    exact classPairList_sound_276
  by_cases h277 : c.1 = 277
  · have hc : c = (277 : Fin 293) := Fin.ext h277
    subst c
    exact classPairList_sound_277
  by_cases h278 : c.1 = 278
  · have hc : c = (278 : Fin 293) := Fin.ext h278
    subst c
    exact classPairList_sound_278
  by_cases h279 : c.1 = 279
  · have hc : c = (279 : Fin 293) := Fin.ext h279
    subst c
    exact classPairList_sound_279
  by_cases h280 : c.1 = 280
  · have hc : c = (280 : Fin 293) := Fin.ext h280
    subst c
    exact classPairList_sound_280
  by_cases h281 : c.1 = 281
  · have hc : c = (281 : Fin 293) := Fin.ext h281
    subst c
    exact classPairList_sound_281
  by_cases h282 : c.1 = 282
  · have hc : c = (282 : Fin 293) := Fin.ext h282
    subst c
    exact classPairList_sound_282
  by_cases h283 : c.1 = 283
  · have hc : c = (283 : Fin 293) := Fin.ext h283
    subst c
    exact classPairList_sound_283
  by_cases h284 : c.1 = 284
  · have hc : c = (284 : Fin 293) := Fin.ext h284
    subst c
    exact classPairList_sound_284
  by_cases h285 : c.1 = 285
  · have hc : c = (285 : Fin 293) := Fin.ext h285
    subst c
    exact classPairList_sound_285
  by_cases h286 : c.1 = 286
  · have hc : c = (286 : Fin 293) := Fin.ext h286
    subst c
    exact classPairList_sound_286
  have hc : c = (287 : Fin 293) := Fin.ext (by lia)
  subst c
  exact classPairList_sound_287

private theorem classPairList_sound_288_293 (c : Fin 293)
    (hlo : 288 ≤ c.1) (hhi : c.1 < 293) :
    (classPairList c).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = c) := by
  by_cases h288 : c.1 = 288
  · have hc : c = (288 : Fin 293) := Fin.ext h288
    subst c
    exact classPairList_sound_288
  by_cases h289 : c.1 = 289
  · have hc : c = (289 : Fin 293) := Fin.ext h289
    subst c
    exact classPairList_sound_289
  by_cases h290 : c.1 = 290
  · have hc : c = (290 : Fin 293) := Fin.ext h290
    subst c
    exact classPairList_sound_290
  by_cases h291 : c.1 = 291
  · have hc : c = (291 : Fin 293) := Fin.ext h291
    subst c
    exact classPairList_sound_291
  have hc : c = (292 : Fin 293) := Fin.ext (by lia)
  subst c
  exact classPairList_sound_292

private theorem classPairList_sound (c : Fin 293) :
    (classPairList c).Forall
      (fun pair ↦ productClassIndex pair.1 pair.2 = c) := by
  by_cases h0 : c.1 < 32
  · exact classPairList_sound_0_32 c (by lia) h0
  by_cases h32 : c.1 < 64
  · exact classPairList_sound_32_64 c (by lia) h32
  by_cases h64 : c.1 < 96
  · exact classPairList_sound_64_96 c (by lia) h64
  by_cases h96 : c.1 < 128
  · exact classPairList_sound_96_128 c (by lia) h96
  by_cases h128 : c.1 < 160
  · exact classPairList_sound_128_160 c (by lia) h128
  by_cases h160 : c.1 < 192
  · exact classPairList_sound_160_192 c (by lia) h160
  by_cases h192 : c.1 < 224
  · exact classPairList_sound_192_224 c (by lia) h192
  by_cases h224 : c.1 < 256
  · exact classPairList_sound_224_256 c (by lia) h224
  by_cases h256 : c.1 < 288
  · exact classPairList_sound_256_288 c (by lia) h256
  exact classPairList_sound_288_293 c (by lia) (by lia)

/-- Every pair stored in a sparse fiber has that fiber's class. -/
theorem classPairs_sound (c : Fin 293) (pair : Fin 22 × Fin 22)
    (hpair : pair ∈ classPairs c) :
    productClassIndex pair.1 pair.2 = c := by
  have hlist : pair ∈ classPairList c := by
    simpa [classPairs] using hpair
  exact (List.forall_iff_forall_mem.mp (classPairList_sound c)) pair hlist

/-- Every pair with left coordinate 0 occurs in its class fiber. -/
private theorem classPairs_complete_left_0 (right : Fin 22) :
    (0, right) ∈ classPairs (productClassIndex 0 right) := by
  fin_cases right <;> decide

/-- Every pair with left coordinate 1 occurs in its class fiber. -/
private theorem classPairs_complete_left_1 (right : Fin 22) :
    (1, right) ∈ classPairs (productClassIndex 1 right) := by
  fin_cases right <;> decide

/-- Every pair with left coordinate 2 occurs in its class fiber. -/
private theorem classPairs_complete_left_2 (right : Fin 22) :
    (2, right) ∈ classPairs (productClassIndex 2 right) := by
  fin_cases right <;> decide

/-- Every pair with left coordinate 3 occurs in its class fiber. -/
private theorem classPairs_complete_left_3 (right : Fin 22) :
    (3, right) ∈ classPairs (productClassIndex 3 right) := by
  fin_cases right <;> decide

/-- Every pair with left coordinate 4 occurs in its class fiber. -/
private theorem classPairs_complete_left_4 (right : Fin 22) :
    (4, right) ∈ classPairs (productClassIndex 4 right) := by
  fin_cases right <;> decide

/-- Every pair with left coordinate 5 occurs in its class fiber. -/
private theorem classPairs_complete_left_5 (right : Fin 22) :
    (5, right) ∈ classPairs (productClassIndex 5 right) := by
  fin_cases right <;> decide

/-- Every pair with left coordinate 6 occurs in its class fiber. -/
private theorem classPairs_complete_left_6 (right : Fin 22) :
    (6, right) ∈ classPairs (productClassIndex 6 right) := by
  fin_cases right <;> decide

/-- Every pair with left coordinate 7 occurs in its class fiber. -/
private theorem classPairs_complete_left_7 (right : Fin 22) :
    (7, right) ∈ classPairs (productClassIndex 7 right) := by
  fin_cases right <;> decide

/-- Every pair with left coordinate 8 occurs in its class fiber. -/
private theorem classPairs_complete_left_8 (right : Fin 22) :
    (8, right) ∈ classPairs (productClassIndex 8 right) := by
  fin_cases right <;> decide

/-- Every pair with left coordinate 9 occurs in its class fiber. -/
private theorem classPairs_complete_left_9 (right : Fin 22) :
    (9, right) ∈ classPairs (productClassIndex 9 right) := by
  fin_cases right <;> decide

/-- Every pair with left coordinate 10 occurs in its class fiber. -/
private theorem classPairs_complete_left_10 (right : Fin 22) :
    (10, right) ∈ classPairs (productClassIndex 10 right) := by
  fin_cases right <;> decide

/-- Every pair with left coordinate 11 occurs in its class fiber. -/
private theorem classPairs_complete_left_11 (right : Fin 22) :
    (11, right) ∈ classPairs (productClassIndex 11 right) := by
  fin_cases right <;> decide

/-- Every pair with left coordinate 12 occurs in its class fiber. -/
private theorem classPairs_complete_left_12 (right : Fin 22) :
    (12, right) ∈ classPairs (productClassIndex 12 right) := by
  fin_cases right <;> decide

/-- Every pair with left coordinate 13 occurs in its class fiber. -/
private theorem classPairs_complete_left_13 (right : Fin 22) :
    (13, right) ∈ classPairs (productClassIndex 13 right) := by
  fin_cases right <;> decide

/-- Every pair with left coordinate 14 occurs in its class fiber. -/
private theorem classPairs_complete_left_14 (right : Fin 22) :
    (14, right) ∈ classPairs (productClassIndex 14 right) := by
  fin_cases right <;> decide

/-- Every pair with left coordinate 15 occurs in its class fiber. -/
private theorem classPairs_complete_left_15 (right : Fin 22) :
    (15, right) ∈ classPairs (productClassIndex 15 right) := by
  fin_cases right <;> decide

/-- Every pair with left coordinate 16 occurs in its class fiber. -/
private theorem classPairs_complete_left_16 (right : Fin 22) :
    (16, right) ∈ classPairs (productClassIndex 16 right) := by
  fin_cases right <;> decide

/-- Every pair with left coordinate 17 occurs in its class fiber. -/
private theorem classPairs_complete_left_17 (right : Fin 22) :
    (17, right) ∈ classPairs (productClassIndex 17 right) := by
  fin_cases right <;> decide

/-- Every pair with left coordinate 18 occurs in its class fiber. -/
private theorem classPairs_complete_left_18 (right : Fin 22) :
    (18, right) ∈ classPairs (productClassIndex 18 right) := by
  fin_cases right <;> decide

/-- Every pair with left coordinate 19 occurs in its class fiber. -/
private theorem classPairs_complete_left_19 (right : Fin 22) :
    (19, right) ∈ classPairs (productClassIndex 19 right) := by
  fin_cases right <;> decide

/-- Every pair with left coordinate 20 occurs in its class fiber. -/
private theorem classPairs_complete_left_20 (right : Fin 22) :
    (20, right) ∈ classPairs (productClassIndex 20 right) := by
  fin_cases right <;> decide

/-- Every pair with left coordinate 21 occurs in its class fiber. -/
private theorem classPairs_complete_left_21 (right : Fin 22) :
    (21, right) ∈ classPairs (productClassIndex 21 right) := by
  fin_cases right <;> decide

/-- Every support pair occurs in the sparse fiber selected by the replay table. -/
theorem classPairs_complete (left right : Fin 22) :
    (left, right) ∈ classPairs (productClassIndex left right) := by
  fin_cases left
  · exact classPairs_complete_left_0 right
  · exact classPairs_complete_left_1 right
  · exact classPairs_complete_left_2 right
  · exact classPairs_complete_left_3 right
  · exact classPairs_complete_left_4 right
  · exact classPairs_complete_left_5 right
  · exact classPairs_complete_left_6 right
  · exact classPairs_complete_left_7 right
  · exact classPairs_complete_left_8 right
  · exact classPairs_complete_left_9 right
  · exact classPairs_complete_left_10 right
  · exact classPairs_complete_left_11 right
  · exact classPairs_complete_left_12 right
  · exact classPairs_complete_left_13 right
  · exact classPairs_complete_left_14 right
  · exact classPairs_complete_left_15 right
  · exact classPairs_complete_left_16 right
  · exact classPairs_complete_left_17 right
  · exact classPairs_complete_left_18 right
  · exact classPairs_complete_left_19 right
  · exact classPairs_complete_left_20 right
  · exact classPairs_complete_left_21 right

/-- Every sparse fiber is exactly the corresponding replay-table fiber. -/
theorem classPairs_eq_filter (c : Fin 293) :
    classPairs c =
      (Finset.univ : Finset (Fin 22 × Fin 22)).filter
        (fun pair ↦ productClassIndex pair.1 pair.2 = c) := by
  ext pair
  constructor
  · intro hpair
    simpa using classPairs_sound c pair hpair
  · intro hpair
    have hclass : productClassIndex pair.1 pair.2 = c := by
      simpa using hpair
    simpa [hclass] using classPairs_complete pair.1 pair.2

/-- Reindex a collected convolution by its sparse fiber. -/
theorem convolution_eq_classPairs
    {R : Type*} [CommRing R]
    (left right : Fin 22 → R) (c : Fin 293) :
    (∑ a, ∑ b, if productClassIndex a b = c then
        left a * right b else 0) =
      ∑ pair ∈ classPairs c, left pair.1 * right pair.2 := by
  classical
  calc
    (∑ a, ∑ b, if productClassIndex a b = c then
        left a * right b else 0) =
        ∑ pair : Fin 22 × Fin 22,
          if productClassIndex pair.1 pair.2 = c then
            left pair.1 * right pair.2 else 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ pair ∈ classPairs c, left pair.1 * right pair.2 := by
      rw [classPairs_eq_filter, Finset.sum_filter]

/-- Integer specialization used by exact numerator computations. -/
theorem integerConvolution_eq_classPairs
    (left right : Fin 22 → ℤ) (c : Fin 293) :
    (∑ a, ∑ b, if productClassIndex a b = c then
        left a * right b else 0) =
      ∑ pair ∈ classPairs c, left pair.1 * right pair.2 :=
  convolution_eq_classPairs left right c

end LiteralP13HodgePairTable
end GroupApproximation

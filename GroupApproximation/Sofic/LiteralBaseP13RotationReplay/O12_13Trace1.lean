import GroupApproximation.Sofic.LiteralBaseP13RotationReplay
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O31_32

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem o12_13Trace1 :
    rotationWord (word (rotationSignedWord "YxzYzYXYxyZXyyxyZX")) =
      rotationWord (word (rotationSignedWord "")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "YxzYzYXYxyZXYxyZX")) :=
      rotationStep "YxzYzYXYxyZXyyxyZX" "YxzYzYXYxyZXYxyZX" "YxzYzYXYxyZX" 1 false
    _ = rotationWord (word (rotationSignedWord "YxzYzYXYXXyZXYxyZX")) :=
      rotationStep "YxzYzYXYxyZXYxyZX" "YxzYzYXYXXyZXYxyZX" "YxzYzYXY" 0 false
    _ = rotationWord (word (rotationSignedWord "XXzYXYYYxyZX")) :=
      rotationConsequenceStep "YxzYzYXYXXyZXYxyZX" "XXzYXYYYxyZX" "X"
        "xYxzYzYXYXXyZXyyxyZx" false (hrelation := o31_32Image_eq_one)
    _ = rotationWord (word (rotationSignedWord "XXX")) :=
      rotationStep "XXzYXYYYxyZX" "XXX" "XXzYX" 1 true
    _ = rotationWord (word (rotationSignedWord "")) :=
      rotationStep "XXX" "" "" 0 true

end

end GroupApproximation.LiteralBaseP13RotationReplay

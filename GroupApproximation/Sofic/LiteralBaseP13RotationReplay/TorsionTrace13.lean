import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.TorsionTrace12

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem torsionTrace13 :
    rotationWord (word (rotationSignedWord "YxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYX")) =
      rotationWord (word (rotationSignedWord "")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "XYXzxYXzX")) := torsionTrace12
    _ = rotationWord (word (rotationSignedWord "XYXZxYXzX")) :=
      rotationStep "XYXzxYXzX" "XYXZxYXzX" "XYX" 2 false
    _ = rotationWord (word (rotationSignedWord "XXzzX")) :=
      rotationStep "XYXZxYXzX" "XXzzX" "X" 5 true
    _ = rotationWord (word (rotationSignedWord "XXX")) :=
      rotationStep "XXzzX" "XXX" "XX" 2 false
    _ = rotationWord (word (rotationSignedWord "")) :=
      rotationStep "XXX" "" "" 0 true

end

end GroupApproximation.LiteralBaseP13RotationReplay

import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O12_32

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem torsionTrace1 :
    rotationWord (word (rotationSignedWord "YxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYX")) =
      rotationWord (word (rotationSignedWord "YxzYzxyZXYxzYzxzYzYXYxzYXZXYzYXYxzYXZXYzYX")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "YxzYXZXYZYXYxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYX")) :=
      rotationStep "YxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYX" "YxzYXZXYZYXYxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYX" "YxzYXZXY" 2 false
    _ = rotationWord (word (rotationSignedWord "YxzYzxzYZYXYxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYX")) :=
      rotationStep "YxzYXZXYZYXYxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYX" "YxzYzxzYZYXYxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYX" "YxzYX" 3 true
    _ = rotationWord (word (rotationSignedWord "YxzYzxZYZYXYxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYX")) :=
      rotationStep "YxzYzxzYZYXYxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYX" "YxzYzxZYZYXYxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYX" "YxzYzx" 2 false
    _ = rotationWord (word (rotationSignedWord "YxzYzxyzXYxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYX")) :=
      rotationStep "YxzYzxZYZYXYxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYX" "YxzYzxyzXYxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYX" "YxzYzx" 4 true
    _ = rotationWord (word (rotationSignedWord "YxzYzxyZXYxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYX")) :=
      rotationStep "YxzYzxyzXYxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYX" "YxzYzxyZXYxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYX" "YxzYzxy" 2 false
    _ = rotationWord (word (rotationSignedWord "YxzYzxyZXYxzYzxzYzYXYxzYXZXYzYXYxzYXZXYzYX")) :=
      rotationStep "YxzYzxyZXYxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYX" "YxzYzxyZXYxzYzxzYzYXYxzYXZXYzYXYxzYXZXYzYX" "YxzYzxyZXYxzYX" 3 true

end

end GroupApproximation.LiteralBaseP13RotationReplay

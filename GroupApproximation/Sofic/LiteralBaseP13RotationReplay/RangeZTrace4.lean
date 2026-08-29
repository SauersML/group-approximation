import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.RangeZTrace3

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem rangeZTrace4 :
    rotationWord (word (rotationSignedWord "YxzYXZXYXyXyZXyXYxzYzYXYXyZXyXXyZXyzYXYZ")) =
      rotationWord (word (rotationSignedWord "")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "YxzXYZYZXZxY")) := rangeZTrace3
    _ = rotationWord (word (rotationSignedWord "YxzXzyXZxY")) :=
      rotationStep "YxzXYZYZXZxY" "YxzXzyXZxY" "YxzXY" 4 true
    _ = rotationWord (word (rotationSignedWord "YxzXzyXzxY")) :=
      rotationStep "YxzXzyXZxY" "YxzXzyXzxY" "YxzXzyX" 2 true
    _ = rotationWord (word (rotationSignedWord "YxzXzXZxYY")) :=
      rotationStep "YxzXzyXzxY" "YxzXzXZxYY" "YxzXzy" 5 false
    _ = rotationWord (word (rotationSignedWord "YxzXzXZxy")) :=
      rotationStep "YxzXzXZxYY" "YxzXzXZxy" "YxzXzXZx" 1 true
    _ = rotationWord (word (rotationSignedWord "YxzXZXZxy")) :=
      rotationStep "YxzXzXZxy" "YxzXZXZxy" "YxzX" 2 false
    _ = rotationWord (word (rotationSignedWord "Yxzzxxy")) :=
      rotationStep "YxzXZXZxy" "Yxzzxxy" "YxzX" 3 true
    _ = rotationWord (word (rotationSignedWord "Yxxxy")) :=
      rotationStep "Yxzzxxy" "Yxxxy" "Yx" 2 false
    _ = rotationWord (word (rotationSignedWord "")) :=
      rotationStep "Yxxxy" "" "Y" 0 false

end

end GroupApproximation.LiteralBaseP13RotationReplay

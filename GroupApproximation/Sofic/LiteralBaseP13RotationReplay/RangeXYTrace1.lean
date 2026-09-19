import GroupApproximation.Sofic.LiteralBaseP13RotationReplay

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem rangeXYTrace1 :
    rotationWord (word (rotationSignedWord "xyZXyyxyZYxzYxYX")) =
      rotationWord (word (rotationSignedWord "")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "xyZXYxyZYxzYxYX")) :=
      rotationStep "xyZXyyxyZYxzYxYX" "xyZXYxyZYxzYxYX" "xyZX" 1 false
    _ = rotationWord (word (rotationSignedWord "xyZXYxYYZYxzYxYX")) :=
      rotationStep "xyZXYxyZYxzYxYX" "xyZXYxYYZYxzYxYX" "xyZXYx" 1 false
    _ = rotationWord (word (rotationSignedWord "xyZXYxYzyzxzYxYX")) :=
      rotationStep "xyZXYxYYZYxzYxYX" "xyZXYxYzyzxzYxYX" "xyZXYxYY" 4 true
    _ = rotationWord (word (rotationSignedWord "xyZXYYZyXzxzYxYX")) :=
      rotationStep "xyZXYxYzyzxzYxYX" "xyZXYYZyXzxzYxYX" "xyZXYx" 6 false
    _ = rotationWord (word (rotationSignedWord "xyZXyZyXzxzYxYX")) :=
      rotationStep "xyZXYYZyXzxzYxYX" "xyZXyZyXzxzYxYX" "xyZX" 1 true
    _ = rotationWord (word (rotationSignedWord "xyZXyZyXXZXYxYX")) :=
      rotationStep "xyZXyZyXzxzYxYX" "xyZXyZyXXZXYxYX" "xyZXyZyXz" 3 false
    _ = rotationWord (word (rotationSignedWord "xyZXyZyxZXYxYX")) :=
      rotationStep "xyZXyZyXXZXYxYX" "xyZXyZyxZXYxYX" "xyZXyZy" 0 true
    _ = rotationWord (word (rotationSignedWord "xyZXyzyxZXYxYX")) :=
      rotationStep "xyZXyZyxZXYxYX" "xyZXyzyxZXYxYX" "xyZXy" 2 true
    _ = rotationWord (word (rotationSignedWord "xyZXyzyxzXYxYX")) :=
      rotationStep "xyZXyzyxZXYxYX" "xyZXyzyxzXYxYX" "xyZXyzyx" 2 true
    _ = rotationWord (word (rotationSignedWord "xyZXZYZxzXYxYX")) :=
      rotationStep "xyZXyzyxzXYxYX" "xyZXZYZxzXYxYX" "xyZX" 4 false
    _ = rotationWord (word (rotationSignedWord "xyZXZYzxzXYxYX")) :=
      rotationStep "xyZXZYZxzXYxYX" "xyZXZYzxzXYxYX" "xyZXZY" 2 true
    _ = rotationWord (word (rotationSignedWord "xyZXZYXZXXYxYX")) :=
      rotationStep "xyZXZYzxzXYxYX" "xyZXZYXZXXYxYX" "xyZXZYz" 3 false
    _ = rotationWord (word (rotationSignedWord "xyZXZYXZxYxYX")) :=
      rotationStep "xyZXZYXZXXYxYX" "xyZXZYXZxYxYX" "xyZXZYXZ" 0 true
    _ = rotationWord (word (rotationSignedWord "xyZXZXzxxYX")) :=
      rotationStep "xyZXZYXZxYxYX" "xyZXZXzxxYX" "xyZXZ" 5 true
    _ = rotationWord (word (rotationSignedWord "xyxzzxxYX")) :=
      rotationStep "xyZXZXzxxYX" "xyxzzxxYX" "xy" 3 true
    _ = rotationWord (word (rotationSignedWord "xyxxxYX")) :=
      rotationStep "xyxzzxxYX" "xyxxxYX" "xyx" 2 false
    _ = rotationWord (word (rotationSignedWord "")) :=
      rotationStep "xyxxxYX" "" "xy" 0 false

end

end GroupApproximation.LiteralBaseP13RotationReplay

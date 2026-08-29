import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.S132Trace1

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem s132Trace2 :
    rotationWord (word (rotationSignedWord "xzYXYXzYXYXyxyZyxyZxxyZXy")) =
      rotationWord (word (rotationSignedWord "")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "ZXyzxZxxyZx")) := s132Trace1
    _ = rotationWord (word (rotationSignedWord "ZXyzxzxxyZx")) :=
      rotationStep "ZXyzxZxxyZx" "ZXyzxzxxyZx" "ZXyzx" 2 true
    _ = rotationWord (word (rotationSignedWord "ZXyXZxyZx")) :=
      rotationStep "ZXyzxzxxyZx" "ZXyXZxyZx" "ZXyz" 3 false
    _ = rotationWord (word (rotationSignedWord "ZXyXzxyZx")) :=
      rotationStep "ZXyXZxyZx" "ZXyXzxyZx" "ZXyX" 2 true
    _ = rotationWord (word (rotationSignedWord "ZXXZxZx")) :=
      rotationStep "ZXyXzxyZx" "ZXXZxZx" "ZXy" 5 false
    _ = rotationWord (word (rotationSignedWord "ZxZxZx")) :=
      rotationStep "ZXXZxZx" "ZxZxZx" "Z" 0 true
    _ = rotationWord (word (rotationSignedWord "zxZxZx")) :=
      rotationStep "ZxZxZx" "zxZxZx" "" 2 true
    _ = rotationWord (word (rotationSignedWord "zxzxZx")) :=
      rotationStep "zxZxZx" "zxzxZx" "zx" 2 true
    _ = rotationWord (word (rotationSignedWord "XZZx")) :=
      rotationStep "zxzxZx" "XZZx" "z" 3 false
    _ = rotationWord (word (rotationSignedWord "")) :=
      rotationStep "XZZx" "" "X" 2 true

end

end GroupApproximation.LiteralBaseP13RotationReplay

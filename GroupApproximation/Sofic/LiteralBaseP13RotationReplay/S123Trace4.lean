import GroupApproximation.Sofic.LiteralBaseP13RotationReplay
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.S123Trace3

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem s123Trace4 :
    rotationWord (word (rotationSignedWord "YxzYXXYxzYxyZXyyZXyxyxyZX")) =
      rotationWord (word (rotationSignedWord "")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "yZYxyXXZXyx")) := s123Trace3
    _ = rotationWord (word (rotationSignedWord "yZYxyXzxzyx")) :=
      rotationStep "yZYxyXXZXyx" "yZYxyXzxzyx" "yZYxyXX" 3 true
    _ = rotationWord (word (rotationSignedWord "yZYZxYzyx")) :=
      rotationStep "yZYxyXzxzyx" "yZYZxYzyx" "yZYxy" 5 false
    _ = rotationWord (word (rotationSignedWord "yZYZYZy")) :=
      rotationStep "yZYZxYzyx" "yZYZYZy" "yZYZx" 6 false
    _ = rotationWord (word (rotationSignedWord "yyy")) :=
      rotationStep "yZYZYZy" "yyy" "y" 4 true
    _ = rotationWord (word (rotationSignedWord "")) :=
      rotationStep "yyy" "" "" 1 false

end

end GroupApproximation.LiteralBaseP13RotationReplay

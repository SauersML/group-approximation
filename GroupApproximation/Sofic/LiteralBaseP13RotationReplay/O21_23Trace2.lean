import GroupApproximation.Sofic.LiteralBaseP13RotationReplay
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O21_23Trace1

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem o21_23Trace2 :
    rotationWord (word (rotationSignedWord "YxyxzXYxzYZXYXyyZXyx")) =
      rotationWord (word (rotationSignedWord "yyy")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "YxZYxYZXYXYZXyx")) := o21_23Trace1
    _ = rotationWord (word (rotationSignedWord "YxZYxYzXYXYZXyx")) :=
      rotationStep "YxZYxYZXYXYZXyx" "YxZYxYzXYXYZXyx" "YxZYxY" 2 true
    _ = rotationWord (word (rotationSignedWord "YxZyyxYzXYXYZXyx")) :=
      rotationStep "YxZYxYzXYXYZXyx" "YxZyyxYzXYXYZXyx" "YxZ" 1 true
    _ = rotationWord (word (rotationSignedWord "YxZyZyXYXYXYZXyx")) :=
      rotationStep "YxZyyxYzXYXYZXyx" "YxZyZyXYXYXYZXyx" "YxZyZy" 6 false
    _ = rotationWord (word (rotationSignedWord "YxZyZyyxyxyxZXyx")) :=
      rotationStep "YxZyZyXYXYXYZXyx" "YxZyZyyxyxyxZXyx" "YxZyZyX" 7 true
    _ = rotationWord (word (rotationSignedWord "YxZyZYxyxyxZXyx")) :=
      rotationStep "YxZyZyyxyxyxZXyx" "YxZyZYxyxyxZXyx" "YxZyZ" 1 false
    _ = rotationWord (word (rotationSignedWord "YxzyZYxyxyxZXyx")) :=
      rotationStep "YxZyZYxyxyxZXyx" "YxzyZYxyxyxZXyx" "Yx" 2 true
    _ = rotationWord (word (rotationSignedWord "YxzyzYxyxyxZXyx")) :=
      rotationStep "YxzyZYxyxyxZXyx" "YxzyzYxyxyxZXyx" "Yxzy" 2 true
    _ = rotationWord (word (rotationSignedWord "YxYZYYxyxyxZXyx")) :=
      rotationStep "YxzyzYxyxyxZXyx" "YxYZYYxyxyxZXyx" "Yxz" 4 false
    _ = rotationWord (word (rotationSignedWord "YxYZyxyxyxZXyx")) :=
      rotationStep "YxYZYYxyxyxZXyx" "YxYZyxyxyxZXyx" "YxYZ" 1 true
    _ = rotationWord (word (rotationSignedWord "YxYzyxyxyxZXyx")) :=
      rotationStep "YxYZyxyxyxZXyx" "YxYzyxyxyxZXyx" "YxY" 2 true
    _ = rotationWord (word (rotationSignedWord "YYZyyxyxZXyx")) :=
      rotationStep "YxYzyxyxyxZXyx" "YYZyyxyxZXyx" "Yx" 6 false
    _ = rotationWord (word (rotationSignedWord "YYZYxyxZXyx")) :=
      rotationStep "YYZyyxyxZXyx" "YYZYxyxZXyx" "YYZ" 1 false
    _ = rotationWord (word (rotationSignedWord "yZYxyxZXyx")) :=
      rotationStep "YYZYxyxZXyx" "yZYxyxZXyx" "" 1 true
    _ = rotationWord (word (rotationSignedWord "yZYxyXXZXyx")) :=
      rotationStep "yZYxyxZXyx" "yZYxyXXZXyx" "yZYxy" 0 false
    _ = rotationWord (word (rotationSignedWord "yZYxyXzxzyx")) :=
      rotationStep "yZYxyXXZXyx" "yZYxyXzxzyx" "yZYxyXX" 3 true
    _ = rotationWord (word (rotationSignedWord "yZYZxYzyx")) :=
      rotationStep "yZYxyXzxzyx" "yZYZxYzyx" "yZYxy" 5 false
    _ = rotationWord (word (rotationSignedWord "yZYZYZy")) :=
      rotationStep "yZYZxYzyx" "yZYZYZy" "yZYZx" 6 false
    _ = rotationWord (word (rotationSignedWord "yyy")) :=
      rotationStep "yZYZYZy" "yyy" "y" 4 true

end

end GroupApproximation.LiteralBaseP13RotationReplay

import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O21_31Trace1

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem o21_31Trace2 :
    rotationWord (word (rotationSignedWord "YxyxzxYxzYxZXYXyXyZXyX")) =
      rotationWord (word (rotationSignedWord "Yxzxzxzy")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "YxyXyyzyyxzyXyZXyX")) := o21_31Trace1
    _ = rotationWord (word (rotationSignedWord "YxyXYzyyxzyXyZXyX")) :=
      rotationStep "YxyXyyzyyxzyXyZXyX" "YxyXYzyyxzyXyZXyX" "YxyX" 1 false
    _ = rotationWord (word (rotationSignedWord "YxyXYzYxzyXyZXyX")) :=
      rotationStep "YxyXYzyyxzyXyZXyX" "YxyXYzYxzyXyZXyX" "YxyXYz" 1 false
    _ = rotationWord (word (rotationSignedWord "YxyXYZYxzyXyZXyX")) :=
      rotationStep "YxyXYzYxzyXyZXyX" "YxyXYZYxzyXyZXyX" "YxyXY" 2 false
    _ = rotationWord (word (rotationSignedWord "YxzyxYYxzyXyZXyX")) :=
      rotationStep "YxyXYZYxzyXyZXyX" "YxzyxYYxzyXyZXyX" "Yxy" 6 true
    _ = rotationWord (word (rotationSignedWord "YxzyxyxzyXyZXyX")) :=
      rotationStep "YxzyxYYxzyXyZXyX" "YxzyxyxzyXyZXyX" "Yxzyx" 1 true
    _ = rotationWord (word (rotationSignedWord "YxzyxyxZyXyZXyX")) :=
      rotationStep "YxzyxyxzyXyZXyX" "YxzyxyxZyXyZXyX" "Yxzyxyx" 2 false
    _ = rotationWord (word (rotationSignedWord "YxzyxyxZyXYYZXyX")) :=
      rotationStep "YxzyxyxZyXyZXyX" "YxzyxyxZyXYYZXyX" "YxzyxyxZyX" 1 false
    _ = rotationWord (word (rotationSignedWord "YxzyxyxyxYzYZXyX")) :=
      rotationStep "YxzyxyxZyXYYZXyX" "YxzyxyxyxYzYZXyX" "Yxzyxyxyx" 6 true
    _ = rotationWord (word (rotationSignedWord "YxzyxyxyxYZYZXyX")) :=
      rotationStep "YxzyxyxyxYzYZXyX" "YxzyxyxyxYZYZXyX" "YxzyxyxyxY" 2 false
    _ = rotationWord (word (rotationSignedWord "YxzyxyxyxzyXyX")) :=
      rotationStep "YxzyxyxyxYZYZXyX" "YxzyxyxyxzyXyX" "YxzyxyxyxY" 4 true
    _ = rotationWord (word (rotationSignedWord "YxzyxyxyxZyXyX")) :=
      rotationStep "YxzyxyxyxzyXyX" "YxzyxyxyxZyXyX" "Yxzyxyxyx" 2 false
    _ = rotationWord (word (rotationSignedWord "YxzXYXYXYZyXyX")) :=
      rotationStep "YxzyxyxyxZyXyX" "YxzXYXYXYZyXyX" "Yxzy" 7 false
    _ = rotationWord (word (rotationSignedWord "YxzXYXYYzyyX")) :=
      rotationStep "YxzXYXYXYZyXyX" "YxzXYXYYzyyX" "YxzXYXY" 6 true
    _ = rotationWord (word (rotationSignedWord "YxzXYXyzyyX")) :=
      rotationStep "YxzXYXYYzyyX" "YxzXYXyzyyX" "YxzXYX" 1 true
    _ = rotationWord (word (rotationSignedWord "YxzXYXZYZyX")) :=
      rotationStep "YxzXYXyzyyX" "YxzXYXZYZyX" "YxzXYX" 4 false
    _ = rotationWord (word (rotationSignedWord "YxzXYXZxYzy")) :=
      rotationStep "YxzXYXZYZyX" "YxzXYXZxYzy" "YxzXYXZx" 6 true
    _ = rotationWord (word (rotationSignedWord "YxzXXzxzy")) :=
      rotationStep "YxzXYXZxYzy" "YxzXXzxzy" "YxzX" 5 true
    _ = rotationWord (word (rotationSignedWord "Yxzxzxzy")) :=
      rotationStep "YxzXXzxzy" "Yxzxzxzy" "Yxz" 0 true

end

end GroupApproximation.LiteralBaseP13RotationReplay

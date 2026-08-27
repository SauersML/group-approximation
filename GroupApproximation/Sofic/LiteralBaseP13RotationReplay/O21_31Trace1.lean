import GroupApproximation.Sofic.LiteralBaseP13RotationReplay

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem o21_31Trace1 :
    rotationWord (word (rotationSignedWord "YxyxzxYxzYxZXYXyXyZXyX")) =
      rotationWord (word (rotationSignedWord "YxyXyyzyyxzyXyZXyX")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "YxyxZxYxzYxZXYXyXyZXyX")) :=
      rotationStep "YxyxzxYxzYxZXYXyXyZXyX" "YxyxZxYxzYxZXYXyXyZXyX" "Yxyx" 2 false
    _ = rotationWord (word (rotationSignedWord "YxyXXZxYxzYxZXYXyXyZXyX")) :=
      rotationStep "YxyxZxYxzYxZXYXyXyZXyX" "YxyXXZxYxzYxZXYXyXyZXyX" "Yxy" 0 false
    _ = rotationWord (word (rotationSignedWord "YxyXyXzxxzYxZXYXyXyZXyX")) :=
      rotationStep "YxyXXZxYxzYxZXYXyXyZXyX" "YxyXyXzxxzYxZXYXyXyZXyX" "YxyXy" 5 true
    _ = rotationWord (word (rotationSignedWord "YxyXyXzXzYxZXYXyXyZXyX")) :=
      rotationStep "YxyXyXzxxzYxZXYXyXyZXyX" "YxyXyXzXzYxZXYXyXyZXyX" "YxyXyXz" 0 false
    _ = rotationWord (word (rotationSignedWord "YxyXyXZXzYxZXYXyXyZXyX")) :=
      rotationStep "YxyXyXzXzYxZXYXyXyZXyX" "YxyXyXZXzYxZXYXyXyZXyX" "YxyXyX" 2 false
    _ = rotationWord (word (rotationSignedWord "YxyXyXZXZYxZXYXyXyZXyX")) :=
      rotationStep "YxyXyXZXzYxZXYXyXyZXyX" "YxyXyXZXZYxZXYXyXyZXyX" "YxyXyXZX" 2 false
    _ = rotationWord (word (rotationSignedWord "YxyXyzxYxZXYXyXyZXyX")) :=
      rotationStep "YxyXyXZXZYxZXYXyXyZXyX" "YxyXyzxYxZXYXyXyZXyX" "YxyXyX" 3 true
    _ = rotationWord (word (rotationSignedWord "YxyXyzxYxzXYXyXyZXyX")) :=
      rotationStep "YxyXyzxYxZXYXyXyZXyX" "YxyXyzxYxzXYXyXyZXyX" "YxyXyzxYx" 2 true
    _ = rotationWord (word (rotationSignedWord "YxyXyzxYxzxxYXyXyZXyX")) :=
      rotationStep "YxyXyzxYxzXYXyXyZXyX" "YxyXyzxYxzxxYXyXyZXyX" "YxyXyzxYxz" 0 true
    _ = rotationWord (word (rotationSignedWord "YxyXyzxYZXZxYXyXyZXyX")) :=
      rotationStep "YxyXyzxYxzxxYXyXyZXyX" "YxyXyzxYZXZxYXyXyZXyX" "YxyXyzxY" 3 false
    _ = rotationWord (word (rotationSignedWord "YxyXyzxYZyXzyXyZXyX")) :=
      rotationStep "YxyXyzxYZXZxYXyXyZXyX" "YxyXyzxYZyXzyXyZXyX" "YxyXyzxYZy" 5 true
    _ = rotationWord (word (rotationSignedWord "YxyXyzxxYzyzyXyZXyX")) :=
      rotationStep "YxyXyzxYZyXzyXyZXyX" "YxyXyzxxYzyzyXyZXyX" "YxyXyzxx" 6 true
    _ = rotationWord (word (rotationSignedWord "YxyXyzXYzyzyXyZXyX")) :=
      rotationStep "YxyXyzxxYzyzyXyZXyX" "YxyXyzXYzyzyXyZXyX" "YxyXyz" 0 false
    _ = rotationWord (word (rotationSignedWord "YxyXyzXYZyzyXyZXyX")) :=
      rotationStep "YxyXyzXYzyzyXyZXyX" "YxyXyzXYZyzyXyZXyX" "YxyXyzXY" 2 false
    _ = rotationWord (word (rotationSignedWord "YxyXyZXYZyzyXyZXyX")) :=
      rotationStep "YxyXyzXYZyzyXyZXyX" "YxyXyZXYZyzyXyZXyX" "YxyXy" 2 false
    _ = rotationWord (word (rotationSignedWord "YxyXyZYzyxzyXyZXyX")) :=
      rotationStep "YxyXyZXYZyzyXyZXyX" "YxyXyZYzyxzyXyZXyX" "YxyXyZ" 6 true
    _ = rotationWord (word (rotationSignedWord "YxyXyZYZyxzyXyZXyX")) :=
      rotationStep "YxyXyZYzyxzyXyZXyX" "YxyXyZYZyxzyXyZXyX" "YxyXyZY" 2 false
    _ = rotationWord (word (rotationSignedWord "YxyXyyzyyxzyXyZXyX")) :=
      rotationStep "YxyXyZYZyxzyXyZXyX" "YxyXyyzyyxzyXyZXyX" "YxyXy" 4 true

end

end GroupApproximation.LiteralBaseP13RotationReplay

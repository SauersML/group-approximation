import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.S321Trace1

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem s321Trace2 :
    rotationWord (word (rotationSignedWord "XzYXYXYxyxzxyxyZxZXYXyXyZXyX")) =
      rotationWord (word (rotationSignedWord "YzxYxZxYxyXyZXyX")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "YXZXyxyXyXYxzyXyXyZXyX")) := s321Trace1
    _ = rotationWord (word (rotationSignedWord "YXZXyxyXyXYZXZXyXyXyZXyX")) :=
      rotationStep "YXZXyxyXyXYxzyXyXyZXyX" "YXZXyxyXyXYZXZXyXyXyZXyX" "YXZXyxyXyXY" 3 false
    _ = rotationWord (word (rotationSignedWord "YXZXyxyXzyxYXZXyXyXyZXyX")) :=
      rotationStep "YXZXyxyXyXYZXZXyXyXyZXyX" "YXZXyxyXzyxYXZXyXyXyZXyX" "YXZXyxyXy" 6 true
    _ = rotationWord (word (rotationSignedWord "YXZXyxyXzyzxyXXyXyXyZXyX")) :=
      rotationStep "YXZXyxyXzyxYXZXyXyXyZXyX" "YXZXyxyXzyzxyXXyXyXyZXyX" "YXZXyxyXzyx" 5 true
    _ = rotationWord (word (rotationSignedWord "YXZXyxyXzyzxyxyXyXyZXyX")) :=
      rotationStep "YXZXyxyXzyzxyXXyXyXyZXyX" "YXZXyxyXzyzxyxyXyXyZXyX" "YXZXyxyXzyzxy" 0 true
    _ = rotationWord (word (rotationSignedWord "YXZXyxyXYZYxyxyXyXyZXyX")) :=
      rotationStep "YXZXyxyXzyzxyxyXyXyZXyX" "YXZXyxyXYZYxyxyXyXyZXyX" "YXZXyxyXz" 4 false
    _ = rotationWord (word (rotationSignedWord "YXZXyxzyxYYxyxyXyXyZXyX")) :=
      rotationStep "YXZXyxyXYZYxyxyXyXyZXyX" "YXZXyxzyxYYxyxyXyXyZXyX" "YXZXyxy" 6 true
    _ = rotationWord (word (rotationSignedWord "YXZXyxzyxyxyxyXyXyZXyX")) :=
      rotationStep "YXZXyxzyxYYxyxyXyXyZXyX" "YXZXyxzyxyxyxyXyXyZXyX" "YXZXyxzyx" 1 true
    _ = rotationWord (word (rotationSignedWord "YXZXyxzXYXYXXyXyZXyX")) :=
      rotationStep "YXZXyxzyxyxyxyXyXyZXyX" "YXZXyxzXYXYXXyXyZXyX" "YXZXyxzy" 7 false
    _ = rotationWord (word (rotationSignedWord "YXZXyxzXYXYxyXyZXyX")) :=
      rotationStep "YXZXyxzXYXYXXyXyZXyX" "YXZXyxzXYXYxyXyZXyX" "YXZXyxzXYXY" 0 true
    _ = rotationWord (word (rotationSignedWord "YXZXyxzxxYXYxyXyZXyX")) :=
      rotationStep "YXZXyxzXYXYxyXyZXyX" "YXZXyxzxxYXYxyXyZXyX" "YXZXyxz" 0 true
    _ = rotationWord (word (rotationSignedWord "YXZXyZXZxYXYxyXyZXyX")) :=
      rotationStep "YXZXyxzxxYXYxyXyZXyX" "YXZXyZXZxYXYxyXyZXyX" "YXZXy" 3 false
    _ = rotationWord (word (rotationSignedWord "YXZXyZyXzYxyXyZXyX")) :=
      rotationStep "YXZXyZXZxYXYxyXyZXyX" "YXZXyZyXzYxyXyZXyX" "YXZXyZy" 5 true
    _ = rotationWord (word (rotationSignedWord "YXZXyzyXzYxyXyZXyX")) :=
      rotationStep "YXZXyZyXzYxyXyZXyX" "YXZXyzyXzYxyXyZXyX" "YXZXy" 2 true
    _ = rotationWord (word (rotationSignedWord "YzxzyzyXzYxyXyZXyX")) :=
      rotationStep "YXZXyzyXzYxyXyZXyX" "YzxzyzyXzYxyXyZXyX" "YX" 3 true
    _ = rotationWord (word (rotationSignedWord "YzxYZXzYxyXyZXyX")) :=
      rotationStep "YzxzyzyXzYxyXyZXyX" "YzxYZXzYxyXyZXyX" "Yzxz" 4 false
    _ = rotationWord (word (rotationSignedWord "YzxYZXZYxyXyZXyX")) :=
      rotationStep "YzxYZXzYxyXyZXyX" "YzxYZXZYxyXyZXyX" "YzxYZX" 2 false
    _ = rotationWord (word (rotationSignedWord "YzxYxzxYxyXyZXyX")) :=
      rotationStep "YzxYZXZYxyXyZXyX" "YzxYxzxYxyXyZXyX" "YzxY" 3 true
    _ = rotationWord (word (rotationSignedWord "YzxYxZxYxyXyZXyX")) :=
      rotationStep "YzxYxzxYxyXyZXyX" "YzxYxZxYxyXyZXyX" "YzxYx" 2 false

end

end GroupApproximation.LiteralBaseP13RotationReplay

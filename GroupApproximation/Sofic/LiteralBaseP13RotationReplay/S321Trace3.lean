import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.S321Trace2

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem s321Trace3 :
    rotationWord (word (rotationSignedWord "XzYXYXYxyxzxyxyZxZXYXyXyZXyX")) =
      rotationWord (word (rotationSignedWord "YxzXYXYYzyyX")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "YzxYxZxYxyXyZXyX")) := s321Trace2
    _ = rotationWord (word (rotationSignedWord "YzxYXXZxYxyXyZXyX")) :=
      rotationStep "YzxYxZxYxyXyZXyX" "YzxYXXZxYxyXyZXyX" "YzxY" 0 false
    _ = rotationWord (word (rotationSignedWord "YzxYXyXzxxyXyZXyX")) :=
      rotationStep "YzxYXXZxYxyXyZXyX" "YzxYXyXzxxyXyZXyX" "YzxYXy" 5 true
    _ = rotationWord (word (rotationSignedWord "YzxYXyXzXyXyZXyX")) :=
      rotationStep "YzxYXyXzxxyXyZXyX" "YzxYXyXzXyXyZXyX" "YzxYXyXz" 0 false
    _ = rotationWord (word (rotationSignedWord "YZxYXyXzXyXyZXyX")) :=
      rotationStep "YzxYXyXzXyXyZXyX" "YZxYXyXzXyXyZXyX" "Y" 2 false
    _ = rotationWord (word (rotationSignedWord "YZxYXyXZXyXyZXyX")) :=
      rotationStep "YZxYXyXzXyXyZXyX" "YZxYXyXZXyXyZXyX" "YZxYXyX" 2 false
    _ = rotationWord (word (rotationSignedWord "YZxYXyzxzyXyZXyX")) :=
      rotationStep "YZxYXyXZXyXyZXyX" "YZxYXyzxzyXyZXyX" "YZxYXyX" 3 true
    _ = rotationWord (word (rotationSignedWord "YxyXzyzxzyXyZXyX")) :=
      rotationStep "YZxYXyzxzyXyZXyX" "YxyXzyzxzyXyZXyX" "Yxy" 5 true
    _ = rotationWord (word (rotationSignedWord "YxyXYZYxzyXyZXyX")) :=
      rotationStep "YxyXzyzxzyXyZXyX" "YxyXYZYxzyXyZXyX" "YxyXz" 4 false
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

end

end GroupApproximation.LiteralBaseP13RotationReplay

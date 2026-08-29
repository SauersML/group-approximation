import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.S123Trace2

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem s123Trace3 :
    rotationWord (word (rotationSignedWord "YxzYXXYxzYxyZXyyZXyxyxyZX")) =
      rotationWord (word (rotationSignedWord "yZYxyXXZXyx")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "YxzYxYxZxYxyXZyx")) := s123Trace2
    _ = rotationWord (word (rotationSignedWord "YxzYxYxzxYxyXZyx")) :=
      rotationStep "YxzYxYxZxYxyXZyx" "YxzYxYxzxYxyXZyx" "YxzYxYx" 2 true
    _ = rotationWord (word (rotationSignedWord "YxzYxYxzxYxyXzyx")) :=
      rotationStep "YxzYxYxzxYxyXZyx" "YxzYxYxzxYxyXzyx" "YxzYxYxzxYxyX" 2 true
    _ = rotationWord (word (rotationSignedWord "YxzYxYZXZYxyXzyx")) :=
      rotationStep "YxzYxYxzxYxyXzyx" "YxzYxYZXZYxyXzyx" "YxzYxY" 3 false
    _ = rotationWord (word (rotationSignedWord "YxzYxYZXZYZxYXyx")) :=
      rotationStep "YxzYxYZXZYxyXzyx" "YxzYxYZXZYZxYXyx" "YxzYxYZXZYZx" 5 false
    _ = rotationWord (word (rotationSignedWord "YxzYxYZXyzyxYXyx")) :=
      rotationStep "YxzYxYZXZYZxYXyx" "YxzYxYZXyzyxYXyx" "YxzYxYZX" 4 true
    _ = rotationWord (word (rotationSignedWord "YxzYxYZXyyXYZXyx")) :=
      rotationStep "YxzYxYZXyzyxYXyx" "YxzYxYZXyyXYZXyx" "YxzYxYZXyy" 6 false
    _ = rotationWord (word (rotationSignedWord "YxzYxYZXYXYZXyx")) :=
      rotationStep "YxzYxYZXyyXYZXyx" "YxzYxYZXYXYZXyx" "YxzYxYZX" 1 false
    _ = rotationWord (word (rotationSignedWord "YxzYxYzXYXYZXyx")) :=
      rotationStep "YxzYxYZXYXYZXyx" "YxzYxYzXYXYZXyx" "YxzYxY" 2 true
    _ = rotationWord (word (rotationSignedWord "YxzyyxYzXYXYZXyx")) :=
      rotationStep "YxzYxYzXYXYZXyx" "YxzyyxYzXYXYZXyx" "Yxz" 1 true
    _ = rotationWord (word (rotationSignedWord "YxzyZyXYXYXYZXyx")) :=
      rotationStep "YxzyyxYzXYXYZXyx" "YxzyZyXYXYXYZXyx" "YxzyZy" 6 false
    _ = rotationWord (word (rotationSignedWord "YxzyzyXYXYXYZXyx")) :=
      rotationStep "YxzyZyXYXYXYZXyx" "YxzyzyXYXYXYZXyx" "Yxzy" 2 true
    _ = rotationWord (word (rotationSignedWord "YxYZXYXYXYZXyx")) :=
      rotationStep "YxzyzyXYXYXYZXyx" "YxYZXYXYXYZXyx" "Yxz" 4 false
    _ = rotationWord (word (rotationSignedWord "YxYzXYXYXYZXyx")) :=
      rotationStep "YxYZXYXYXYZXyx" "YxYzXYXYXYZXyx" "YxY" 2 true
    _ = rotationWord (word (rotationSignedWord "YxYzyxyxyxZXyx")) :=
      rotationStep "YxYzXYXYXYZXyx" "YxYzyxyxyxZXyx" "YxYzX" 7 true
    _ = rotationWord (word (rotationSignedWord "YYZyyxyxZXyx")) :=
      rotationStep "YxYzyxyxyxZXyx" "YYZyyxyxZXyx" "Yx" 6 false
    _ = rotationWord (word (rotationSignedWord "YYZYxyxZXyx")) :=
      rotationStep "YYZyyxyxZXyx" "YYZYxyxZXyx" "YYZ" 1 false
    _ = rotationWord (word (rotationSignedWord "yZYxyxZXyx")) :=
      rotationStep "YYZYxyxZXyx" "yZYxyxZXyx" "" 1 true
    _ = rotationWord (word (rotationSignedWord "yZYxyXXZXyx")) :=
      rotationStep "yZYxyxZXyx" "yZYxyXXZXyx" "yZYxy" 0 false

end

end GroupApproximation.LiteralBaseP13RotationReplay

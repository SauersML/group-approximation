import GroupApproximation.Sofic.LiteralBaseP13RotationReplay

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem o21_23Trace1 :
    rotationWord (word (rotationSignedWord "YxyxzXYxzYZXYXyyZXyx")) =
      rotationWord (word (rotationSignedWord "YxZYxYZXYXYZXyx")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "YxyxzXYxzYZXYXYZXyx")) :=
      rotationStep "YxyxzXYxzYZXYXyyZXyx" "YxyxzXYxzYZXYXYZXyx" "YxyxzXYxzYZXYX" 1 false
    _ = rotationWord (word (rotationSignedWord "YxyxzXYxZYZXYXYZXyx")) :=
      rotationStep "YxyxzXYxzYZXYXYZXyx" "YxyxzXYxZYZXYXYZXyx" "YxyxzXYx" 2 false
    _ = rotationWord (word (rotationSignedWord "YxyxzXYxyzyXYXYZXyx")) :=
      rotationStep "YxyxzXYxZYZXYXYZXyx" "YxyxzXYxyzyXYXYZXyx" "YxyxzXYx" 4 true
    _ = rotationWord (word (rotationSignedWord "YxyxzXYxyZyXYXYZXyx")) :=
      rotationStep "YxyxzXYxyzyXYXYZXyx" "YxyxzXYxyZyXYXYZXyx" "YxyxzXYxy" 2 false
    _ = rotationWord (word (rotationSignedWord "YxyxzXYxyyxYzXYZXyx")) :=
      rotationStep "YxyxzXYxyZyXYXYZXyx" "YxyxzXYxyyxYzXYZXyx" "YxyxzXYxyyx" 6 true
    _ = rotationWord (word (rotationSignedWord "YxyxzXYxYxYzXYZXyx")) :=
      rotationStep "YxyxzXYxyyxYzXYZXyx" "YxyxzXYxYxYzXYZXyx" "YxyxzXYx" 1 false
    _ = rotationWord (word (rotationSignedWord "YxyxzxxYxYxYzXYZXyx")) :=
      rotationStep "YxyxzXYxYxYzXYZXyx" "YxyxzxxYxYxYzXYZXyx" "Yxyxz" 0 true
    _ = rotationWord (word (rotationSignedWord "YxyZXZxYxYxYzXYZXyx")) :=
      rotationStep "YxyxzxxYxYxYzXYZXyx" "YxyZXZxYxYxYzXYZXyx" "Yxy" 3 false
    _ = rotationWord (word (rotationSignedWord "YxyZyXzxxYxYzXYZXyx")) :=
      rotationStep "YxyZXZxYxYxYzXYZXyx" "YxyZyXzxxYxYzXYZXyx" "YxyZy" 5 true
    _ = rotationWord (word (rotationSignedWord "YxyZyXzXYxYzXYZXyx")) :=
      rotationStep "YxyZyXzxxYxYzXYZXyx" "YxyZyXzXYxYzXYZXyx" "YxyZyXz" 0 false
    _ = rotationWord (word (rotationSignedWord "YxyZyXZXYxYzXYZXyx")) :=
      rotationStep "YxyZyXzXYxYzXYZXyx" "YxyZyXZXYxYzXYZXyx" "YxyZyX" 2 false
    _ = rotationWord (word (rotationSignedWord "YxyzyXZXYxYzXYZXyx")) :=
      rotationStep "YxyZyXZXYxYzXYZXyx" "YxyzyXZXYxYzXYZXyx" "Yxy" 2 true
    _ = rotationWord (word (rotationSignedWord "YxyzyzxzYxYzXYZXyx")) :=
      rotationStep "YxyzyXZXYxYzXYZXyx" "YxyzyzxzYxYzXYZXyx" "YxyzyX" 3 true
    _ = rotationWord (word (rotationSignedWord "YxZYxzYxYzXYZXyx")) :=
      rotationStep "YxyzyzxzYxYzXYZXyx" "YxZYxzYxYzXYZXyx" "Yx" 4 false
    _ = rotationWord (word (rotationSignedWord "YxZYxzyyxYzXYZXyx")) :=
      rotationStep "YxZYxzYxYzXYZXyx" "YxZYxzyyxYzXYZXyx" "YxZYxz" 1 true
    _ = rotationWord (word (rotationSignedWord "YxZYxzyZyXYXYZXyx")) :=
      rotationStep "YxZYxzyyxYzXYZXyx" "YxZYxzyZyXYXYZXyx" "YxZYxzyZy" 6 false
    _ = rotationWord (word (rotationSignedWord "YxZYxzyzyXYXYZXyx")) :=
      rotationStep "YxZYxzyZyXYXYZXyx" "YxZYxzyzyXYXYZXyx" "YxZYxzy" 2 true
    _ = rotationWord (word (rotationSignedWord "YxZYxYZXYXYZXyx")) :=
      rotationStep "YxZYxzyzyXYXYZXyx" "YxZYxYZXYXYZXyx" "YxZYxz" 4 false

end

end GroupApproximation.LiteralBaseP13RotationReplay

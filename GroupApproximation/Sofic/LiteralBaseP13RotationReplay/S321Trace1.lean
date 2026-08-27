import GroupApproximation.Sofic.LiteralBaseP13RotationReplay

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem s321Trace1 :
    rotationWord (word (rotationSignedWord "XzYXYXYxyxzxyxyZxZXYXyXyZXyX")) =
      rotationWord (word (rotationSignedWord "YXZXyxyXyXYxzyXyXyZXyX")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "XzYXYXYxyxzxyxyzxZXYXyXyZXyX")) :=
      rotationStep "XzYXYXYxyxzxyxyZxZXYXyXyZXyX" "XzYXYXYxyxzxyxyzxZXYXyXyZXyX" "XzYXYXYxyxzxyxy" 2 true
    _ = rotationWord (word (rotationSignedWord "XzYXYXYxyxzxyxyzxzXYXyXyZXyX")) :=
      rotationStep "XzYXYXYxyxzxyxyzxZXYXyXyZXyX" "XzYXYXYxyxzxyxyzxzXYXyXyZXyX" "XzYXYXYxyxzxyxyzx" 2 true
    _ = rotationWord (word (rotationSignedWord "XzYXYXYxyxzxyxyXZXXYXyXyZXyX")) :=
      rotationStep "XzYXYXYxyxzxyxyzxzXYXyXyZXyX" "XzYXYXYxyxzxyxyXZXXYXyXyZXyX" "XzYXYXYxyxzxyxyz" 3 false
    _ = rotationWord (word (rotationSignedWord "XzYXYXYxyxzxyxyXZxYXyXyZXyX")) :=
      rotationStep "XzYXYXYxyxzxyxyXZXXYXyXyZXyX" "XzYXYXYxyxzxyxyXZxYXyXyZXyX" "XzYXYXYxyxzxyxyXZ" 0 true
    _ = rotationWord (word (rotationSignedWord "XzYXYXYxyxzxyxyyXzyXyZXyX")) :=
      rotationStep "XzYXYXYxyxzxyxyXZxYXyXyZXyX" "XzYXYXYxyxzxyxyyXzyXyZXyX" "XzYXYXYxyxzxyxyy" 5 true
    _ = rotationWord (word (rotationSignedWord "XzYXYXYxyxzxyxYXzyXyZXyX")) :=
      rotationStep "XzYXYXYxyxzxyxyyXzyXyZXyX" "XzYXYXYxyxzxyxYXzyXyZXyX" "XzYXYXYxyxzxyx" 1 false
    _ = rotationWord (word (rotationSignedWord "XzYXYXYxyxzxyxYXZyXyZXyX")) :=
      rotationStep "XzYXYXYxyxzxyxYXzyXyZXyX" "XzYXYXYxyxzxyxYXZyXyZXyX" "XzYXYXYxyxzxyxYX" 2 false
    _ = rotationWord (word (rotationSignedWord "XzYXYXYxyxzxyzxyXyXyZXyX")) :=
      rotationStep "XzYXYXYxyxzxyxYXZyXyZXyX" "XzYXYXYxyxzxyzxyXyXyZXyX" "XzYXYXYxyxzxyx" 5 true
    _ = rotationWord (word (rotationSignedWord "XzYXYXYxyXXzxyzxyXyXyZXyX")) :=
      rotationStep "XzYXYXYxyxzxyzxyXyXyZXyX" "XzYXYXYxyXXzxyzxyXyXyZXyX" "XzYXYXYxy" 0 false
    _ = rotationWord (word (rotationSignedWord "XzYXYXYxyXYXZxzxyXyXyZXyX")) :=
      rotationStep "XzYXYXYxyXXzxyzxyXyXyZXyX" "XzYXYXYxyXYXZxzxyXyXyZXyX" "XzYXYXYxyX" 5 false
    _ = rotationWord (word (rotationSignedWord "XzYXYXYxyXYXzxzxyXyXyZXyX")) :=
      rotationStep "XzYXYXYxyXYXZxzxyXyXyZXyX" "XzYXYXYxyXYXzxzxyXyXyZXyX" "XzYXYXYxyXYX" 2 true
    _ = rotationWord (word (rotationSignedWord "XzYXYXYxyXYXXZyXyXyZXyX")) :=
      rotationStep "XzYXYXYxyXYXzxzxyXyXyZXyX" "XzYXYXYxyXYXXZyXyXyZXyX" "XzYXYXYxyXYXz" 3 false
    _ = rotationWord (word (rotationSignedWord "XzYXYXYxyXYxZyXyXyZXyX")) :=
      rotationStep "XzYXYXYxyXYXXZyXyXyZXyX" "XzYXYXYxyXYxZyXyXyZXyX" "XzYXYXYxyXY" 0 true
    _ = rotationWord (word (rotationSignedWord "XzYXYXYXXyXYxZyXyXyZXyX")) :=
      rotationStep "XzYXYXYxyXYxZyXyXyZXyX" "XzYXYXYXXyXYxZyXyXyZXyX" "XzYXYXY" 0 false
    _ = rotationWord (word (rotationSignedWord "XzxyxyxyXyXYxZyXyXyZXyX")) :=
      rotationStep "XzYXYXYXXyXYxZyXyXyZXyX" "XzxyxyxyXyXYxZyXyXyZXyX" "Xz" 7 true
    _ = rotationWord (word (rotationSignedWord "YXZxxyxyXyXYxZyXyXyZXyX")) :=
      rotationStep "XzxyxyxyXyXYxZyXyXyZXyX" "YXZxxyxyXyXYxZyXyXyZXyX" "" 5 false
    _ = rotationWord (word (rotationSignedWord "YXZXyxyXyXYxZyXyXyZXyX")) :=
      rotationStep "YXZxxyxyXyXYxZyXyXyZXyX" "YXZXyxyXyXYxZyXyXyZXyX" "YXZ" 0 false
    _ = rotationWord (word (rotationSignedWord "YXZXyxyXyXYxzyXyXyZXyX")) :=
      rotationStep "YXZXyxyXyXYxZyXyXyZXyX" "YXZXyxyXyXYxzyXyXyZXyX" "YXZXyxyXyXYx" 2 true

end

end GroupApproximation.LiteralBaseP13RotationReplay

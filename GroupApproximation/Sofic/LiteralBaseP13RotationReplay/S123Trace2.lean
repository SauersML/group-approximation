import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.S123Trace1

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem s123Trace2 :
    rotationWord (word (rotationSignedWord "YxzYXXYxzYxyZXyyZXyxyxyZX")) =
      rotationWord (word (rotationSignedWord "YxzYxYxZxYxyXZyx")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "YxzYxYxYXYXyyXYZXYXYXZX")) := s123Trace1
    _ = rotationWord (word (rotationSignedWord "YxzYxYxYXYXYXYZXYXYXZX")) :=
      rotationStep "YxzYxYxYXYXyyXYZXYXYXZX" "YxzYxYxYXYXYXYZXYXYXZX" "YxzYxYxYXYX" 1 false
    _ = rotationWord (word (rotationSignedWord "YxzYxYxxyxyxZXYXYXZX")) :=
      rotationStep "YxzYxYxYXYXYXYZXYXYXZX" "YxzYxYxxyxyxZXYXYXZX" "YxzYxYx" 7 true
    _ = rotationWord (word (rotationSignedWord "YxzYxYXyxyxZXYXYXZX")) :=
      rotationStep "YxzYxYxxyxyxZXYXYXZX" "YxzYxYXyxyxZXYXYXZX" "YxzYxY" 0 false
    _ = rotationWord (word (rotationSignedWord "YxzYxYXyxyXXZXYXYXZX")) :=
      rotationStep "YxzYxYXyxyxZXYXYXZX" "YxzYxYXyxyXXZXYXYXZX" "YxzYxYXyxy" 0 false
    _ = rotationWord (word (rotationSignedWord "YxzYxYXyxyXzxzYXYXZX")) :=
      rotationStep "YxzYxYXyxyXXZXYXYXZX" "YxzYxYXyxyXzxzYXYXZX" "YxzYxYXyxyXX" 3 true
    _ = rotationWord (word (rotationSignedWord "YxzYxYXyZxYzYXYXZX")) :=
      rotationStep "YxzYxYXyxyXzxzYXYXZX" "YxzYxYXyZxYzYXYXZX" "YxzYxYXyxy" 5 false
    _ = rotationWord (word (rotationSignedWord "YxzYxYXyZxYzYxxYXZX")) :=
      rotationStep "YxzYxYXyZxYzYXYXZX" "YxzYxYXyZxYzYxxYXZX" "YxzYxYXyZxYzY" 0 true
    _ = rotationWord (word (rotationSignedWord "YxzYxYXyZxYzYxzxyXX")) :=
      rotationStep "YxzYxYXyZxYzYxxYXZX" "YxzYxYXyZxYzYxzxyXX" "YxzYxYXyZxYzYxx" 5 true
    _ = rotationWord (word (rotationSignedWord "YxzYxYXyZxYzYxzxyx")) :=
      rotationStep "YxzYxYXyZxYzYxzxyXX" "YxzYxYXyZxYzYxzxyx" "YxzYxYXyZxYzYxzxy" 0 true
    _ = rotationWord (word (rotationSignedWord "YxzYxYXyZxYZYxzxyx")) :=
      rotationStep "YxzYxYXyZxYzYxzxyx" "YxzYxYXyZxYZYxzxyx" "YxzYxYXyZxY" 2 false
    _ = rotationWord (word (rotationSignedWord "YxzYxYXyZxYZYZXZyx")) :=
      rotationStep "YxzYxYXyZxYZYxzxyx" "YxzYxYXyZxYZYZXZyx" "YxzYxYXyZxYZY" 3 false
    _ = rotationWord (word (rotationSignedWord "YxzYxYXyZxzyXZyx")) :=
      rotationStep "YxzYxYXyZxYZYZXZyx" "YxzYxYXyZxzyXZyx" "YxzYxYXyZxY" 4 true
    _ = rotationWord (word (rotationSignedWord "YxzYxYXyzxzyXZyx")) :=
      rotationStep "YxzYxYXyZxzyXZyx" "YxzYxYXyzxzyXZyx" "YxzYxYXy" 2 true
    _ = rotationWord (word (rotationSignedWord "YxzYxYXyXZXyXZyx")) :=
      rotationStep "YxzYxYXyzxzyXZyx" "YxzYxYXyXZXyXZyx" "YxzYxYXyz" 3 false
    _ = rotationWord (word (rotationSignedWord "YxzYxYXyXzXyXZyx")) :=
      rotationStep "YxzYxYXyXZXyXZyx" "YxzYxYXyXzXyXZyx" "YxzYxYXyX" 2 true
    _ = rotationWord (word (rotationSignedWord "YxzYxYxxyXzXyXZyx")) :=
      rotationStep "YxzYxYXyXzXyXZyx" "YxzYxYxxyXzXyXZyx" "YxzYxY" 0 true
    _ = rotationWord (word (rotationSignedWord "YxzYxYxZxYXXyXZyx")) :=
      rotationStep "YxzYxYxxyXzXyXZyx" "YxzYxYxZxYXXyXZyx" "YxzYxYxZx" 5 false
    _ = rotationWord (word (rotationSignedWord "YxzYxYxZxYxyXZyx")) :=
      rotationStep "YxzYxYxZxYXXyXZyx" "YxzYxYxZxYxyXZyx" "YxzYxYxZxY" 0 true

end

end GroupApproximation.LiteralBaseP13RotationReplay

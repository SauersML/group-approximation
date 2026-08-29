import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.S312Trace1

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem s312Trace2 :
    rotationWord (word (rotationSignedWord "xYxzYxYxzYXXyZXyyZXyxyxyZx")) =
      rotationWord (word (rotationSignedWord "xYxzYxYXyXXZYXy")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "xYxzYxYxzYxyzxzxyxYxyXy")) := s312Trace1
    _ = rotationWord (word (rotationSignedWord "xYxzYxYxzYxyXZyxYxyXy")) :=
      rotationStep "xYxzYxYxzYxyzxzxyxYxyXy" "xYxzYxYxzYxyXZyxYxyXy" "xYxzYxYxzYxyz" 3 false
    _ = rotationWord (word (rotationSignedWord "xYxzYxYxZYxyXZyxYxyXy")) :=
      rotationStep "xYxzYxYxzYxyXZyxYxyXy" "xYxzYxYxZYxyXZyxYxyXy" "xYxzYxYx" 2 false
    _ = rotationWord (word (rotationSignedWord "xYxzYxYxZYxyXzyxYxyXy")) :=
      rotationStep "xYxzYxYxZYxyXZyxYxyXy" "xYxzYxYxZYxyXzyxYxyXy" "xYxzYxYxZYxyX" 2 true
    _ = rotationWord (word (rotationSignedWord "xYxzYxYxZYZxYXyxYxyXy")) :=
      rotationStep "xYxzYxYxZYxyXzyxYxyXy" "xYxzYxYxZYZxYXyxYxyXy" "xYxzYxYxZYZx" 5 false
    _ = rotationWord (word (rotationSignedWord "xYxzYxYxyzyxYXyxYxyXy")) :=
      rotationStep "xYxzYxYxZYZxYXyxYxyXy" "xYxzYxYxyzyxYXyxYxyXy" "xYxzYxYx" 4 true
    _ = rotationWord (word (rotationSignedWord "xYxzYxYxyyXYZXyxYxyXy")) :=
      rotationStep "xYxzYxYxyzyxYXyxYxyXy" "xYxzYxYxyyXYZXyxYxyXy" "xYxzYxYxyy" 6 false
    _ = rotationWord (word (rotationSignedWord "xYxzYxYxYXYZXyxYxyXy")) :=
      rotationStep "xYxzYxYxyyXYZXyxYxyXy" "xYxzYxYxYXYZXyxYxyXy" "xYxzYxYx" 1 false
    _ = rotationWord (word (rotationSignedWord "xYxzYxYxYXYxzxzyxYxyXy")) :=
      rotationStep "xYxzYxYxYXYZXyxYxyXy" "xYxzYxYxYXYxzxzyxYxyXy" "xYxzYxYxYXY" 3 true
    _ = rotationWord (word (rotationSignedWord "xYxzYxYxYXYxzxyXYZxyXy")) :=
      rotationStep "xYxzYxYxYXYxzxzyxYxyXy" "xYxzYxYxYXYxzxyXYZxyXy" "xYxzYxYxYXYxzxy" 6 false
    _ = rotationWord (word (rotationSignedWord "xYxzYxYxYXYxxYXZYZxyXy")) :=
      rotationStep "xYxzYxYxYXYxzxyXYZxyXy" "xYxzYxYxYXYxxYXZYZxyXy" "xYxzYxYxYXYxx" 5 false
    _ = rotationWord (word (rotationSignedWord "xYxzYxYxYXYXYXZYZxyXy")) :=
      rotationStep "xYxzYxYxYXYxxYXZYZxyXy" "xYxzYxYxYXYXYXZYZxyXy" "xYxzYxYxYXY" 0 false
    _ = rotationWord (word (rotationSignedWord "xYxzYxYxxyxyxyZYZxyXy")) :=
      rotationStep "xYxzYxYxYXYXYXZYZxyXy" "xYxzYxYxxyxyxyZYZxyXy" "xYxzYxYx" 7 true
    _ = rotationWord (word (rotationSignedWord "xYxzYxYXyxyxyZYZxyXy")) :=
      rotationStep "xYxzYxYxxyxyxyZYZxyXy" "xYxzYxYXyxyxyZYZxyXy" "xYxzYxY" 0 false
    _ = rotationWord (word (rotationSignedWord "xYxzYxYXyxyxyyzyxyXy")) :=
      rotationStep "xYxzYxYXyxyxyZYZxyXy" "xYxzYxYXyxyxyyzyxyXy" "xYxzYxYXyxyxy" 4 true
    _ = rotationWord (word (rotationSignedWord "xYxzYxYXyxyxYzyxyXy")) :=
      rotationStep "xYxzYxYXyxyxyyzyxyXy" "xYxzYxYXyxyxYzyxyXy" "xYxzYxYXyxyx" 1 false
    _ = rotationWord (word (rotationSignedWord "xYxzYxYXyxZyyXy")) :=
      rotationStep "xYxzYxYXyxyxYzyxyXy" "xYxzYxYXyxZyyXy" "xYxzYxYXyxyx" 6 false
    _ = rotationWord (word (rotationSignedWord "xYxzYxYXyxZYXy")) :=
      rotationStep "xYxzYxYXyxZyyXy" "xYxzYxYXyxZYXy" "xYxzYxYXyxZ" 1 false
    _ = rotationWord (word (rotationSignedWord "xYxzYxYXyXXZYXy")) :=
      rotationStep "xYxzYxYXyxZYXy" "xYxzYxYXyXXZYXy" "xYxzYxYXy" 0 false

end

end GroupApproximation.LiteralBaseP13RotationReplay

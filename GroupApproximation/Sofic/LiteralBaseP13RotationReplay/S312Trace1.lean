import GroupApproximation.Sofic.LiteralBaseP13RotationReplay

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem s312Trace1 :
    rotationWord (word (rotationSignedWord "xYxzYxYxzYXXyZXyyZXyxyxyZx")) =
      rotationWord (word (rotationSignedWord "xYxzYxYxzYxyzxzxyxYxyXy")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "xYxzYxYxzYxyZXyyZXyxyxyZx")) :=
      rotationStep "xYxzYxYxzYXXyZXyyZXyxyxyZx" "xYxzYxYxzYxyZXyyZXyxyxyZx" "xYxzYxYxzY" 0 true
    _ = rotationWord (word (rotationSignedWord "xYxzYxYxzYxyZXYZXyxyxyZx")) :=
      rotationStep "xYxzYxYxzYxyZXyyZXyxyxyZx" "xYxzYxYxzYxyZXYZXyxyxyZx" "xYxzYxYxzYxyZX" 1 false
    _ = rotationWord (word (rotationSignedWord "xYxzYxYxzYxyZXYZxxyxyxyZx")) :=
      rotationStep "xYxzYxYxzYxyZXYZXyxyxyZx" "xYxzYxYxzYxyZXYZxxyxyxyZx" "xYxzYxYxzYxyZXYZ" 0 true
    _ = rotationWord (word (rotationSignedWord "xYxzYxYxzYxyZXYZxYXYXYXZx")) :=
      rotationStep "xYxzYxYxzYxyZXYZxxyxyxyZx" "xYxzYxYxzYxyZXYZxYXYXYXZx" "xYxzYxYxzYxyZXYZx" 7 false
    _ = rotationWord (word (rotationSignedWord "xYxzYxYxzYxyZXYZxYXYXXzxy")) :=
      rotationStep "xYxzYxYxzYxyZXYZxYXYXYXZx" "xYxzYxYxzYxyZXYZxYXYXXzxy" "xYxzYxYxzYxyZXYZxYXYX" 5 true
    _ = rotationWord (word (rotationSignedWord "xYxzYxYxzYxyZXYZxYXYxzxy")) :=
      rotationStep "xYxzYxYxzYxyZXYZxYXYXXzxy" "xYxzYxYxzYxyZXYZxYXYxzxy" "xYxzYxYxzYxyZXYZxYXY" 0 true
    _ = rotationWord (word (rotationSignedWord "xYxzYxYxzYxyZXYZxYXYZXZy")) :=
      rotationStep "xYxzYxYxzYxyZXYZxYXYxzxy" "xYxzYxYxzYxyZXYZxYXYZXZy" "xYxzYxYxzYxyZXYZxYXY" 3 false
    _ = rotationWord (word (rotationSignedWord "xYxzYxYxzYxyZXYZxyyXYZXZy")) :=
      rotationStep "xYxzYxYxzYxyZXYZxYXYZXZy" "xYxzYxYxzYxyZXYZxyyXYZXZy" "xYxzYxYxzYxyZXYZx" 1 true
    _ = rotationWord (word (rotationSignedWord "xYxzYxYxzYxyZXYZxyzyxYXZy")) :=
      rotationStep "xYxzYxYxzYxyZXYZxyyXYZXZy" "xYxzYxYxzYxyZXYZxyzyxYXZy" "xYxzYxYxzYxyZXYZxyy" 6 true
    _ = rotationWord (word (rotationSignedWord "xYxzYxYxzYxyZXYZxZYZxYXZy")) :=
      rotationStep "xYxzYxYxzYxyZXYZxyzyxYXZy" "xYxzYxYxzYxyZXYZxZYZxYXZy" "xYxzYxYxzYxyZXYZx" 4 false
    _ = rotationWord (word (rotationSignedWord "xYxzYxYxzYxyZXYZxZYxyXy")) :=
      rotationStep "xYxzYxYxzYxyZXYZxZYZxYXZy" "xYxzYxYxzYxyZXYZxZYxyXy" "xYxzYxYxzYxyZXYZxZYZx" 5 true
    _ = rotationWord (word (rotationSignedWord "xYxzYxYxzYxyZXYzxZYxyXy")) :=
      rotationStep "xYxzYxYxzYxyZXYZxZYxyXy" "xYxzYxYxzYxyZXYzxZYxyXy" "xYxzYxYxzYxyZXY" 2 true
    _ = rotationWord (word (rotationSignedWord "xYxzYxYxzYxyZXYzxzYxyXy")) :=
      rotationStep "xYxzYxYxzYxyZXYzxZYxyXy" "xYxzYxYxzYxyZXYzxzYxyXy" "xYxzYxYxzYxyZXYzx" 2 true
    _ = rotationWord (word (rotationSignedWord "xYxzYxYxzYxyZXYXZXYxyXy")) :=
      rotationStep "xYxzYxYxzYxyZXYzxzYxyXy" "xYxzYxYxzYxyZXYXZXYxyXy" "xYxzYxYxzYxyZXYz" 3 false
    _ = rotationWord (word (rotationSignedWord "xYxzYxYxzYxyZxxYXZXYxyXy")) :=
      rotationStep "xYxzYxYxzYxyZXYXZXYxyXy" "xYxzYxYxzYxyZxxYXZXYxyXy" "xYxzYxYxzYxyZ" 0 true
    _ = rotationWord (word (rotationSignedWord "xYxzYxYxzYxyZxzxyXXYxyXy")) :=
      rotationStep "xYxzYxYxzYxyZxxYXZXYxyXy" "xYxzYxYxzYxyZxzxyXXYxyXy" "xYxzYxYxzYxyZxx" 5 true
    _ = rotationWord (word (rotationSignedWord "xYxzYxYxzYxyZxzxyxYxyXy")) :=
      rotationStep "xYxzYxYxzYxyZxzxyXXYxyXy" "xYxzYxYxzYxyZxzxyxYxyXy" "xYxzYxYxzYxyZxzxy" 0 true
    _ = rotationWord (word (rotationSignedWord "xYxzYxYxzYxyzxzxyxYxyXy")) :=
      rotationStep "xYxzYxYxzYxyZxzxyxYxyXy" "xYxzYxYxzYxyzxzxyxYxyXy" "xYxzYxYxzYxy" 2 true

end

end GroupApproximation.LiteralBaseP13RotationReplay

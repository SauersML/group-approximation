import GroupApproximation.Sofic.LiteralBaseP13RotationReplay

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem s123Trace1 :
    rotationWord (word (rotationSignedWord "YxzYXXYxzYxyZXyyZXyxyxyZX")) =
      rotationWord (word (rotationSignedWord "YxzYxYxYXYXyyXYZXYXYXZX")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "YxzYxYxzYxyZXyyZXyxyxyZX")) :=
      rotationStep "YxzYXXYxzYxyZXyyZXyxyxyZX" "YxzYxYxzYxyZXyyZXyxyxyZX" "YxzY" 0 true
    _ = rotationWord (word (rotationSignedWord "YxzYxYxzYxyZXYZXyxyxyZX")) :=
      rotationStep "YxzYxYxzYxyZXyyZXyxyxyZX" "YxzYxYxzYxyZXYZXyxyxyZX" "YxzYxYxzYxyZX" 1 false
    _ = rotationWord (word (rotationSignedWord "YxzYxYxzYxyZYzyxYXyxyxyZX")) :=
      rotationStep "YxzYxYxzYxyZXYZXyxyxyZX" "YxzYxYxzYxyZYzyxYXyxyxyZX" "YxzYxYxzYxyZ" 6 true
    _ = rotationWord (word (rotationSignedWord "YxzYxYxzYxyZYZyxYXyxyxyZX")) :=
      rotationStep "YxzYxYxzYxyZYzyxYXyxyxyZX" "YxzYxYxzYxyZYZyxYXyxyxyZX" "YxzYxYxzYxyZY" 2 false
    _ = rotationWord (word (rotationSignedWord "YxzYxYxzYxyyzyyxYXyxyxyZX")) :=
      rotationStep "YxzYxYxzYxyZYZyxYXyxyxyZX" "YxzYxYxzYxyyzyyxYXyxyxyZX" "YxzYxYxzYxy" 4 true
    _ = rotationWord (word (rotationSignedWord "YxzYxYxzYxYzyyxYXyxyxyZX")) :=
      rotationStep "YxzYxYxzYxyyzyyxYXyxyxyZX" "YxzYxYxzYxYzyyxYXyxyxyZX" "YxzYxYxzYx" 1 false
    _ = rotationWord (word (rotationSignedWord "YxzYxYxzYYZyXyxYXyxyxyZX")) :=
      rotationStep "YxzYxYxzYxYzyyxYXyxyxyZX" "YxzYxYxzYYZyXyxYXyxyxyZX" "YxzYxYxzYx" 6 false
    _ = rotationWord (word (rotationSignedWord "YxzYxYxzyZyXyxYXyxyxyZX")) :=
      rotationStep "YxzYxYxzYYZyXyxYXyxyxyZX" "YxzYxYxzyZyXyxYXyxyxyZX" "YxzYxYxz" 1 true
    _ = rotationWord (word (rotationSignedWord "YxzYxYxzyzyXyxYXyxyxyZX")) :=
      rotationStep "YxzYxYxzyZyXyxYXyxyxyZX" "YxzYxYxzyzyXyxYXyxyxyZX" "YxzYxYxzy" 2 true
    _ = rotationWord (word (rotationSignedWord "YxzYxYxYZXyxYXyxyxyZX")) :=
      rotationStep "YxzYxYxzyzyXyxYXyxyxyZX" "YxzYxYxYZXyxYXyxyxyZX" "YxzYxYxz" 4 false
    _ = rotationWord (word (rotationSignedWord "YxzYxYxYxzxzyxYXyxyxyZX")) :=
      rotationStep "YxzYxYxYZXyxYXyxyxyZX" "YxzYxYxYxzxzyxYXyxyxyZX" "YxzYxYxY" 3 true
    _ = rotationWord (word (rotationSignedWord "YxzYxYxYxzxyXYZXyxyxyZX")) :=
      rotationStep "YxzYxYxYxzxzyxYXyxyxyZX" "YxzYxYxYxzxyXYZXyxyxyZX" "YxzYxYxYxzxy" 6 false
    _ = rotationWord (word (rotationSignedWord "YxzYxYxYxxYXZYZXyxyxyZX")) :=
      rotationStep "YxzYxYxYxzxyXYZXyxyxyZX" "YxzYxYxYxxYXZYZXyxyxyZX" "YxzYxYxYxx" 5 false
    _ = rotationWord (word (rotationSignedWord "YxzYxYxYXYXZYZXyxyxyZX")) :=
      rotationStep "YxzYxYxYxxYXZYZXyxyxyZX" "YxzYxYxYXYXZYZXyxyxyZX" "YxzYxYxY" 0 false
    _ = rotationWord (word (rotationSignedWord "YxzYxYxYXYXyzyXyxyxyZX")) :=
      rotationStep "YxzYxYxYXYXZYZXyxyxyZX" "YxzYxYxYXYXyzyXyxyxyZX" "YxzYxYxYXYX" 4 true
    _ = rotationWord (word (rotationSignedWord "YxzYxYxYXYXyzyxxyxyxyZX")) :=
      rotationStep "YxzYxYxYXYXyzyXyxyxyZX" "YxzYxYxYXYXyzyxxyxyxyZX" "YxzYxYxYXYXyzy" 0 true
    _ = rotationWord (word (rotationSignedWord "YxzYxYxYXYXyzyxYXYXYXZX")) :=
      rotationStep "YxzYxYxYXYXyzyxxyxyxyZX" "YxzYxYxYXYXyzyxYXYXYXZX" "YxzYxYxYXYXyzyx" 7 false
    _ = rotationWord (word (rotationSignedWord "YxzYxYxYXYXyyXYZXYXYXZX")) :=
      rotationStep "YxzYxYxYXYXyzyxYXYXYXZX" "YxzYxYxYXYXyyXYZXYXYXZX" "YxzYxYxYXYXyy" 6 false

end

end GroupApproximation.LiteralBaseP13RotationReplay

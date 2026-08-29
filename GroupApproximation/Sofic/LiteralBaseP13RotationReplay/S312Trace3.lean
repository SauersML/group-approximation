import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.S312Trace2

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem s312Trace3 :
    rotationWord (word (rotationSignedWord "xYxzYxYxzYXXyZXyyZXyxyxyZx")) =
      rotationWord (word (rotationSignedWord "xYYZYxyxZXy")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "xYxzYxYXyXXZYXy")) := s312Trace2
    _ = rotationWord (word (rotationSignedWord "xYxzYxYXyXzxzxYXy")) :=
      rotationStep "xYxzYxYXyXXZYXy" "xYxzYxYXyXzxzxYXy" "xYxzYxYXyXz" 3 true
    _ = rotationWord (word (rotationSignedWord "xYxzYxYXXZxYzxYXy")) :=
      rotationStep "xYxzYxYXyXzxzxYXy" "xYxzYxYXXZxYzxYXy" "xYxzYxYXy" 5 false
    _ = rotationWord (word (rotationSignedWord "xYxzYxYxZxYzxYXy")) :=
      rotationStep "xYxzYxYXXZxYzxYXy" "xYxzYxYxZxYzxYXy" "xYxzYxY" 0 true
    _ = rotationWord (word (rotationSignedWord "xYxzYxYxZxYZxYXy")) :=
      rotationStep "xYxzYxYxZxYzxYXy" "xYxzYxYxZxYZxYXy" "xYxzYxYxZxY" 2 false
    _ = rotationWord (word (rotationSignedWord "xYxzYxYxzxYZxYXy")) :=
      rotationStep "xYxzYxYxZxYZxYXy" "xYxzYxYxzxYZxYXy" "xYxzYxYx" 2 true
    _ = rotationWord (word (rotationSignedWord "xYxzYxYZXZYZxYXy")) :=
      rotationStep "xYxzYxYxzxYZxYXy" "xYxzYxYZXZYZxYXy" "xYxzYxY" 3 false
    _ = rotationWord (word (rotationSignedWord "xYxzYxYZXyzyxYXy")) :=
      rotationStep "xYxzYxYZXZYZxYXy" "xYxzYxYZXyzyxYXy" "xYxzYxYZX" 4 true
    _ = rotationWord (word (rotationSignedWord "xYxzYxYZXyyXYZXy")) :=
      rotationStep "xYxzYxYZXyzyxYXy" "xYxzYxYZXyyXYZXy" "xYxzYxYZXyy" 6 false
    _ = rotationWord (word (rotationSignedWord "xYxzYxYZXYXYZXy")) :=
      rotationStep "xYxzYxYZXyyXYZXy" "xYxzYxYZXYXYZXy" "xYxzYxYZX" 1 false
    _ = rotationWord (word (rotationSignedWord "xYxzYxYzXYXYZXy")) :=
      rotationStep "xYxzYxYZXYXYZXy" "xYxzYxYzXYXYZXy" "xYxzYxY" 2 true
    _ = rotationWord (word (rotationSignedWord "xYxzyyxYzXYXYZXy")) :=
      rotationStep "xYxzYxYzXYXYZXy" "xYxzyyxYzXYXYZXy" "xYxz" 1 true
    _ = rotationWord (word (rotationSignedWord "xYxzyZyXYXYXYZXy")) :=
      rotationStep "xYxzyyxYzXYXYZXy" "xYxzyZyXYXYXYZXy" "xYxzyZy" 6 false
    _ = rotationWord (word (rotationSignedWord "xYxzyzyXYXYXYZXy")) :=
      rotationStep "xYxzyZyXYXYXYZXy" "xYxzyzyXYXYXYZXy" "xYxzy" 2 true
    _ = rotationWord (word (rotationSignedWord "xYxYZXYXYXYZXy")) :=
      rotationStep "xYxzyzyXYXYXYZXy" "xYxYZXYXYXYZXy" "xYxz" 4 false
    _ = rotationWord (word (rotationSignedWord "xYxYzXYXYXYZXy")) :=
      rotationStep "xYxYZXYXYXYZXy" "xYxYzXYXYXYZXy" "xYxY" 2 true
    _ = rotationWord (word (rotationSignedWord "xYxYzyxyxyxZXy")) :=
      rotationStep "xYxYzXYXYXYZXy" "xYxYzyxyxyxZXy" "xYxYzX" 7 true
    _ = rotationWord (word (rotationSignedWord "xYYZyyxyxZXy")) :=
      rotationStep "xYxYzyxyxyxZXy" "xYYZyyxyxZXy" "xYx" 6 false
    _ = rotationWord (word (rotationSignedWord "xYYZYxyxZXy")) :=
      rotationStep "xYYZyyxyxZXy" "xYYZYxyxZXy" "xYYZ" 1 false

end

end GroupApproximation.LiteralBaseP13RotationReplay

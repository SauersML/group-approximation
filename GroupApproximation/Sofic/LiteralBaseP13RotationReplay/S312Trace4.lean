import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.S312Trace3

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem s312Trace4 :
    rotationWord (word (rotationSignedWord "xYxzYxYxzYXXyZXyyZXyxyxyZx")) =
      rotationWord (word (rotationSignedWord "")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "xYYZYxyxZXy")) := s312Trace3
    _ = rotationWord (word (rotationSignedWord "xYzyzxyxZXy")) :=
      rotationStep "xYYZYxyxZXy" "xYzyzxyxZXy" "xYY" 4 true
    _ = rotationWord (word (rotationSignedWord "YZyXzxyxZXy")) :=
      rotationStep "xYzyzxyxZXy" "YZyXzxyxZXy" "x" 6 false
    _ = rotationWord (word (rotationSignedWord "YZXZxxZXy")) :=
      rotationStep "YZyXzxyxZXy" "YZXZxxZXy" "YZy" 5 false
    _ = rotationWord (word (rotationSignedWord "YZXZXZXy")) :=
      rotationStep "YZXZxxZXy" "YZXZXZXy" "YZXZ" 0 false
    _ = rotationWord (word (rotationSignedWord "")) :=
      rotationStep "YZXZXZXy" "" "Y" 3 true

end

end GroupApproximation.LiteralBaseP13RotationReplay

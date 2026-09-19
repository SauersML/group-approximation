import GroupApproximation.Sofic.LiteralBaseP13RotationReplay
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O31_32Trace1

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem o31_32Trace2 :
    rotationWord (word (rotationSignedWord "xYxzYzYXYXXyZXyyxyZx")) =
      rotationWord (word (rotationSignedWord "xYZxYzyxyZX")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "xYxyxZxYXYXZYxyZx")) := o31_32Trace1
    _ = rotationWord (word (rotationSignedWord "xYxyxxyXzYXZYxyZx")) :=
      rotationStep "xYxyxZxYXYXZYxyZx" "xYxyxxyXzYXZYxyZx" "xYxyxxy" 5 true
    _ = rotationWord (word (rotationSignedWord "xYxyXyXzYXZYxyZx")) :=
      rotationStep "xYxyxxyXzYXZYxyZx" "xYxyXyXzYXZYxyZx" "xYxy" 0 false
    _ = rotationWord (word (rotationSignedWord "xYxyXyXzYXZYxyzx")) :=
      rotationStep "xYxyXyXzYXZYxyZx" "xYxyXyXzYXZYxyzx" "xYxyXyXzYXZYxy" 2 true
    _ = rotationWord (word (rotationSignedWord "xYxyXyXzYXZYxyXZXZ")) :=
      rotationStep "xYxyXyXzYXZYxyzx" "xYxyXyXzYXZYxyXZXZ" "xYxyXyXzYXZYxyX" 3 false
    _ = rotationWord (word (rotationSignedWord "xYxyXyXzYXZYxyXzXZ")) :=
      rotationStep "xYxyXyXzYXZYxyXZXZ" "xYxyXyXzYXZYxyXzXZ" "xYxyXyXzYXZYxyX" 2 true
    _ = rotationWord (word (rotationSignedWord "xYxyXyXzYXZYZxYXXZ")) :=
      rotationStep "xYxyXyXzYXZYxyXzXZ" "xYxyXyXzYXZYZxYXXZ" "xYxyXyXzYXZYZx" 5 false
    _ = rotationWord (word (rotationSignedWord "xYxyXyXzYXZYZxYxZ")) :=
      rotationStep "xYxyXyXzYXZYZxYXXZ" "xYxyXyXzYXZYZxYxZ" "xYxyXyXzYXZYZxY" 0 true
    _ = rotationWord (word (rotationSignedWord "xYxyXyXzYXyzyxYxZ")) :=
      rotationStep "xYxyXyXzYXZYZxYxZ" "xYxyXyXzYXyzyxYxZ" "xYxyXyXzYX" 4 true
    _ = rotationWord (word (rotationSignedWord "xYxyXyXzYXyyXYZxZ")) :=
      rotationStep "xYxyXyXzYXyzyxYxZ" "xYxyXyXzYXyyXYZxZ" "xYxyXyXzYXyy" 6 false
    _ = rotationWord (word (rotationSignedWord "xYxyXyXzYXYXYZxZ")) :=
      rotationStep "xYxyXyXzYXyyXYZxZ" "xYxyXyXzYXYXYZxZ" "xYxyXyXzYX" 1 false
    _ = rotationWord (word (rotationSignedWord "xYxyXyXzYXYXYzxZ")) :=
      rotationStep "xYxyXyXzYXYXYZxZ" "xYxyXyXzYXYXYzxZ" "xYxyXyXzYXYXY" 2 true
    _ = rotationWord (word (rotationSignedWord "xYxyXyXzYXYXYzxz")) :=
      rotationStep "xYxyXyXzYXYXYzxZ" "xYxyXyXzYXYXYzxz" "xYxyXyXzYXYXYzx" 2 true
    _ = rotationWord (word (rotationSignedWord "xYxyXyXzYXYXYXZX")) :=
      rotationStep "xYxyXyXzYXYXYzxz" "xYxyXyXzYXYXYXZX" "xYxyXyXzYXYXYz" 3 false
    _ = rotationWord (word (rotationSignedWord "xYxyXyXzxyxyxyZX")) :=
      rotationStep "xYxyXyXzYXYXYXZX" "xYxyXyXzxyxyxyZX" "xYxyXyXz" 7 true
    _ = rotationWord (word (rotationSignedWord "xYxyXXZxxyxyZX")) :=
      rotationStep "xYxyXyXzxyxyxyZX" "xYxyXXZxxyxyZX" "xYxyXy" 5 false
    _ = rotationWord (word (rotationSignedWord "xYxyXXZXyxyZX")) :=
      rotationStep "xYxyXXZxxyxyZX" "xYxyXXZXyxyZX" "xYxyXXZ" 0 false
    _ = rotationWord (word (rotationSignedWord "xYxyXzxzyxyZX")) :=
      rotationStep "xYxyXXZXyxyZX" "xYxyXzxzyxyZX" "xYxyXX" 3 true
    _ = rotationWord (word (rotationSignedWord "xYZxYzyxyZX")) :=
      rotationStep "xYxyXzxzyxyZX" "xYZxYzyxyZX" "xYxy" 5 false

end

end GroupApproximation.LiteralBaseP13RotationReplay

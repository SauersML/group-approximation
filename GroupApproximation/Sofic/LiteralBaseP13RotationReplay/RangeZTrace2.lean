import GroupApproximation.Sofic.LiteralBaseP13RotationReplay
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.RangeZTrace1
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O21_31

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem rangeZTrace2 :
    rotationWord (word (rotationSignedWord "YxzYXZXYXyXyZXyXYxzYzYXYXyZXyXXyZXyzYXYZ")) =
      rotationWord (word (rotationSignedWord "YxzYxyxzxxzyXyxyZXZxY")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "YxzYxyZXyzYXyZXyxyZXyzyyXYZ")) := rangeZTrace1
    _ = rotationWord (word (rotationSignedWord "YxzYxyZXyzYXyZXyxyZXZYZyXYZ")) :=
      rotationStep "YxzYxyZXyzYXyZXyxyZXyzyyXYZ" "YxzYxyZXyzYXyZXyxyZXZYZyXYZ" "YxzYxyZXyzYXyZXyxyZX" 4 false
    _ = rotationWord (word (rotationSignedWord "YxzYxyZXyzYXyZXyxyZXZxY")) :=
      rotationStep "YxzYxyZXyzYXyZXyxyZXZYZyXYZ" "YxzYxyZXyzYXyZXyxyZXZxY" "YxzYxyZXyzYXyZXyxyZXZYZy" 6 true
    _ = rotationWord (word (rotationSignedWord "YxzYxyZXyzyyXyZXyxyZXZxY")) :=
      rotationStep "YxzYxyZXyzYXyZXyxyZXZxY" "YxzYxyZXyzyyXyZXyxyZXZxY" "YxzYxyZXyz" 1 true
    _ = rotationWord (word (rotationSignedWord "YxzYxyZXZYZyXyZXyxyZXZxY")) :=
      rotationStep "YxzYxyZXyzyyXyZXyxyZXZxY" "YxzYxyZXZYZyXyZXyxyZXZxY" "YxzYxyZX" 4 false
    _ = rotationWord (word (rotationSignedWord "YxzYxyZXZxYzyyZXyxyZXZxY")) :=
      rotationStep "YxzYxyZXZYZyXyZXyxyZXZxY" "YxzYxyZXZxYzyyZXyxyZXZxY" "YxzYxyZXZx" 6 true
    _ = rotationWord (word (rotationSignedWord "YxzYxyZXZxYzYZXyxyZXZxY")) :=
      rotationStep "YxzYxyZXZxYzyyZXyxyZXZxY" "YxzYxyZXZxYzYZXyxyZXZxY" "YxzYxyZXZxYz" 1 false
    _ = rotationWord (word (rotationSignedWord "YxzYxyZXZxYZYZXyxyZXZxY")) :=
      rotationStep "YxzYxyZXZxYzYZXyxyZXZxY" "YxzYxyZXZxYZYZXyxyZXZxY" "YxzYxyZXZxY" 2 false
    _ = rotationWord (word (rotationSignedWord "YxzYxyZXZxzyXyxyZXZxY")) :=
      rotationStep "YxzYxyZXZxYZYZXyxyZXZxY" "YxzYxyZXZxzyXyxyZXZxY" "YxzYxyZXZxY" 4 true
    _ = rotationWord (word (rotationSignedWord "YxzYxyxzxxzyXyxyZXZxY")) :=
      rotationStep "YxzYxyZXZxzyXyxyZXZxY" "YxzYxyxzxxzyXyxyZXZxY" "YxzYxy" 3 true

end

end GroupApproximation.LiteralBaseP13RotationReplay

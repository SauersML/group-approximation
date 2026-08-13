import GroupApproximation.Sofic.LiteralBaseP13RotationReplay

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem o31_32Trace1 :
    rotationWord (word (rotationSignedWord "xYxzYzYXYXXyZXyyxyZx")) =
      rotationWord (word (rotationSignedWord "xYxyxZxYXYXZYxyZx")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "xYxzYzYXYxyZXyyxyZx")) :=
      rotationStep "xYxzYzYXYXXyZXyyxyZx" "xYxzYzYXYxyZXyyxyZx" "xYxzYzYXY" 0 true
    _ = rotationWord (word (rotationSignedWord "xYxzYzYXYxyZXYxyZx")) :=
      rotationStep "xYxzYzYXYxyZXyyxyZx" "xYxzYzYXYxyZXYxyZx" "xYxzYzYXYxyZX" 1 false
    _ = rotationWord (word (rotationSignedWord "xYxZYzYXYxyZXYxyZx")) :=
      rotationStep "xYxzYzYXYxyZXYxyZx" "xYxZYzYXYxyZXYxyZx" "xYx" 2 false
    _ = rotationWord (word (rotationSignedWord "xYxZYZYXYxyZXYxyZx")) :=
      rotationStep "xYxZYzYXYxyZXYxyZx" "xYxZYZYXYxyZXYxyZx" "xYxZY" 2 false
    _ = rotationWord (word (rotationSignedWord "xYxyzXYxyZXYxyZx")) :=
      rotationStep "xYxZYZYXYxyZXYxyZx" "xYxyzXYxyZXYxyZx" "xYx" 4 true
    _ = rotationWord (word (rotationSignedWord "xYxyzXYxYYZXYxyZx")) :=
      rotationStep "xYxyzXYxyZXYxyZx" "xYxyzXYxYYZXYxyZx" "xYxyzXYx" 1 false
    _ = rotationWord (word (rotationSignedWord "xYxyzXYxYzyzyXYxyZx")) :=
      rotationStep "xYxyzXYxYYZXYxyZx" "xYxyzXYxYzyzyXYxyZx" "xYxyzXYxYz" 4 true
    _ = rotationWord (word (rotationSignedWord "xYxyzXYYZyXzyXYxyZx")) :=
      rotationStep "xYxyzXYxYzyzyXYxyZx" "xYxyzXYYZyXzyXYxyZx" "xYxyzXYx" 6 false
    _ = rotationWord (word (rotationSignedWord "xYxyzXyZyXzyXYxyZx")) :=
      rotationStep "xYxyzXYYZyXzyXYxyZx" "xYxyzXyZyXzyXYxyZx" "xYxyzX" 1 true
    _ = rotationWord (word (rotationSignedWord "xYxyzXyZyXZyXYxyZx")) :=
      rotationStep "xYxyzXyZyXzyXYxyZx" "xYxyzXyZyXZyXYxyZx" "xYxyzXyZyX" 2 false
    _ = rotationWord (word (rotationSignedWord "xYxyzXyzyXZyXYxyZx")) :=
      rotationStep "xYxyzXyZyXZyXYxyZx" "xYxyzXyzyXZyXYxyZx" "xYxyzXy" 2 true
    _ = rotationWord (word (rotationSignedWord "xYxyzXZYZXZyXYxyZx")) :=
      rotationStep "xYxyzXyzyXZyXYxyZx" "xYxyzXZYZXZyXYxyZx" "xYxyzX" 4 false
    _ = rotationWord (word (rotationSignedWord "xYxyzXZYxzxyXYxyZx")) :=
      rotationStep "xYxyzXZYZXZyXYxyZx" "xYxyzXZYxzxyXYxyZx" "xYxyzXZY" 3 true
    _ = rotationWord (word (rotationSignedWord "xYxyzXZYxxYXZYxyZx")) :=
      rotationStep "xYxyzXZYxzxyXYxyZx" "xYxyzXZYxxYXZYxyZx" "xYxyzXZYxx" 5 false
    _ = rotationWord (word (rotationSignedWord "xYxyzXZYXYXZYxyZx")) :=
      rotationStep "xYxyzXZYxxYXZYxyZx" "xYxyzXZYXYXZYxyZx" "xYxyzXZY" 0 false
    _ = rotationWord (word (rotationSignedWord "xYxyZXZYXYXZYxyZx")) :=
      rotationStep "xYxyzXZYXYXZYxyZx" "xYxyZXZYXYXZYxyZx" "xYxy" 2 false
    _ = rotationWord (word (rotationSignedWord "xYxyxzxYXYXZYxyZx")) :=
      rotationStep "xYxyZXZYXYXZYxyZx" "xYxyxzxYXYXZYxyZx" "xYxy" 3 true
    _ = rotationWord (word (rotationSignedWord "xYxyxZxYXYXZYxyZx")) :=
      rotationStep "xYxyxzxYXYXZYxyZx" "xYxyxZxYXYXZYxyZx" "xYxyx" 2 false

end

end GroupApproximation.LiteralBaseP13RotationReplay

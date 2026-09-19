import GroupApproximation.Sofic.LiteralBaseP13RotationReplay
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O31_32Trace2

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem o31_32Trace3 :
    rotationWord (word (rotationSignedWord "xYxzYzYXYXXyZXyyxyZx")) =
      rotationWord (word (rotationSignedWord "")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "xYZxYzyxyZX")) := o31_32Trace2
    _ = rotationWord (word (rotationSignedWord "xYZYZyyZX")) :=
      rotationStep "xYZxYzyxyZX" "xYZYZyyZX" "xYZx" 6 false
    _ = rotationWord (word (rotationSignedWord "xzyyyZX")) :=
      rotationStep "xYZYZyyZX" "xzyyyZX" "xY" 4 true
    _ = rotationWord (word (rotationSignedWord "")) :=
      rotationStep "xzyyyZX" "" "xz" 1 false

end

end GroupApproximation.LiteralBaseP13RotationReplay

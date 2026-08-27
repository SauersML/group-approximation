import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O31_32Trace3

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem o31_32Image_eq_one :
    rotationWord (word (rotationSignedWord "xYxzYzYXYXXyZXyyxyZx")) = 1 := by
  calc
    _ = rotationWord (word (rotationSignedWord "")) := o31_32Trace3
    _ = 1 := by rfl

end

end GroupApproximation.LiteralBaseP13RotationReplay

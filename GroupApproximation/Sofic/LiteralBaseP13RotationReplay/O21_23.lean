import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O21_23Trace3

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem o21_23Image_eq_one :
    rotationWord (word (rotationSignedWord "YxyxzXYxzYZXYXyyZXyx")) = 1 := by
  calc
    _ = rotationWord (word (rotationSignedWord "")) := o21_23Trace3
    _ = 1 := by rfl

end

end GroupApproximation.LiteralBaseP13RotationReplay

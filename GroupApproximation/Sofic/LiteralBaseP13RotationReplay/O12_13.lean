import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O12_13Trace1

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem o12_13Image_eq_one :
    rotationWord (word (rotationSignedWord "YxzYzYXYxyZXyyxyZX")) = 1 := by
  calc
    _ = rotationWord (word (rotationSignedWord "")) := o12_13Trace1
    _ = 1 := by rfl

end

end GroupApproximation.LiteralBaseP13RotationReplay

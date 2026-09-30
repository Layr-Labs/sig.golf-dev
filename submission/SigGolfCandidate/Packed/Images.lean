import SigGolfCandidate.Packed.Codec
import SigGolfCandidate.Images
import SigGolfCandidate.Expand.Loop

/-!
# Executable RV64 images for 6398-byte signatures

Signing runs the old signer through its final success preparation at PC 2799.
At PC 2800 it permutes the 6404-byte raw signature into the witness scratch
buffer, copies the first 6384 witness bytes back into the signature buffer,
packs the five witness counters into fourteen bytes, and halts.

Expansion copies the 6384-byte body straight into the witness buffer and
unpacks the fourteen-byte counter trailer into five 32-bit words.
-/

namespace SigGolfCandidate.Packed.Images

open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv

/-- Initialize x6 to witness 0x800, x7 to signature 0x2650, and x8 to 1596
    32-bit words. -/
def signBodyPrelude : List (BitVec 32) :=
  [0x00001337, 0x80030313, 0x000023b7, 0x65038393, 0x63c00413]

/-- At loop exit, x6 = witness counter tail 0x20F0 and x7 = signature trailer
    0x3F40. The high two bytes of the second store lie outside the 6398-byte
    signature and are ignored by its reader. -/
def signCounterPrelude : List (BitVec 32) :=
  [0x00002337, 0x0f030313, 0x000043b7, 0xf4038393]

def signCounterPack : List (BitVec 32) :=
  [0x00036483, 0x02849493, 0x0284d493, 0x00436503, 0x02a51513,
   0x01255513, 0x00a4e5b3, 0x00836683, 0x02e69193, 0x0035e5b3,
   0x0126d613, 0x00f00193, 0x00367633, 0x00c36703, 0x02a71713,
   0x02675713, 0x00e66633, 0x01036783, 0x02a79793, 0x0107d793,
   0x00f66633, 0x00b3b023, 0x00c3b423, 0x00100293, 0x00000513, 0x00000073]

def signCode : List (BitVec 32) :=
  SigGolfCandidate.Images.signCode.take 2800 ++
  SigGolfCandidate.Images.expandCode.take 120 ++
  signBodyPrelude ++ SigGolfCandidate.Expand.loopCode ++
  signCounterPrelude ++ signCounterPack

def signImage : Riscv.Image := ⟨signCode, SigGolfCandidate.Images.signData⟩

/-- Copy the body from signature 0x2650 to witness 0x800. -/
def expandBodyPrelude : List (BitVec 32) :=
  [0x00002337, 0x65030313, 0x000013b7, 0x80038393, 0x63c00413]

/-- Reestablish absolute trailer pointers after the body-copy loop. -/
def expandCounterPrelude : List (BitVec 32) :=
  [0x00004337, 0xf4030313, 0x000023b7, 0x0f038393]

/-- At loop exit, x6 = packed trailer 0x3F40 and x7 = witness counter tail
    0x20F0. Only the low 48 bits of the second 64-bit load are consumed. -/
def expandCounterUnpack : List (BitVec 32) :=
  [0x00033483, 0x00833503, 0x02849593, 0x0285d593, 0x00b3a023,
   0x01249593, 0x02a5d593, 0x00b3a223, 0x02e4d593, 0x03c51613,
   0x02a65613, 0x00c5e5b3, 0x00b3a423, 0x02651593, 0x02a5d593,
   0x00b3a623, 0x01051593, 0x02a5d593, 0x00b3a823, 0x00100293,
   0x00000513, 0x00000073]

def expandCode : List (BitVec 32) :=
  expandBodyPrelude ++ SigGolfCandidate.Expand.loopCode ++
  expandCounterPrelude ++ expandCounterUnpack

def expandImage : Riscv.Image := ⟨expandCode, []⟩

theorem sign_valid :
    signImage.Valid sizes SigGolfCandidate.Images.layout := by decide +kernel

theorem expand_valid :
    expandImage.Valid sizes SigGolfCandidate.Images.layout := by decide +kernel

end SigGolfCandidate.Packed.Images

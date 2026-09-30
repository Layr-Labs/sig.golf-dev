import SigGolfCandidate.Verify.Post

/-! # Short names for symbolic words -/

namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

def cw (n : Nat) : E := .c (BitVec.ofNat 64 n)
def ldE (a : Nat) : E := .ld (cw a)
def stW (a : Nat) (v : E) : E := .bin (.st .w 4) (ldE a) v
def stW0 (a : Nat) (v : E) : E := .bin (.st .w 0) (ldE a) v

end SigGolfCandidate.Verify

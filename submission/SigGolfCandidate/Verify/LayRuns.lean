import SigGolfCandidate.Verify.LayBase

/-!
# The layer section: expected results of its code blocks

Instruction indices (`verify.lst`): `layers` 4096, `lay_loop` 4121, encoding ECALL 4164,
`chain_loop` 4211, `step_loop` 4221 (ECALL 4222), `step_done` 4225, leaf ECALL 4239,
`fold_loop` 4248 (ECALL 4271), compare 4281, HALT(0) 4289, `reject` 30 (ECALL 32).

Buffers: EB = 256 (encoding, `M` at EB+32), EO = 320 (answers), CB = 192 (chain block, value at
CB+48), NB = 448 (node block), LB = 832 (leaf, chain ends at LB+32+16 i), DIG8 = 1920 (digits).
-/

namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

def kv (r : Reg) (n : Nat) : Reg × Word := (r, BitVec.ofNat 64 n)
def wk (a : Nat) (v : E) : Addr × E := (⟨none, BitVec.ofNat 64 a⟩, v)

/-! ## Prologue (4096 → 4121) -/

def proK : List (Reg × Word) := [(.x5, 0), (.x19, 0x1978)]
def proMem : List (Addr × E) :=
  [wk 472 (cw 0), wk 464 (cw 0), wk 216 (cw 0), wk 208 (cw 0), wk 1400 (cw 0), wk 1392 (cw 0),
    wk 1384 (cw 0), wk 1376 (cw 0)]
def proSpec : Spec := ⟨[], proMem, 4121, false, 25, [], none⟩
def layK (lay : Nat) : List (Reg × Word) := gkY ++ [kv .x8 lay, kv .x11 64]

/-! ## Route and encoding (4121 → ECALL 4164) -/

def eE (lay : Nat) : E := .bin .and (.bin .srl (.reg .x22) (cw (sT lay))) (cw (2 ^ hT lay - 1))
def tauE (lay : Nat) : E := .bin .srl (.reg .x22) (cw (sT lay + hT lay))
def t6E (lay : Nat) : E := .bin .add (tauE lay) (.bin .sll (eE lay) (cw 32))
/-- The counter `c_lay` (`lwu` of `WIT + 6040 + 4 lay`). -/
def ctrL (lay : Nat) : E := .un (.ld .wu (4 * (lay % 2))) (ldE (8088 + 8 * (lay / 2)))

def headSteps (lay : Nat) : Nat := if lay = 0 then 32 else if lay < 4 then 36 else 34
def headMem (lay : Nat) : List (Addr × E) :=
  [wk 312 (cw 0), wk 304 (ctrL lay), wk 264 (t6E lay), wk 256 (cw (1025 + 65536 * lay))]
def headSpec (lay : Nat) : Spec :=
  ⟨[(.x13, eE lay), (.x30, tauE lay), (.x31, t6E lay)], headMem lay, 4164, true, headSteps lay, [], none⟩
/-- Known after the route: `s0`, `s1 = h`, `a0 = EB`, `a1`, `a2 = EO`, `s7 = lay << 16`, `s8 = body`. -/
def encK (lay : Nat) : List (Reg × Word) :=
  gkY ++ [kv .x8 lay, kv .x9 (hT lay), kv .x10 256, kv .x11 64, kv .x12 320, kv .x23 (65536 * lay),
    kv .x24 (bodyA lay)]

/-! ## Encoding check, digits, chain setup (4165 → 4211) -/

def aE : E := ldE 320
def bE : E := ldE 328
def nibE : E := .c nibW
def laneE : E := .c laneW
def sw1 : E :=
  .bin .add (.bin .add (.bin .add (.bin .and (.bin .srl aE (cw 4)) nibE) (.bin .and aE nibE))
    (.bin .and (.bin .srl bE (cw 4)) nibE)) (.bin .and bE nibE)
def sw2 : E := .bin .add sw1 (.bin .srl sw1 (cw 8))
def sw3 : E := .bin .and sw2 laneE
def sw4 : E := .bin .add sw3 (.bin .srl sw3 (cw 16))
def sw5 : E := .bin .add sw4 (.bin .srl sw4 (cw 32))
/-- `(swar & 1023) - 312`. -/
def swF : E := .bin .add (.bin .and sw5 (cw 1023)) (.c (-312#64))

def shr4 : Nat → E → E
  | 0, e => e
  | n + 1, e => .bin .srl (shr4 n e) (cw 4)
def digE (i : Nat) : E := .bin .and (shr4 (i % 16) (if i < 16 then aE else bE)) (cw 15)
def digMem : List (Addr × E) := (List.range 32).reverse.map fun i => wk (1920 + 8 * i) (digE i)

def encMem (lay : Nat) : List (Addr × E) :=
  [wk 192 (.bin (.st .w 4) (stW0 192 (cw (257 + 65536 * lay))) (cw 0)), wk 232 (cw 0), wk 224 (cw 0),
    wk 200 (.reg .x31)] ++ digMem
def encSpec (lay : Nat) : Spec := ⟨[], encMem lay, 4211, false, 196, [⟨.ne, swF, .c 0, false⟩], none⟩
def rejSpecY (steps : Nat) (brs : List Br) : Spec :=
  ⟨[(.x5, cw 1), (.x10, cw 1)], [], 32, true, steps, brs, none⟩
def encRej : Spec := rejSpecY 24 [⟨.ne, swF, .c 0, true⟩]

/-- Known in the chain loop at chain `i` (besides the per-layer registers). -/
def chK (i : Nat) : List (Reg × Word) := gkY ++ [kv .x10 192, kv .x11 64, kv .x12 240, kv .x25 i, kv .x29 15]
def chK0 (lay : Nat) : List (Reg × Word) :=
  gkY ++ [kv .x8 lay, kv .x9 (hT lay), kv .x10 192, kv .x11 64, kv .x12 240, kv .x23 (65536 * lay),
    kv .x24 (bodyA lay), kv .x25 0, kv .x29 15]

/-! ## Chains -/

def wAt (o : Nat) : E := .ld (addC (.reg .x24) (BitVec.ofNat 64 o))
def cHeadMem (i : Nat) : List (Addr × E) :=
  [wk 192 (.bin (.st .b 5) (ldE 192) (cw i)), wk 248 (wAt (16 * i + 8)), wk 240 (wAt (16 * i))]
def cHeadSpec (i : Nat) (d : Bool) : Spec :=
  ⟨[(.x26, ldE (1920 + 8 * i))], cHeadMem i, if d then 4225 else 4221, false, 10,
    [⟨.eq, ldE (1920 + 8 * i), cw 15, d⟩], none⟩
def cHeadObl (i : Nat) : List Oblig :=
  [.valid ⟨some (.reg .x24), BitVec.ofNat 64 (16 * i + 8)⟩ 8, .valid ⟨some (.reg .x24), BitVec.ofNat 64 (16 * i)⟩ 8]
/-- Registers of the layer kept through the chain loop. -/
def layKeep : List Reg := [.x8, .x9, .x13, .x23, .x24, .x30, .x31]

def stepK : List (Reg × Word) := gkY ++ [kv .x10 192, kv .x11 64, kv .x12 240, kv .x29 15]
def stepSpec : Spec := ⟨[], [wk 192 (.bin (.st .b 4) (ldE 192) (.reg .x26))], 4222, true, 1, [], none⟩
def stepEndSpec (d : Bool) : Spec :=
  ⟨[(.x26, addC (.reg .x26) 1)], [], if d then 4221 else 4225, false, 2,
    [⟨.ne, addC (.reg .x26) 1, cw 15, d⟩], none⟩
def cEndSpec (i : Nat) : Spec :=
  ⟨[], [wk (872 + 16 * i) (ldE 248), wk (864 + 16 * i) (ldE 240)], if i + 1 < 32 then 4211 else 4233,
    false, 8, [], none⟩

/-! ## Leaf, folds -/

def leafK (lay : Nat) : List (Reg × Word) :=
  gkY ++ [kv .x8 lay, kv .x9 (hT lay), kv .x23 (65536 * lay), kv .x24 (bodyA lay)]
def leafSpecY (lay : Nat) : Spec := ⟨[], [wk 840 (.reg .x31), wk 832 (cw (513 + 65536 * lay))], 4239, true, 6, [], none⟩
def leafPost (lay : Nat) : List (Reg × Word) := leafK lay ++ [kv .x10 832, kv .x11 576, kv .x12 320]

def sibA (lay l : Nat) : Nat := bodyA lay + 512 + 16 * l
def foldK (lay l : Nat) : List (Reg × Word) :=
  leafK lay ++ [kv .x10 448, kv .x11 64, kv .x12 320, kv .x25 l, kv .x26 (sibA lay l)]
def fsetSpec (lay : Nat) : Spec :=
  ⟨[], [wk 456 (stW0 456 (.reg .x30)), wk 448 (cw (769 + 65536 * lay))], 4248, false, 8, [], none⟩

def heapE (lay l : Nat) : E := addC (.bin .srl (.reg .x13) (cw (l + 1))) (BitVec.ofNat 64 (2 ^ (hT lay - (l + 1))))
def bitE (l : Nat) : E := .bin .and (.bin .srl (.reg .x13) (cw l)) (cw 1)
def foldMem (lay l : Nat) (d : Bool) : List (Addr × E) :=
  (if d then [wk 504 (ldE 328), wk 496 (ldE 320), wk 488 (ldE (sibA lay l + 8)), wk 480 (ldE (sibA lay l))]
   else [wk 504 (ldE (sibA lay l + 8)), wk 496 (ldE (sibA lay l)), wk 488 (ldE 328), wk 480 (ldE 320)]) ++
  [wk 456 (stW 456 (heapE lay l))]
def foldSpec (lay l : Nat) (d : Bool) : Spec :=
  ⟨[], foldMem lay l d, 4271, true, if d then 18 else 19, [⟨.ne, bitE l, cw 0, d⟩], none⟩

def fendSpec (lay l : Nat) : Spec :=
  if l + 1 < hT lay then ⟨[], [], 4248, false, 3, [], none⟩
  else ⟨[], [wk 296 (ldE 328), wk 288 (ldE 320)], if lay = 0 then 4281 else 4121, false, 9, [], none⟩
def fendPost (lay l : Nat) : List (Reg × Word) :=
  if l + 1 < hT lay then foldK lay (l + 1) else if lay = 0 then gkY else layK (lay - 1)

/-! ## Compare (4281) -/

def cmpAcc : Spec :=
  ⟨[(.x5, cw 1), (.x10, cw 0)], [], 4289, true, 8,
    [⟨.ne, ldE 296, ldE 168, false⟩, ⟨.ne, ldE 288, ldE 160, false⟩], none⟩
def cmpR1 : Spec := rejSpecY 6 [⟨.ne, ldE 288, ldE 160, true⟩]
def cmpR2 : Spec := rejSpecY 9 [⟨.ne, ldE 296, ldE 168, true⟩, ⟨.ne, ldE 288, ldE 160, false⟩]

/-! ## The checks -/

def proCheck : Bool :=
  match runAt proK [4121] 4096 [] with
  | none => false
  | some r =>
    listBeq pairBeq r.st.mem proMem && r.pc.toNat == (pcOf 4121).toNat && !r.ecall && r.steps == 25 &&
      r.cycles == 25 && r.brs.isEmpty && r.spc.isNone && r.st.obl.isEmpty &&
      knownB (layK 5) r && keepB [.x22] r

def headCheck (lay : Nat) : Bool := yspecB (runAt (layK lay) [] 4121 []) (headSpec lay) [] (encK lay) []

def encCheck (lay : Nat) : Bool :=
  yspecB (runAt (encK lay) [4211] 4165 [.br false]) (encSpec lay) [] (chK0 lay) [.x13, .x30, .x31] &&
  specB [] (runAt (encK lay) [4211] 4165 [.br true]) encRej [] []

def leafCheckY (lay : Nat) : Bool :=
  yspecB (runAt (leafK lay) [] 4233 []) (leafSpecY lay) [] (leafPost lay) [.x13, .x30, .x31] &&
  yspecB (runAt (leafPost lay) [4248] 4240 []) (fsetSpec lay) [] (foldK lay 0) [.x13, .x30]

def foldCheckY (lay l : Nat) : Bool :=
  yspecB (runAt (foldK lay l) [] 4248 [.br true]) (foldSpec lay l true) [] (foldK lay l) [.x13, .x30] &&
  yspecB (runAt (foldK lay l) [] 4248 [.br false]) (foldSpec lay l false) [] (foldK lay l) [.x13, .x30] &&
  yspecB (runAt (foldK lay l) [4248, 4121, 4281] 4272 []) (fendSpec lay l) [] (fendPost lay l) [.x13, .x30]

def layCheck (lay : Nat) : Bool :=
  headCheck lay && encCheck lay && leafCheckY lay && (List.range (hT lay)).all (foldCheckY lay)

def chainCheckY (i : Nat) : Bool :=
  yspecB (runAt (chK i) [4221, 4225] 4211 [.br true]) (cHeadSpec i true) (cHeadObl i) (chK i) layKeep &&
  yspecB (runAt (chK i) [4221, 4225] 4211 [.br false]) (cHeadSpec i false) (cHeadObl i) (chK i) layKeep &&
  yspecB (runAt (chK i) [4211, 4233] 4225 []) (cEndSpec i) [] (chK (i + 1)) layKeep

def stepCheck : Bool :=
  yspecB (runAt stepK [] 4221 []) stepSpec [] stepK (.x25 :: .x26 :: layKeep) &&
  yspecB (runAt stepK [4221, 4225] 4223 [.br true]) (stepEndSpec true) [] stepK (.x25 :: layKeep) &&
  yspecB (runAt stepK [4221, 4225] 4223 [.br false]) (stepEndSpec false) [] stepK (.x25 :: layKeep)

def cmpCheck : Bool :=
  specB [] (runAt gkY [] 4281 [.br false, .br false]) cmpAcc [] [] &&
  specB [] (runAt gkY [] 4281 [.br true]) cmpR1 [] [] &&
  specB [] (runAt gkY [] 4281 [.br false, .br true]) cmpR2 [] []

end SigGolfCandidate.Verify

import SigGolfCandidate.Verify.PorsMem
import SigGolfCandidate.Verify.Swar4

/-!
# The hypertree layer section (instructions 4096 ..): invariant, checked runs, expected results

The layer section is a loop over the layers `lay = 5 .. 0` (register `s0 = x8`). Its code blocks
are checked by the kernel as path runs (`runAt`) against expected results (`Spec`), one per value
of the loop indices that address memory (`lay`, the chain `i`, the fold level `l`); data (the
leaf index `idx` in `x22`, route values, hash answers, digits) stays symbolic.

The global invariant `GY` of the section: the constant registers `gkY` (`t0 = 0`, `s3`, the SWAR
masks), `s6 = idx`, the witness from byte 128 on (the digit table `DIG8 = 1920 + 8 i` overlaps
the first 128 witness bytes, which the layers do not read), the public key, and the zero words
`zY` (the `P` slots of CB, EB, NB, LB and the leaf padding `LB + 544 .. 576`). Every run writes
only constant addresses below `0x880`, never the public key, and `zY` only with zeros (`memOKY`).
-/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-! ## Parameters -/

/-- Layer heights (layer 0 = top), `height`. -/
def hT (lay : Nat) : Nat := [11, 5, 5, 5, 4, 4].getD lay 0
/-- `shiftBelow`. -/
def sT (lay : Nat) : Nat := [23, 18, 13, 8, 4, 0].getD lay 0
/-- Address of layer `lay`'s witness body, `WIT + witLayerOff lay`. -/
def bodyA (lay : Nat) : Nat := [4472, 5160, 5752, 6344, 6936, 7512].getD lay 0

theorem hT_eq (lay : Nat) (h : lay < 6) : hT lay = height lay := by
  interval_cases lay <;> rfl

theorem sT_eq (lay : Nat) (h : lay < 6) : sT lay = shiftBelow lay := by
  interval_cases lay <;> decide

theorem bodyA_eq (lay : Nat) (h : lay < 6) : bodyA lay = 0x800 + witLayerOff lay := by
  interval_cases lay <;> decide

theorem hT_bounds (lay : Nat) (h : lay < 6) : 4 ≤ hT lay ∧ hT lay ≤ 11 ∧ sT lay + hT lay ≤ 34 ∧
    4 ≤ sT lay + hT lay := by
  interval_cases lay <;> decide

theorem route_eqY (idx lay : Nat) (h : lay < 6) :
    route idx lay = (idx / 2 ^ sT lay % 2 ^ hT lay, idx / 2 ^ (sT lay + hT lay)) := by
  unfold route
  rw [← hT_eq lay h, ← sT_eq lay h]

def nibW : Word := BitVec.ofNat 64 nibM
def laneW : Word := BitVec.ofNat 64 laneM

/-! ## The global invariant -/

/-- Constant registers of the layer section. -/
def gkY : List (Reg × Word) := [(.x5, 0), (.x19, 0x1978), (.x20, nibW), (.x21, laneW)]

/-- Zero words: the `P` slots of CB, EB, NB, LB and the leaf padding `LB + 544 .. 576`. -/
def zY : List Nat := [0xD0, 0xD8, 0x110, 0x118, 0x1D0, 0x1D8, 0x350, 0x358, 0x560, 0x568, 0x570, 0x578]

structure GY (wl pk : List Byte) (idx : Nat) (s : MachineState) : Prop where
  k : KnownOK gkY s
  x22 : s.getReg .x22 = BitVec.ofNat 64 idx
  wit : ∀ j, 16 ≤ j → j < 880 → s.getMem (BitVec.ofNat 64 (0x800 + 8 * j)) = w64 (slice wl (8 * j) 8)
  pk : PkOK pk s
  z : ∀ a ∈ zY, s.getMem (BitVec.ofNat 64 a) = 0

def safeY (n : Nat) : Bool := decide (n + 8 ≤ 0x880) && n != 0xA0 && n != 0xA8

def memOKY (ws : SymMem) : Bool :=
  ws.all fun p => p.1.base.isNone && safeY p.1.off.toNat &&
    (!(zY.contains p.1.off.toNat) || E.beq p.2 (cw 0))

theorem memOKY_const {ws : SymMem} (h : memOKY ws = true) : (ws.all fun p => p.1.base.isNone) = true := by
  simp only [memOKY, List.all_eq_true, Bool.and_eq_true] at h ⊢
  intro p hp; exact (h p hp).1.1

theorem memOKY_frame {ws : SymMem} (h : memOKY ws = true) (s : MachineState) (A : Nat) (hA : A < 2 ^ 64)
    (hp : 0x880 ≤ A ∨ A = 0xA0 ∨ A = 0xA8) :
    memEval s ws (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
  rw [memEval_look s ws A hA (memOKY_const h)]
  split
  · rename_i v hv
    obtain ⟨p, hp', -, hoff, -⟩ := memLook_mem hv
    simp only [memOKY, List.all_eq_true, Bool.and_eq_true] at h
    have := (h p hp').1.2
    simp only [safeY, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at this
    rw [hoff] at this
    omega
  · rfl

theorem memOKY_zero {ws : SymMem} (h : memOKY ws = true) (s : MachineState) (A : Nat) (hA : A ∈ zY)
    (h0 : s.getMem (BitVec.ofNat 64 A) = 0) : memEval s ws (BitVec.ofNat 64 A) = 0 := by
  have hA' : A < 2 ^ 64 := by simp [zY] at hA; omega
  rw [memEval_look s ws A hA' (memOKY_const h)]
  split
  · rename_i v hv
    obtain ⟨p, hp', -, hoff, hv'⟩ := memLook_mem hv
    simp only [memOKY, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    rcases (h p hp').2 with h2 | h2
    · rw [hoff] at h2; simp [List.contains_iff_mem, hA] at h2
    · rw [← hv', E.beq_eq h2]; rfl
  · exact h0

/-! ## Checked runs -/

def yspecB (o : Option PRes) (sp : Spec) (obl : List Oblig) (post : List (Reg × Word))
    (keep : List Reg) : Bool :=
  match o with
  | none => false
  | some r =>
    regsB r sp.regs && listBeq pairBeq r.st.mem sp.mem && r.pc.toNat == (pcOf sp.pc).toNat &&
      r.ecall == sp.ecall && r.steps == sp.steps && r.cycles == sp.steps &&
      listBeq Br.beq r.brs sp.brs && r.spc.isNone && listBeq Oblig.beq r.st.obl obl &&
      memOKY r.st.mem && regsOK gkY r.st.regs && knownB post r && keepB (.x22 :: keep) r

/-- What a checked layer run gives on a concrete state. -/
structure YRes (sp : Spec) (post : List (Reg × Word)) (keep : List Reg) (s t : MachineState) : Prop where
  steps : Steps image s sp.steps sp.steps t
  ecall : sp.ecall = true → fetch image t = some (.base .ECALL)
  gk : KnownOK gkY t
  known : KnownOK post t
  keep : ∀ x ∈ (.x22 :: keep), t.getReg x = s.getReg x
  regs : ∀ p ∈ sp.regs, t.getReg p.1 = p.2.eval s
  mem : ∀ A, t.getMem A = memEval s sp.mem A
  memc : memOKY sp.mem = true
  pc : t.pc = pcOf sp.pc

theorem yspec_run {known post : List (Reg × Word)} {stops : List Nat} {n : Nat} {dirs : List Dir}
    {sp : Spec} {obl : List Oblig} {keep : List Reg}
    (h : yspecB (runAt known stops n dirs) sp obl post keep = true)
    (s : MachineState) (hpc : s.pc = pcOf n) (hk : KnownOK known s)
    (hbr : ∀ b ∈ sp.brs, b.holds s) (hob : ∀ o ∈ obl, o.holds s) :
    ∃ t, YRes sp post keep s t := by
  unfold yspecB at h
  split at h
  · cases h
  rename_i r hr
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hregs, hmem⟩, hpc'⟩, hec⟩, hst⟩, hcy⟩, hbrs⟩, hspc⟩, hobl⟩, hmok⟩, hrok⟩, hkn⟩,
    hkeep⟩ := h
  have hbrs' := listBeq_eq (fun _ _ => Br.beq_eq) hbrs
  have hmem' := listBeq_eq (fun _ _ => pairBeq_eq) hmem
  have hobl' := listBeq_eq (fun _ _ => Oblig.beq_eq) hobl
  have hspc0 : r.spc = none := by simpa using hspc
  obtain ⟨hst', hec'⟩ := pathRun_sound hr vlook_ok s hpc hk (by rw [hobl']; exact hob)
    (by rw [hbrs']; exact hbr)
  refine ⟨r.toState s, ⟨?_, ?_, knownB_ok hrok s, knownB_ok hkn s, keepB_ok hkeep s, ?_, ?_, ?_, ?_⟩⟩
  · rw [hcy, hst] at hst'; exact hst'
  · intro he; exact hec' (hec.trans he)
  · intro p hp
    rw [PRes.toState_getReg, E.beq_eq (List.all_eq_true.mp hregs p hp)]
  · intro A; rw [PRes.toState_getMem, hmem']
  · rw [← hmem']; exact hmok
  · rw [PRes.toState_pc _ _ hspc0, BitVec.eq_of_toNat_eq hpc']

theorem GY.step {wl pk : List Byte} {idx : Nat} {sp : Spec} {post : List (Reg × Word)} {keep : List Reg}
    {s t : MachineState} (hG : GY wl pk idx s) (h : YRes sp post keep s t) : GY wl pk idx t := by
  refine ⟨h.gk, ?_, fun j hj1 hj2 => ?_, ?_, fun a ha => ?_⟩
  · rw [h.keep .x22 (by simp)]; exact hG.x22
  · rw [h.mem, memOKY_frame h.memc s _ (by omega) (Or.inl (by omega))]; exact hG.wit j hj1 hj2
  · refine ⟨?_, ?_⟩
    · rw [show (0xA0 : Word) = BitVec.ofNat 64 0xA0 from rfl, h.mem,
        memOKY_frame h.memc s _ (by omega) (by omega)]; exact hG.pk.1
    · rw [show (0xA8 : Word) = BitVec.ofNat 64 0xA8 from rfl, h.mem,
        memOKY_frame h.memc s _ (by omega) (by omega)]; exact hG.pk.2
  · rw [h.mem]; exact memOKY_zero h.memc s a ha (hG.z a ha)

theorem GY.hash {wl pk : List Byte} {idx : Nat} {s : MachineState} (hG : GY wl pk idx s)
    (ans : BitVec 256) (d : Nat) (hd : s.getReg .x12 = BitVec.ofNat 64 d)
    (hd1 : d + 32 ≤ 0x880) (hz : ∀ a ∈ zY, a + 8 ≤ d ∨ d + 32 ≤ a) (hpk : 0xA8 + 8 ≤ d) :
    GY wl pk idx (writeHash s ans) := by
  have fr : ∀ A, A < 2 ^ 64 → (A + 8 ≤ d ∨ d + 32 ≤ A) →
      (writeHash s ans).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) :=
    fun A hA hp => writeHash_frame s ans d A hd hA (by omega) hp
  refine ⟨Known_writeHash hG.k ans, by rw [writeHash_getReg]; exact hG.x22, fun j hj1 hj2 => ?_, ?_,
    fun a ha => ?_⟩
  · rw [fr _ (by omega) (Or.inr (by omega))]; exact hG.wit j hj1 hj2
  · exact ⟨(fr 0xA0 (by omega) (by omega)).trans hG.pk.1, (fr 0xA8 (by omega) (by omega)).trans hG.pk.2⟩
  · have : a < 2 ^ 64 := by simp [zY] at ha; omega
    rw [fr a this (hz a ha)]; exact hG.z a ha

/-! ## Memory lists with constant keys -/

theorem memEval_ofNat (s : MachineState) (k A : Nat) (v : E) (ws : SymMem) (hA : A < 2 ^ 64)
    (hk : k < 2 ^ 64) :
    memEval s ((⟨none, BitVec.ofNat 64 k⟩, v) :: ws) (BitVec.ofNat 64 A) =
      if A = k then v.eval s else memEval s ws (BitVec.ofNat 64 A) := by
  rw [memEval_cons]
  split
  · rename_i h1
    have : A = k := (ofNat_eq_iff hA hk).mp h1
    rw [if_pos this]
  · rename_i h1
    rw [if_neg]
    intro h2; exact h1 (by rw [h2]; rfl)

theorem memEval_ofNat_ne (s : MachineState) (k A : Nat) (v : E) (ws : SymMem) (hA : A < 2 ^ 64)
    (hk : k < 2 ^ 64) (h : A ≠ k) :
    memEval s ((⟨none, BitVec.ofNat 64 k⟩, v) :: ws) (BitVec.ofNat 64 A) = memEval s ws (BitVec.ofNat 64 A) := by
  rw [memEval_ofNat s k A v ws hA hk, if_neg h]

theorem memEval_ofNat_eq (s : MachineState) (k A : Nat) (v : E) (ws : SymMem) (hA : A < 2 ^ 64)
    (h : A = k) :
    memEval s ((⟨none, BitVec.ofNat 64 k⟩, v) :: ws) (BitVec.ofNat 64 A) = v.eval s := by
  rw [memEval_ofNat s k A v ws hA (by omega), if_pos h]

/-- A write list that misses `A`. -/
theorem memEval_miss (s : MachineState) (ws : SymMem) (A : Nat) (hA : A < 2 ^ 64)
    (h : ∀ p ∈ ws, p.1.base = none ∧ p.1.off.toNat ≠ A) :
    memEval s ws (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) :=
  memEval_frame_ofNat s ws A hA h

end SigGolfCandidate.Verify

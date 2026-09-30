import SigGolfCandidate.Verify.LayEval

/-!
# The layer section: machine invariants at the block boundaries and the block steps

* `LaysIn`: at `layers` (4096), from the PORS root tail (the PORS root `M` at EB+32);
* `LayIn c M`: at `lay_loop` (4121) for layer `c.lay`, with its message `M` at EB+32;
* `EncOut c a`: after the encoding hash (answer `a` at EO);
* `ChIn c xs i ends`: before chain `i` (`chain_loop`, or the leaf code for `i = 32`), the digits
  `xs` at DIG8, the chain ends `ends` of chains `0 .. i-1` at LB+32;
* `StIn`/`SdIn`: in the step loop of chain `i` (position `x`, value `v` at CB+48) / at `step_done`;
* `LeafOut c a`: after the leaf hash; `FoldIn c l v`/`FoldEnd c l v`: fold level `l` before / after
  its hash (current node `v` at EO); `FinalIn`: at the comparison, the top root at EB+32.
-/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-! ## Helpers -/

theorem memEval_look_some {s : MachineState} {ws : SymMem} {A : Nat} {v : E} (hA : A < 2 ^ 64)
    (hc : (ws.all fun p => p.1.base.isNone) = true) (h : memLook ws A = some v) :
    memEval s ws (BitVec.ofNat 64 A) = v.eval s := by
  rw [memEval_look s ws A hA hc, h]

theorem memEval_look_none {s : MachineState} {ws : SymMem} {A : Nat} (hA : A < 2 ^ 64)
    (hc : (ws.all fun p => p.1.base.isNone) = true) (h : memLook ws A = none) :
    memEval s ws (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
  rw [memEval_look s ws A hA hc, h]

theorem known_mem {known : List (Reg × Word)} {s : MachineState} (h : KnownOK known s) {r : Reg} {n : Nat}
    (hm : kv r n ∈ known) : s.getReg r = BitVec.ofNat 64 n := h _ hm

theorem KnownOK.sub {k1 k2 : List (Reg × Word)} {s : MachineState} (h : KnownOK k2 s)
    (hs : ∀ p ∈ k1, p ∈ k2) : KnownOK k1 s := fun p hp => h p (hs p hp)

theorem gkY_x5 {s : MachineState} (h : KnownOK gkY s) : s.getReg .x5 = 0 := h (.x5, 0) (by simp [gkY])

theorem zY_mem {wl pk : List Byte} {idx : Nat} {s : MachineState} (hG : GY wl pk idx s) (a : Nat)
    (ha : a ∈ zY := by decide) : s.getMem (BitVec.ofNat 64 a) = 0 := hG.z a ha

theorem ofNat_zero64 : (BitVec.ofNat 64 0 : Word) = 0 := rfl

/-- A write list with constant keys below `B` misses every address `≥ B`. -/
theorem memEval_above (s : MachineState) (ws : SymMem) (B A : Nat) (hA : A < 2 ^ 64) (hB : B ≤ A)
    (h : (ws.all fun p => p.1.base.isNone && decide (p.1.off.toNat < B)) = true) :
    memEval s ws (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
  apply memEval_frame_ofNat s ws A hA
  intro p hp
  have := List.all_eq_true.mp h p hp
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, decide_eq_true_eq] at this
  exact ⟨this.1, by omega⟩

/-! ## Inclusions of the known-register lists -/

theorem sub_leafK_chK0 (lay : Nat) : ∀ p ∈ leafK lay, p ∈ chK0 lay := by
  intro p hp
  simp only [leafK, chK0, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp ⊢
  rcases hp with hp | hp | hp | hp | hp
  · exact Or.inl hp
  all_goals (subst hp; simp)

theorem sub_chK_chK0 (lay : Nat) : ∀ p ∈ chK 0, p ∈ chK0 lay := by
  intro p hp
  simp only [chK, chK0, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp ⊢
  rcases hp with hp | hp | hp | hp | hp | hp
  · exact Or.inl hp
  all_goals (subst hp; simp)

/-! ## Invariants -/

/-- At `lay_loop` for layer `c.lay`. -/
structure LayIn (c : YCtx) (M : Val) (s : MachineState) : Prop where
  g : GY c.wl c.pk c.idx s
  k : KnownOK (layK c.lay) s
  m0 : s.getMem (BitVec.ofNat 64 288) = vw0 M
  m1 : s.getMem (BitVec.ofNat 64 296) = vw1 M
  ml : M.length = 16
  pc : s.pc = pcOf 4121

/-- The route registers of layer `c.lay`. -/
structure RouteRegs (c : YCtx) (s : MachineState) : Prop where
  e : s.getReg .x13 = BitVec.ofNat 64 c.e
  tau : s.getReg .x30 = BitVec.ofNat 64 c.tau
  t6 : s.getReg .x31 = BitVec.ofNat 64 c.t6

structure EncOut (c : YCtx) (a : BitVec 256) (s : MachineState) : Prop where
  g : GY c.wl c.pk c.idx s
  k : KnownOK (encK c.lay) s
  r : RouteRegs c s
  a0 : s.getMem (BitVec.ofNat 64 320) = a.extractLsb' 0 64
  a1 : s.getMem (BitVec.ofNat 64 328) = a.extractLsb' 64 64
  pc : s.pc = pcOf 4165

/-- The chain-loop state common to all its blocks. -/
structure ChBase (c : YCtx) (xs : List Nat) (i : Nat) (ends : List Val) (s : MachineState) : Prop where
  g : GY c.wl c.pk c.idx s
  k : KnownOK (leafK c.lay) s
  r : RouteRegs c s
  w200 : s.getMem (BitVec.ofNat 64 200) = BitVec.ofNat 64 c.t6
  w224 : s.getMem (BitVec.ofNat 64 224) = 0
  w232 : s.getMem (BitVec.ofNat 64 232) = 0
  dig : ∀ j, j < 32 → s.getMem (BitVec.ofNat 64 (1920 + 8 * j)) = BitVec.ofNat 64 (xs.getD j 0)
  xlt : ∀ j, j < 32 → xs.getD j 0 < 16
  elen : ends.length = i
  ev : ∀ j, j < i → s.getMem (BitVec.ofNat 64 (864 + 16 * j)) = vw0 (ends.getD j []) ∧
    s.getMem (BitVec.ofNat 64 (872 + 16 * j)) = vw1 (ends.getD j [])
  el : ∀ v ∈ ends, v.length = 16

structure ChIn (c : YCtx) (xs : List Nat) (i : Nat) (ends : List Val) (s : MachineState) : Prop where
  b : ChBase c xs i ends s
  k2 : KnownOK (chK i) s
  cb : ∃ b d, b < 256 ∧ d < 256 ∧ s.getMem (BitVec.ofNat 64 192) = cbW c.lay b d
  pc : s.pc = pcOf (if i < 32 then 4211 else 4233)

structure StIn (c : YCtx) (xs : List Nat) (i : Nat) (ends : List Val) (x : Nat) (v : Val)
    (s : MachineState) : Prop where
  b : ChBase c xs i ends s
  k2 : KnownOK (chK i) s
  cb : ∃ b, b < 256 ∧ s.getMem (BitVec.ofNat 64 192) = cbW c.lay b i
  x26 : s.getReg .x26 = BitVec.ofNat 64 x
  hx : x < 15
  v0 : s.getMem (BitVec.ofNat 64 240) = vw0 v
  v1 : s.getMem (BitVec.ofNat 64 248) = vw1 v
  vl : v.length = 16
  pc : s.pc = pcOf 4221

structure SdIn (c : YCtx) (xs : List Nat) (i : Nat) (ends : List Val) (v : Val) (s : MachineState) : Prop where
  b : ChBase c xs i ends s
  k2 : KnownOK (chK i) s
  cb : ∃ b, b < 256 ∧ s.getMem (BitVec.ofNat 64 192) = cbW c.lay b i
  v0 : s.getMem (BitVec.ofNat 64 240) = vw0 v
  v1 : s.getMem (BitVec.ofNat 64 248) = vw1 v
  vl : v.length = 16
  pc : s.pc = pcOf 4225

/-- The frame of the chain-loop state: the words it describes. -/
def ChProt (i A : Nat) : Prop :=
  A = 200 ∨ A = 224 ∨ A = 232 ∨ (1920 ≤ A ∧ A < 2176) ∨ (864 ≤ A ∧ A < 864 + 16 * i)

theorem ChBase.frame {c : YCtx} {xs : List Nat} {i : Nat} {ends : List Val} {s t : MachineState}
    (h : ChBase c xs i ends s) (hG : GY c.wl c.pk c.idx t) (hk : KnownOK (leafK c.lay) t)
    (hr : ∀ x ∈ [Reg.x13, .x30, .x31], t.getReg x = s.getReg x)
    (hm : ∀ A, ChProt i A → t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)) :
    ChBase c xs i ends t := by
  refine ⟨hG, hk, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, fun j hj => ?_, h.xlt, h.elen, fun j hj => ?_, h.el⟩
  · rw [hr .x13 (by simp)]; exact h.r.e
  · rw [hr .x30 (by simp)]; exact h.r.tau
  · rw [hr .x31 (by simp)]; exact h.r.t6
  · rw [hm 200 (by simp [ChProt])]; exact h.w200
  · rw [hm 224 (by simp [ChProt])]; exact h.w224
  · rw [hm 232 (by simp [ChProt])]; exact h.w232
  · rw [hm _ (by unfold ChProt; omega)]; exact h.dig j hj
  · rw [hm _ (by unfold ChProt; omega), hm (872 + 16 * j) (by unfold ChProt; omega)]; exact h.ev j hj

/-! ## Prologue -/

/-- At `layers`, from the PORS root tail. -/
structure LaysIn (wl pk : List Byte) (idx : Nat) (M : Val) (s : MachineState) : Prop where
  g : Glob [] wl pk s
  k : KnownOK proK s
  x22 : s.getReg .x22 = BitVec.ofNat 64 idx
  m0 : s.getMem (BitVec.ofNat 64 288) = vw0 M
  m1 : s.getMem (BitVec.ofNat 64 296) = vw1 M
  ml : M.length = 16
  pc : s.pc = pcOf 4096

theorem pro_run (s : MachineState) (hpc : s.pc = pcOf 4096) (hk : KnownOK proK s) :
    ∃ t, Steps image s 25 25 t ∧ KnownOK (layK 5) t ∧ t.getReg .x22 = s.getReg .x22 ∧
      (∀ A, t.getMem A = memEval s proMem A) ∧ t.pc = pcOf 4121 := by
  have h := proCheck_ok
  unfold proCheck at h
  split at h
  · cases h
  rename_i r hr
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.isEmpty_iff, Option.isNone_iff_eq_none] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hmem, hpc'⟩, hec⟩, hst⟩, hcy⟩, hbrs⟩, hspc⟩, hobl⟩, hkn⟩, hkeep⟩ := h
  have hmem' := listBeq_eq (fun _ _ => pairBeq_eq) hmem
  obtain ⟨hst', -⟩ := pathRun_sound hr vlook_ok s hpc hk (by rw [hobl]; simp) (by rw [hbrs]; simp)
  refine ⟨r.toState s, by rw [hcy, hst] at hst'; exact hst', knownB_ok hkn s,
    keepB_ok hkeep s .x22 (by simp), fun A => by rw [PRes.toState_getMem, hmem'], ?_⟩
  rw [PRes.toState_pc _ _ hspc, BitVec.eq_of_toNat_eq hpc']

theorem proMem_const : (proMem.all fun p => p.1.base.isNone) = true := by decide

theorem pro_step (wl pk : List Byte) (idx : Nat) (M : Val) (s : MachineState) (hs : LaysIn wl pk idx M s) :
    ∃ t, Steps image s 25 25 t ∧ LayIn ⟨wl, pk, idx, 5⟩ M t := by
  obtain ⟨t, hst, hk, h22, hm, hpc⟩ := pro_run s hs.pc hs.k
  have fr : ∀ A, A < 2 ^ 64 → memLook proMem A = none → t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) :=
    fun A hA h => by rw [hm]; exact memEval_look_none hA proMem_const h
  have hG := hs.g
  refine ⟨t, hst, ⟨⟨hk.sub (fun p hp => by simp [layK, hp]), by rw [h22]; exact hs.x22,
    fun j hj1 hj2 => ?_, ?_, fun a ha => ?_⟩, hk, ?_, ?_, hs.ml, hpc⟩⟩
  · rw [hm, memEval_above s proMem 0x800 _ (by omega) (by omega) (by decide)]
    exact hG.2.1 j hj2
  · refine ⟨?_, ?_⟩
    · rw [show (0xA0 : Word) = BitVec.ofNat 64 0xA0 from rfl, fr _ (by omega) rfl]; exact hG.2.2.1.1
    · rw [show (0xA8 : Word) = BitVec.ofNat 64 0xA8 from rfl, fr _ (by omega) rfl]; exact hG.2.2.1.2
  · have hz : ∀ b ∈ pSlots, s.getMem (BitVec.ofNat 64 b) = 0 := hG.2.2.2
    simp only [zY, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | (rw [fr _ (by omega) rfl]; exact hz _ (by decide))
      | (rw [hm, memEval_look_some (by omega) proMem_const rfl]; rfl)
  · rw [fr _ (by omega) rfl]; exact hs.m0
  · rw [fr _ (by omega) rfl]; exact hs.m1

/-! ## Route and encoding -/

theorem head_step (c : YCtx) (hc : c.ok) (M : Val) (s : MachineState) (hs : LayIn c M s) :
    ∃ u, Steps image s (headSteps c.lay) (headSteps c.lay) u ∧
      fetch image u = some (.base .ECALL) ∧ u.getReg .x5 = 0 ∧ hashArgumentsValid u = true ∧
      hashInput u = pad64 (encInput c.lay c.tau c.e M (witCounter c.wl c.lay)) ∧
      ∀ a, EncOut c a (writeHash u a) := by
  have hL := layCheck_at c.lay hc.1
  simp only [layCheck, headCheck, Bool.and_eq_true] at hL
  obtain ⟨u, hu⟩ := yspec_run hL.1.1.1 s hs.pc hs.k (by simp [headSpec]) (by simp)
  have hG := hs.g.step hu
  have hK := hu.known
  have h10 : u.getReg .x10 = BitVec.ofNat 64 256 := known_mem hK (by simp [encK, kv])
  have h11 : u.getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)) := known_mem hK (by simp [encK, kv])
  have h12 : u.getReg .x12 = BitVec.ofNat 64 320 := known_mem hK (by simp [encK, kv])
  have hx22 := hs.g.x22
  have he := c.e_lt hc
  have ht := c.tau_lt hc
  have hlay := hc.1
  have hc_ : (headMem c.lay).all (fun p => p.1.base.isNone) = true := by simp [headMem, wk]
  have hm : ∀ A, A < 2 ^ 64 → u.getMem (BitVec.ofNat 64 A) = memEval s (headMem c.lay) (BitVec.ofNat 64 A) :=
    fun A _ => hu.mem _
  refine ⟨u, hu.steps, hu.ecall rfl, gkY_x5 hu.gk,
    hashArgs_ofNat _ _ _ _ h10 h11 h12 (by omega) (by omega) (by omega) (by decide), ?_, fun a => ?_⟩
  · rw [hashInput_ofNat _ 256 0 h10 h11 (by decide) (by decide), pad64_encInput _ _ _ _ hs.ml]
    congr 1
    simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero,
      Nat.mul_zero, List.cons.injEq]
    refine ⟨?_, ?_, zY_mem hG 272, zY_mem hG 280, ?_, ?_, ?_, ?_, trivial⟩
    · rw [hm _ (by omega), memEval_look_some (by omega) hc_ rfl]
      simp only [Rv.E.eval, cw]
      congr 1; unfold twLo; rw [Nat.div_eq_of_lt (by omega : c.tau < 2 ^ 32)]; omega
    · rw [hm _ (by omega), memEval_look_some (by omega) hc_ rfl, t6E_eval c hc s hx22]
      congr 1; unfold twHi YCtx.t6; omega
    · rw [hm _ (by omega), memEval_look_none (by omega) hc_ rfl]; exact hs.m0
    · rw [hm _ (by omega), memEval_look_none (by omega) hc_ rfl]; exact hs.m1
    · rw [hm _ (by omega), memEval_look_some (by omega) hc_ rfl, ctrL_eval c hc s hs.g.wit]
      have := witCounter_lt c.wl c.lay
      rw [Nat.mod_eq_of_lt this]
    · rw [hm _ (by omega), memEval_look_some (by omega) hc_ rfl]; rfl
  · refine ⟨hG.hash a 320 h12 (by omega) (by decide) (by omega), Known_writeHash hK a, ⟨?_, ?_, ?_⟩,
      writeHash_at0 _ a _ h12 (by omega), writeHash_at8 _ a _ h12 (by omega), ?_⟩
    · rw [writeHash_getReg, hu.regs (.x13, eE c.lay) (by simp [headSpec]), eE_eval c hc s hx22]
    · rw [writeHash_getReg, hu.regs (.x30, tauE c.lay) (by simp [headSpec]), tauE_eval c hc s hx22]
    · rw [writeHash_getReg, hu.regs (.x31, t6E c.lay) (by simp [headSpec]), t6E_eval c hc s hx22]
    · rw [writeHash_pc, hu.pc, pcOf_add4]; rfl

/-! ## Encoding check, digits, chain setup -/

theorem memEval_range_map (s : MachineState) (f : Nat → E) (base : Nat) :
    ∀ n j, j < n → base + 8 * n < 2 ^ 64 →
      memEval s ((List.range n).reverse.map fun i => wk (base + 8 * i) (f i)) (BitVec.ofNat 64 (base + 8 * j)) =
        (f j).eval s := by
  intro n
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj hb
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append, List.map_cons]
    unfold wk
    rw [memEval_ofNat s _ _ _ _ (by omega) (by omega)]
    by_cases h : j = n
    · subst h; rw [if_pos rfl]
    · rw [if_neg (by omega)]; exact ih j (by omega) (by omega)

theorem memEval_digMem (s : MachineState) (j : Nat) (hj : j < 32) :
    memEval s digMem (BitVec.ofNat 64 (1920 + 8 * j)) = (digE j).eval s :=
  memEval_range_map s digE 1920 32 j hj (by norm_num)

theorem br_ne_c0 (e : E) (d : Bool) (s : MachineState) :
    Br.holds s ⟨.ne, e, .c 0, d⟩ ↔ (decide (e.eval s ≠ 0) = d) := by
  simp only [Br.holds, CmpOp.eval, E.eval]
  cases d <;> simp [bne_iff_ne]

theorem br_ne_cw0 (e : E) (d : Bool) (s : MachineState) :
    Br.holds s ⟨.ne, e, cw 0, d⟩ ↔ (decide (e.eval s ≠ 0) = d) := br_ne_c0 e d s

theorem enc_step (c : YCtx) (hc : c.ok) (a : BitVec 256) (s : MachineState) (hs : EncOut c a s) :
    (decodeDigits (answerBytes 16 a) = none → ∃ t, Steps image s 24 24 t ∧
        fetch image t = some (.base .ECALL) ∧ t.getReg .x5 = 1 ∧ t.getReg .x10 = 1) ∧
    (∀ xs, decodeDigits (answerBytes 16 a) = some xs → ∃ t, Steps image s 196 196 t ∧ ChIn c xs 0 [] t) := by
  have hL := layCheck_at c.lay hc.1
  simp only [layCheck, encCheck, Bool.and_eq_true] at hL
  obtain ⟨hacc, hrej⟩ := hL.1.1.2
  have hlay := hc.1
  have hsw : swF.eval s = 0 ↔ (digitsOf (a.extractLsb' 0 64).toNat (a.extractLsb' 64 64).toNat).sum = 312 := by
    rw [swF_eq_zero, hs.a0, hs.a1, digitsOf_sum]
  have hdec := decodeDigits_answer a
  rw [show targetSum = 312 from rfl] at hdec
  constructor
  · intro hn
    have hne : (digitsOf (a.extractLsb' 0 64).toNat (a.extractLsb' 64 64).toNat).sum ≠ 312 := by
      intro h; rw [hdec, if_pos h] at hn; cases hn
    obtain ⟨t, ht⟩ := spec_run hrej s hs.pc hs.k (by
      intro b hb; simp only [encRej, rejSpecY, List.mem_singleton] at hb; subst hb
      rw [br_ne_c0]; simp only [ne_eq, decide_eq_true_eq]; exact fun h => hne (hsw.mp h))
    exact ⟨t, ht.steps, ht.ecall rfl, ht.regs (.x5, cw 1) (by simp [encRej, rejSpecY]),
      ht.regs (.x10, cw 1) (by simp [encRej, rejSpecY])⟩
  · intro xs hxs
    have hsum : (digitsOf (a.extractLsb' 0 64).toNat (a.extractLsb' 64 64).toNat).sum = 312 := by
      by_contra h; rw [hdec, if_neg h] at hxs; cases hxs
    have hx : xs = digitsOf (a.extractLsb' 0 64).toNat (a.extractLsb' 64 64).toNat := by
      rw [hdec, if_pos hsum] at hxs; exact (Option.some.inj hxs).symm
    subst hx
    obtain ⟨t, ht⟩ := yspec_run hacc s hs.pc hs.k (by
      intro b hb; simp only [encSpec, List.mem_singleton] at hb; subst hb
      rw [br_ne_c0]; simp only [ne_eq, decide_eq_false_iff_not, not_not]; exact hsw.mpr hsum) (by simp)
    have hc_ : (encMem c.lay).all (fun p => p.1.base.isNone) = true := by
      simp [encMem, digMem, wk]
    have hK := ht.known
    have hm : ∀ A, t.getMem A = memEval s (encMem c.lay) A := ht.mem
    refine ⟨t, ht.steps, ⟨⟨hs.g.step ht, hK.sub (sub_leafK_chK0 _), ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, fun j hj => ?_,
      fun j hj => digitsOf_lt _ _ j hj, rfl, fun j hj => absurd hj (by omega), fun v hv => by simp at hv⟩,
      hK.sub (sub_chK_chK0 _), ⟨0, 0, by omega, by omega, ?_⟩, by rw [ht.pc]; rfl⟩⟩
    · rw [ht.keep .x13 (by simp)]; exact hs.r.e
    · rw [ht.keep .x30 (by simp)]; exact hs.r.tau
    · rw [ht.keep .x31 (by simp)]; exact hs.r.t6
    · rw [hm, memEval_look_some (by omega) hc_ rfl]; exact hs.r.t6
    · rw [hm, memEval_look_some (by omega) hc_ rfl]; rfl
    · rw [hm, memEval_look_some (by omega) hc_ rfl]; rfl
    · rw [hm]
      simp only [encMem, wk, List.cons_append, List.nil_append]
      rw [memEval_ofNat_ne _ _ _ _ _ (by omega) (by omega) (by omega),
        memEval_ofNat_ne _ _ _ _ _ (by omega) (by omega) (by omega),
        memEval_ofNat_ne _ _ _ _ _ (by omega) (by omega) (by omega),
        memEval_ofNat_ne _ _ _ _ _ (by omega) (by omega) (by omega), memEval_digMem s j hj,
        digE_eval s j hj, hs.a0, hs.a1, digitsOf_getD _ _ j hj]
    · rw [hm, memEval_look_some (by omega) hc_ rfl]
      exact cb_setup _ c.lay hlay

/-! ## Chains -/

theorem wit_body (c : YCtx) (hc : c.ok) (s : MachineState) (hG : GY c.wl c.pk c.idx s) (o : Nat)
    (ho : o < 700) (h8 : o % 8 = 0) :
    s.getMem (BitVec.ofNat 64 (bodyA c.lay + o)) = w64 (slice c.wl (witLayerOff c.lay + o) 8) := by
  have hb := bodyA_eq c.lay hc.1
  have hw : witLayerOff c.lay % 8 = 0 ∧ 2424 ≤ witLayerOff c.lay ∧ witLayerOff c.lay ≤ 5464 := by
    have := hc.1; interval_cases h : c.lay <;> decide
  have := hG.wit ((witLayerOff c.lay + o) / 8) (by omega) (by omega)
  rwa [show 0x800 + 8 * ((witLayerOff c.lay + o) / 8) = bodyA c.lay + o by omega,
    show 8 * ((witLayerOff c.lay + o) / 8) = witLayerOff c.lay + o by omega] at this

theorem witLayerOff_le (lay : Nat) (h : lay < 6) : witLayerOff lay ≤ 5464 := by
  interval_cases lay <;> decide

theorem length_witChain' (c : YCtx) (hc : c.ok) (i : Nat) (hi : i < 32) : (witChain c.wl c.lay i).length = 16 := by
  have := witLayerOff_le c.lay hc.1
  unfold witChain; apply length_slice16; have := hc.2.2.1; omega

theorem witLayerOff_path (lay : Nat) (h : lay < 6) : witLayerOff lay + 512 + 16 * hT lay ≤ 6040 := by
  interval_cases lay <;> decide

theorem length_witSib' (c : YCtx) (hc : c.ok) (l : Nat) (hl : l < hT c.lay) :
    (witSib c.wl c.lay l).length = 16 := by
  have := witLayerOff_path c.lay hc.1
  unfold witSib nChains; apply length_slice16; have := hc.2.2.1; omega

theorem leafK_keep {lay : Nat} {s t : MachineState} (hk : KnownOK (leafK lay) s) (hg : KnownOK gkY t)
    (hr : ∀ x ∈ [Reg.x8, .x9, .x23, .x24], t.getReg x = s.getReg x) : KnownOK (leafK lay) t := by
  intro p hp
  simp only [leafK, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with hp | hp | hp | hp | hp
  · exact hg p hp
  all_goals (subst hp; rw [hr _ (by simp [kv])]; exact hk _ (by simp [leafK]))

theorem valid_x24 (s : MachineState) (lay o : Nat) (hlay : lay < 6) (ho : o < 600) (h8 : o % 8 = 0)
    (h : s.getReg .x24 = BitVec.ofNat 64 (bodyA lay)) :
    Oblig.holds s (.valid ⟨some (.reg .x24), BitVec.ofNat 64 o⟩ 8) := by
  have hb : bodyA lay % 8 = 0 ∧ bodyA lay ≤ 7512 := by interval_cases lay <;> decide
  simp only [Oblig.holds, Addr.eval, E.eval, h, BitVec.ofNat_add_ofNat, accessValid_iff,
    BitVec.toNat_ofNat, MEMORY_BYTES]
  omega

theorem chead_step (c : YCtx) (hc : c.ok) (xs : List Nat) (i : Nat) (hi : i < 32) (ends : List Val)
    (s : MachineState) (hs : ChIn c xs i ends s) :
    (xs.getD i 0 = 15 → ∃ t, Steps image s 10 10 t ∧ SdIn c xs i ends (witChain c.wl c.lay i) t) ∧
    (xs.getD i 0 < 15 → ∃ t, Steps image s 10 10 t ∧
      StIn c xs i ends (xs.getD i 0) (witChain c.wl c.lay i) t) := by
  have hC := chainCheckY_at i hi
  simp only [chainCheckY, Bool.and_eq_true] at hC
  obtain ⟨⟨hT, hF⟩, -⟩ := hC
  have hpc : s.pc = pcOf 4211 := by rw [hs.pc, if_pos hi]
  have h24 : s.getReg .x24 = BitVec.ofNat 64 (bodyA c.lay) := known_mem hs.b.k (by simp [leafK, kv])
  have hx := hs.b.xlt i hi
  have hd := hs.b.dig i hi
  have hob : ∀ o ∈ cHeadObl i, o.holds s := by
    intro o ho
    simp only [cHeadObl, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · exact valid_x24 s c.lay _ hc.1 (by omega) (by omega) h24
    · exact valid_x24 s c.lay _ hc.1 (by omega) (by omega) h24
  have hbr : ∀ d, d = decide (xs.getD i 0 = 15) → ∀ b ∈ (cHeadSpec i d).brs, b.holds s := by
    intro d hdd b hb
    simp only [cHeadSpec, List.mem_singleton] at hb; subst hb
    simp only [Br.holds, CmpOp.eval, ldE, cw, E.eval, hd]
    subst hdd
    generalize xs.getD i 0 = x at hx ⊢
    by_cases h15 : x = 15
    · subst h15; rfl
    · rw [decide_eq_false h15, beq_eq_false_iff_ne]
      intro e; apply h15
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_ofNat] at this; omega
  have post : ∀ d (t : MachineState), YRes (cHeadSpec i d) (chK i) layKeep s t →
      ChBase c xs i ends t ∧ KnownOK (chK i) t ∧ (∃ b, b < 256 ∧ t.getMem (BitVec.ofNat 64 192) = cbW c.lay b i) ∧
      t.getMem (BitVec.ofNat 64 240) = vw0 (witChain c.wl c.lay i) ∧
      t.getMem (BitVec.ofNat 64 248) = vw1 (witChain c.wl c.lay i) ∧
      t.getReg .x26 = BitVec.ofNat 64 (xs.getD i 0) := by
    intro d t ht
    have hm : ∀ A, t.getMem A = memEval s (cHeadMem i) A := ht.mem
    have hcm : (cHeadMem i).all (fun p => p.1.base.isNone) = true := by simp [cHeadMem, wk]
    refine ⟨hs.b.frame (hs.b.g.step ht) (leafK_keep hs.b.k ht.gk (fun x hx => ht.keep x (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> simp [layKeep])))
        (fun x hx => ht.keep x (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl <;> simp [layKeep]))
        (fun A hA => by
          unfold ChProt at hA
          rw [hm, memEval_miss s _ A (by omega) (by
            intro p hp; simp only [cHeadMem, wk, List.mem_cons, List.not_mem_nil, or_false] at hp
            rcases hp with rfl | rfl | rfl <;> simp <;> omega)]),
      ht.known, ?_, ?_, ?_, ?_⟩
    · obtain ⟨b, dd, hb, hdd, h192⟩ := hs.cb
      refine ⟨b, hb, ?_⟩
      rw [hm, memEval_look_some (by omega) hcm rfl]
      simp only [E.eval, BinOp.eval, ldE, cw, h192]
      rw [stB_cb _ _ _ _ hc.1 hb hdd (by omega) 5 (by omega)]; rfl
    · rw [hm, memEval_look_some (by omega) hcm rfl]
      simp only [wAt, E.eval, addC_eval, h24, BitVec.ofNat_add_ofNat, Nat.add_zero]
      rw [show bodyA c.lay + 16 * i = bodyA c.lay + (16 * i) from rfl, wit_body c hc s hs.b.g _ (by omega) (by omega)]
      unfold witChain; rw [vw0_slice]
    · rw [hm, memEval_look_some (by omega) hcm rfl]
      simp only [wAt, E.eval, addC_eval, h24, BitVec.ofNat_add_ofNat]
      rw [show bodyA c.lay + (16 * i + 8) = bodyA c.lay + (16 * i + 8) from rfl,
        wit_body c hc s hs.b.g _ (by omega) (by omega)]
      unfold witChain; rw [vw1_slice, Nat.add_assoc]
    · rw [ht.regs (.x26, ldE (1920 + 8 * i)) (by simp [cHeadSpec])]; exact hd
  refine ⟨fun h15 => ?_, fun h15 => ?_⟩
  · obtain ⟨t, ht⟩ := yspec_run hT s hpc hs.k2 (hbr true (by rw [h15]; rfl)) hob
    obtain ⟨b1, b2, b3, b4, b5, -⟩ := post true t ht
    exact ⟨t, ht.steps, ⟨b1, b2, b3, b4, b5, length_witChain' c hc i hi, ht.pc⟩⟩
  · obtain ⟨t, ht⟩ := yspec_run hF s hpc hs.k2 (hbr false (decide_eq_false (by omega)).symm) hob
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := post false t ht
    exact ⟨t, ht.steps, ⟨b1, b2, b3, b6, h15, b4, b5, length_witChain' c hc i hi, ht.pc⟩⟩

theorem sub_stepK_chK (i : Nat) : ∀ p ∈ stepK, p ∈ chK i := by
  intro p hp
  simp only [stepK, chK, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp ⊢
  rcases hp with hp | hp | hp | hp | hp
  · exact Or.inl hp
  all_goals (subst hp; simp)

theorem chK_x25 {i : Nat} {s t : MachineState} (hk : KnownOK (chK i) s) (hg : KnownOK stepK t)
    (h25 : t.getReg .x25 = s.getReg .x25) : KnownOK (chK i) t := by
  intro p hp
  simp only [chK, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with hp | hp | hp | hp | hp | hp
  · exact hg p (by simp [stepK, hp])
  · subst hp; exact hg _ (by simp [stepK])
  · subst hp; exact hg _ (by simp [stepK])
  · subst hp; exact hg _ (by simp [stepK])
  · subst hp; show t.getReg .x25 = _; rw [h25]; exact hk (kv .x25 i) (by simp [chK])
  · subst hp; exact hg _ (by simp [stepK])

theorem mem4_layKeep : ∀ r ∈ [Reg.x8, .x9, .x23, .x24], r ∈ layKeep := by decide
theorem mem3_layKeep : ∀ r ∈ [Reg.x13, .x30, .x31], r ∈ layKeep := by decide

theorem ofNat_add_one (x : Nat) : BitVec.ofNat 64 x + 1 = BitVec.ofNat 64 (x + 1) := by
  rw [show (1 : Word) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]

theorem cbW_twLo (lay tau x i : Nat) (hlay : lay < 6) (htau : tau < 2 ^ 30) (hx : x < 256) (hi : i < 32) :
    cbW lay x i = BitVec.ofNat 64 (twLo 1 lay tau (x + 1 - 1 + 256 * i)) := by
  unfold cbW twLo
  congr 1
  rw [Nat.div_eq_of_lt (by omega : tau < 2 ^ 32)]
  omega

/-- One chain step: the byte store of `mu - 1 = x`, the hash, the loop test. -/
theorem step_hash (c : YCtx) (hc : c.ok) (xs : List Nat) (i : Nat) (hi : i < 32) (ends : List Val)
    (x : Nat) (v : Val) (s : MachineState) (hs : StIn c xs i ends x v s) :
    ∃ u, Steps image s 1 1 u ∧ fetch image u = some (.base .ECALL) ∧ u.getReg .x5 = 0 ∧
      hashArgumentsValid u = true ∧ hashInput u = fmt (chainInput c.lay c.tau c.e i (x + 1) v) ∧
      ∀ a, (x + 1 < 15 → ∃ t, Steps image (writeHash u a) 2 2 t ∧
          StIn c xs i ends (x + 1) (answerBytes 16 a) t) ∧
        (x + 1 = 15 → ∃ t, Steps image (writeHash u a) 2 2 t ∧ SdIn c xs i ends (answerBytes 16 a) t) := by
  have hS := stepCheck_ok
  simp only [stepCheck, Bool.and_eq_true] at hS
  obtain ⟨⟨h1, hT⟩, hF⟩ := hS
  have hkS : KnownOK stepK s := hs.k2.sub (sub_stepK_chK i)
  obtain ⟨u, hu⟩ := yspec_run h1 s hs.pc hkS (by simp [stepSpec]) (by simp)
  have hGu := hs.b.g.step hu
  have hK := hu.known
  have h10 : u.getReg .x10 = BitVec.ofNat 64 192 := known_mem hK (by simp [stepK, kv])
  have h11 : u.getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)) := known_mem hK (by simp [stepK, kv])
  have h12 : u.getReg .x12 = BitVec.ofNat 64 240 := known_mem hK (by simp [stepK, kv])
  have hm : ∀ A, u.getMem A = memEval s [wk 192 (.bin (.st .b 4) (ldE 192) (.reg .x26))] A := hu.mem
  have hfr : ∀ A, A < 2 ^ 64 → A ≠ 192 → u.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) :=
    fun A hA hne => by rw [hm, wk, memEval_ofNat_ne _ _ _ _ _ hA (by omega) hne]; rfl
  have htau := c.tau_lt hc
  have he := c.e_lt hc
  have hlay := hc.1
  obtain ⟨b, hb, h192⟩ := hs.cb
  have hx := hs.hx
  have hu192 : u.getMem (BitVec.ofNat 64 192) = cbW c.lay x i := by
    rw [hm, wk, memEval_ofNat_eq _ _ _ _ _ (by omega) rfl]
    simp only [E.eval, BinOp.eval, ldE, cw, h192, hs.x26]
    rw [stB_cb _ _ _ _ hlay hb (by omega) (by omega) 4 (by omega)]; rfl
  refine ⟨u, hu.steps, hu.ecall rfl, gkY_x5 hu.gk,
    hashArgs_ofNat _ _ _ _ h10 h11 h12 (by omega) (by omega) (by omega) (by decide), ?_, fun a => ⟨?_, ?_⟩⟩
  · rw [hashInput_ofNat _ 192 0 h10 h11 (by decide) (by decide),
      fmt_chainInput_words _ _ _ _ _ _ hs.vl (by omega) (by omega) (by omega)]
    congr 1
    simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero,
      Nat.mul_zero, List.cons.injEq]
    refine ⟨?_, ?_, zY_mem hGu 208, zY_mem hGu 216, ?_, ?_, ?_, ?_, trivial⟩
    · rw [hu192]; exact cbW_twLo _ _ _ _ hlay htau (by omega) hi
    · rw [hfr _ (by omega) (by omega), hs.b.w200]; congr 1; unfold twHi YCtx.t6; omega
    · rw [hfr _ (by omega) (by omega), hs.b.w224]
    · rw [hfr _ (by omega) (by omega), hs.b.w232]
    · rw [hfr _ (by omega) (by omega), hs.v0]
    · rw [hfr _ (by omega) (by omega), hs.v1]
  all_goals
    intro hx1
    have hw := (writeHash_pc u a).trans (by rw [hu.pc, pcOf_add4])
    have hGw := hGu.hash a 240 h12 (by omega) (by decide) (by omega)
    have hkw : KnownOK stepK (writeHash u a) := Known_writeHash hK a
    have hbr : ∀ d, d = decide (x + 1 ≠ 15) → ∀ b ∈ (stepEndSpec d).brs, b.holds (writeHash u a) := by
      intro d hd br hbr
      simp only [stepEndSpec, List.mem_singleton] at hbr; subst hbr; subst hd
      simp only [Br.holds, CmpOp.eval, addC_eval, E.eval, cw, writeHash_getReg,
        hu.keep .x26 (by simp [layKeep]), hs.x26, ofNat_add_one]
      by_cases h15 : x + 1 = 15
      · rw [h15]; simp
      · rw [decide_eq_true h15, bne_iff_ne]
        intro e; apply h15
        have := congrArg BitVec.toNat e
        simp only [BitVec.toNat_ofNat] at this; omega
    have post : ∀ d (t : MachineState), YRes (stepEndSpec d) stepK (.x25 :: layKeep) (writeHash u a) t →
        ChBase c xs i ends t ∧ KnownOK (chK i) t ∧
        (∃ b, b < 256 ∧ t.getMem (BitVec.ofNat 64 192) = cbW c.lay b i) ∧
        t.getMem (BitVec.ofNat 64 240) = vw0 (answerBytes 16 a) ∧
        t.getMem (BitVec.ofNat 64 248) = vw1 (answerBytes 16 a) ∧
        t.getReg .x26 = BitVec.ofNat 64 (x + 1) := by
      intro d t ht
      have hmt : ∀ A, t.getMem A = (writeHash u a).getMem A := fun A => by
        rw [ht.mem]; cases d <;> rfl
      have hwf : ∀ A, A < 2 ^ 64 → (A + 8 ≤ 240 ∨ 272 ≤ A) →
          (writeHash u a).getMem (BitVec.ofNat 64 A) = u.getMem (BitVec.ofNat 64 A) :=
        fun A hA h => writeHash_frame u a 240 A h12 hA (by omega) h
      have hk25 : t.getReg .x25 = s.getReg .x25 := by
        rw [ht.keep .x25 (by simp), writeHash_getReg, hu.keep .x25 (by simp)]
      refine ⟨hs.b.frame (hGw.step ht) (leafK_keep hs.b.k ht.gk (fun r hr => ?_)) (fun r hr => ?_)
          (fun A hA => ?_), chK_x25 hs.k2 ht.known hk25, ⟨x, by omega, ?_⟩, ?_, ?_, ?_⟩
      · rw [ht.keep r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem4_layKeep r hr))), writeHash_getReg,
          hu.keep r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem4_layKeep r hr))))]
      · rw [ht.keep r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem3_layKeep r hr))), writeHash_getReg,
          hu.keep r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem3_layKeep r hr))))]
      · unfold ChProt at hA
        rw [hmt, hwf A (by omega) (by omega), hfr A (by omega) (by omega)]
      · rw [hmt, hwf _ (by omega) (by omega), hu192]
      · rw [hmt, writeHash_at0 _ a _ h12 (by omega)]; exact (vw0_answer a).symm
      · rw [hmt, show (248 : Nat) = 240 + 8 from rfl, writeHash_at8 _ a _ h12 (by omega)]
        exact (vw1_answer a).symm
      · rw [ht.regs (.x26, addC (.reg .x26) 1) (by cases d <;> simp [stepEndSpec])]
        simp only [addC_eval, E.eval, writeHash_getReg, hu.keep .x26 (by simp [layKeep]), hs.x26,
          ofNat_add_one]
  · obtain ⟨t, ht⟩ := yspec_run hT (writeHash u a) hw hkw (hbr true (by simp; omega)) (by simp)
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := post true t ht
    exact ⟨t, ht.steps, ⟨b1, b2, b3, b6, hx1, b4, b5, by simp, ht.pc⟩⟩
  · obtain ⟨t, ht⟩ := yspec_run hF (writeHash u a) hw hkw (hbr false (by simp; omega)) (by simp)
    obtain ⟨b1, b2, b3, b4, b5, -⟩ := post false t ht
    exact ⟨t, ht.steps, ⟨b1, b2, b3, b4, b5, by simp, ht.pc⟩⟩

theorem cend_step (c : YCtx) (hc : c.ok) (xs : List Nat) (i : Nat) (hi : i < 32) (ends : List Val)
    (v : Val) (s : MachineState) (hs : SdIn c xs i ends v s) :
    ∃ t, Steps image s 8 8 t ∧ ChIn c xs (i + 1) (ends ++ [v]) t := by
  have hC := chainCheckY_at i hi
  simp only [chainCheckY, Bool.and_eq_true] at hC
  obtain ⟨t, ht⟩ := yspec_run hC.2 s hs.pc hs.k2 (by simp [cEndSpec]) (by simp)
  have hm : ∀ A, t.getMem A = memEval s [wk (872 + 16 * i) (ldE 248), wk (864 + 16 * i) (ldE 240)] A := ht.mem
  have hfr : ∀ A, A < 2 ^ 64 → A ≠ 872 + 16 * i → A ≠ 864 + 16 * i →
      t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := fun A hA h1 h2 => by
    rw [hm, wk, wk, memEval_ofNat_ne _ _ _ _ _ hA (by omega) h1, memEval_ofNat_ne _ _ _ _ _ hA (by omega) h2]
    rfl
  have hb := hs.b
  obtain ⟨b, hb', h192⟩ := hs.cb
  have hel := hb.elen
  refine ⟨t, ht.steps, ⟨⟨hb.g.step ht, leafK_keep hb.k ht.gk (fun r hr => ht.keep r
      (List.mem_cons_of_mem _ (mem4_layKeep r hr))), ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, fun j hj => ?_, hb.xlt,
      by simp [hel], fun j hj => ?_, fun w hw => ?_⟩, ht.known, ⟨b, i, hb', by omega, ?_⟩, ht.pc⟩⟩
  · rw [ht.keep .x13 (by simp [layKeep])]; exact hb.r.e
  · rw [ht.keep .x30 (by simp [layKeep])]; exact hb.r.tau
  · rw [ht.keep .x31 (by simp [layKeep])]; exact hb.r.t6
  · rw [hfr _ (by omega) (by omega) (by omega)]; exact hb.w200
  · rw [hfr _ (by omega) (by omega) (by omega)]; exact hb.w224
  · rw [hfr _ (by omega) (by omega) (by omega)]; exact hb.w232
  · rw [hfr _ (by omega) (by omega) (by omega)]; exact hb.dig j hj
  · by_cases hji : j < i
    · have e : (ends ++ [v]).getD j [] = ends.getD j [] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
      rw [e, hfr _ (by omega) (by omega) (by omega), hfr (872 + 16 * j) (by omega) (by omega) (by omega)]
      exact hb.ev j hji
    · have hj : j = i := by omega
      subst hj
      have e : (ends ++ [v]).getD j [] = v := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hel, Nat.sub_self]; rfl
      rw [e, hm, wk, wk, memEval_ofNat_ne _ _ _ _ _ (by omega) (by omega) (by omega),
        memEval_ofNat_eq _ _ _ _ _ (by omega) rfl, hm, wk, wk, memEval_ofNat_eq _ _ _ _ _ (by omega) rfl]
      exact ⟨hs.v0, hs.v1⟩
  · simp only [List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact hb.el w hw
    · exact hs.vl
  · rw [hfr _ (by omega) (by omega) (by omega)]; exact h192

/-! ## Leaf -/

theorem pairs_getElem? (l : List Val) : ∀ k, ((l.map fun v => [vw0 v, vw1 v]).flatten)[k]? =
    if k < 2 * l.length then
      some (if k % 2 = 0 then vw0 (l.getD (k / 2) []) else vw1 (l.getD (k / 2) [])) else none := by
  induction l with
  | nil => intro k; simp
  | cons v l ih =>
    intro k
    simp only [List.map_cons, List.flatten_cons, List.length_cons]
    match k with
    | 0 => simp
    | 1 => simp <;> omega
    | k + 2 =>
      rw [show [vw0 v, vw1 v] ++ (l.map fun v => [vw0 v, vw1 v]).flatten =
        vw0 v :: vw1 v :: (l.map fun v => [vw0 v, vw1 v]).flatten from rfl,
        List.getElem?_cons_succ, List.getElem?_cons_succ, ih k,
        show (k + 2) % 2 = k % 2 by omega, show (k + 2) / 2 = k / 2 + 1 by omega]
      simp only [List.getD_cons_succ]
      split_ifs <;> first | rfl | omega

theorem leaf_words (lay tau e : Nat) (ends : List Val) (hl : ends.length = 32) (u : MachineState)
    (h0 : u.getMem (BitVec.ofNat 64 832) = BitVec.ofNat 64 (twLo 2 lay tau 0))
    (h1 : u.getMem (BitVec.ofNat 64 840) = BitVec.ofNat 64 (twHi tau e))
    (h2 : u.getMem (BitVec.ofNat 64 848) = 0) (h3 : u.getMem (BitVec.ofNat 64 856) = 0)
    (hE : ∀ j, j < 32 → u.getMem (BitVec.ofNat 64 (864 + 16 * j)) = vw0 (ends.getD j []) ∧
      u.getMem (BitVec.ofNat 64 (872 + 16 * j)) = vw1 (ends.getD j []))
    (hZ : ∀ k, k < 4 → u.getMem (BitVec.ofNat 64 (1376 + 8 * k)) = 0) :
    (List.range (8 * (8 + 1))).map (fun j => u.getMem (BitVec.ofNat 64 (832 + 8 * j))) =
      [BitVec.ofNat 64 (twLo 2 lay tau 0), BitVec.ofNat 64 (twHi tau e), 0, 0] ++
        (ends.map fun v => [vw0 v, vw1 v]).flatten ++ [0, 0, 0, 0] := by
  have hF := pairs_getElem? ends
  have hFl : ((ends.map fun v => [vw0 v, vw1 v]).flatten).length = 64 := by
    have h63 := hF 63; have h64 := hF 64
    rw [hl, if_pos (by omega)] at h63; rw [hl, if_neg (by omega)] at h64
    have a1 := List.getElem?_eq_none_iff.mp h64
    have a2 : 63 < ((ends.map fun v => [vw0 v, vw1 v]).flatten).length := by
      by_contra hc; rw [List.getElem?_eq_none (by omega)] at h63; cases h63
    omega
  have key : ∀ n, n < 72 → ([BitVec.ofNat 64 (twLo 2 lay tau 0), BitVec.ofNat 64 (twHi tau e), 0, 0] ++
      (ends.map fun v => [vw0 v, vw1 v]).flatten ++ [0, 0, 0, 0])[n]? =
      some (u.getMem (BitVec.ofNat 64 (832 + 8 * n))) := by
    intro n hn
    by_cases h4 : n < 4
    · rw [List.append_assoc, List.getElem?_append_left (by simp; omega)]
      interval_cases n
      · show _ = some (u.getMem (BitVec.ofNat 64 832)); rw [h0]; rfl
      · show _ = some (u.getMem (BitVec.ofNat 64 840)); rw [h1]; rfl
      · show _ = some (u.getMem (BitVec.ofNat 64 848)); rw [h2]; rfl
      · show _ = some (u.getMem (BitVec.ofNat 64 856)); rw [h3]; rfl
    · rw [List.append_assoc, List.getElem?_append_right (by simp; omega)]
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
      by_cases h68 : n < 68
      · rw [List.getElem?_append_left (by omega), hF, hl, if_pos (by omega)]
        have hj := hE ((n - 4) / 2) (by omega)
        by_cases hp : (n - 4) % 2 = 0
        · rw [if_pos hp, show 832 + 8 * n = 864 + 16 * ((n - 4) / 2) by omega]; exact congrArg some hj.1.symm
        · rw [if_neg hp, show 832 + 8 * n = 872 + 16 * ((n - 4) / 2) by omega]; exact congrArg some hj.2.symm
      · rw [List.getElem?_append_right (by omega), hFl]
        have := hZ (n - 68) (by omega)
        rw [show 832 + 8 * n = 1376 + 8 * (n - 68) by omega, this]
        have : n - 4 - 64 < 4 := by omega
        interval_cases h : n - 4 - 64 <;> rfl
  apply List.ext_getElem?
  intro n
  rw [List.getElem?_map]
  by_cases hn : n < 72
  · rw [List.getElem?_range (by omega)]; exact (key n hn).symm
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp [hFl]; omega)]; rfl

structure LeafOut (c : YCtx) (a : BitVec 256) (s : MachineState) : Prop where
  g : GY c.wl c.pk c.idx s
  k : KnownOK (leafPost c.lay) s
  e : s.getReg .x13 = BitVec.ofNat 64 c.e
  tau : s.getReg .x30 = BitVec.ofNat 64 c.tau
  a0 : s.getMem (BitVec.ofNat 64 320) = a.extractLsb' 0 64
  a1 : s.getMem (BitVec.ofNat 64 328) = a.extractLsb' 64 64
  pc : s.pc = pcOf 4240

theorem leaf_step (c : YCtx) (hc : c.ok) (xs : List Nat) (ends : List Val) (s : MachineState)
    (hs : ChIn c xs 32 ends s) :
    ∃ u, Steps image s 6 6 u ∧ fetch image u = some (.base .ECALL) ∧ u.getReg .x5 = 0 ∧
      hashArgumentsValid u = true ∧ hashInput u = pad64 (leafInput c.lay c.tau c.e ends) ∧
      ∀ a, LeafOut c a (writeHash u a) := by
  have hL := layCheck_at c.lay hc.1
  simp only [layCheck, leafCheckY, Bool.and_eq_true] at hL
  obtain ⟨u, hu⟩ := yspec_run hL.1.2.1 s (by rw [hs.pc]; rfl) hs.b.k (by simp [leafSpecY]) (by simp)
  have hG := hs.b.g.step hu
  have hK := hu.known
  have h10 : u.getReg .x10 = BitVec.ofNat 64 832 := known_mem hK (by simp [leafPost, kv])
  have h11 : u.getReg .x11 = BitVec.ofNat 64 (64 * (8 + 1)) := known_mem hK (by simp [leafPost, kv])
  have h12 : u.getReg .x12 = BitVec.ofNat 64 320 := known_mem hK (by simp [leafPost, kv])
  have hm : ∀ A, u.getMem A = memEval s [wk 840 (.reg .x31), wk 832 (cw (513 + 65536 * c.lay))] A := hu.mem
  have hfr : ∀ A, A < 2 ^ 64 → A ≠ 840 → A ≠ 832 → u.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) :=
    fun A hA h1 h2 => by
      rw [hm, wk, wk, memEval_ofNat_ne _ _ _ _ _ hA (by omega) h1, memEval_ofNat_ne _ _ _ _ _ hA (by omega) h2]; rfl
  have htau := c.tau_lt hc
  have he := c.e_lt hc
  have hlay := hc.1
  have hel := hs.b.elen
  have hvs := hs.b.el
  refine ⟨u, hu.steps, hu.ecall rfl, gkY_x5 hu.gk,
    hashArgs_ofNat _ _ _ _ h10 h11 h12 (by omega) (by omega) (by omega) (by decide), ?_, fun a => ?_⟩
  · rw [hashInput_ofNat _ 832 8 h10 h11 (by decide) (by decide), pad64_leafInput _ _ _ _ hel hvs]
    congr 1
    refine leaf_words _ _ _ ends hel u ?_ ?_ (zY_mem hG 848) (zY_mem hG 856) (fun j hj => ?_) (fun k hk => ?_)
    · rw [hm, wk, wk, memEval_ofNat_ne _ _ _ _ _ (by omega) (by omega) (by omega),
        memEval_ofNat_eq _ _ _ _ _ (by omega) rfl]
      simp only [E.eval, cw]
      congr 1; unfold twLo; rw [Nat.div_eq_of_lt (by omega : c.tau < 2 ^ 32)]; omega
    · rw [hm, wk, wk, memEval_ofNat_eq _ _ _ _ _ (by omega) rfl]
      simp only [E.eval]; rw [hs.b.r.t6]
      congr 1; unfold twHi YCtx.t6; omega
    · rw [hfr _ (by omega) (by omega) (by omega), hfr (872 + 16 * j) (by omega) (by omega) (by omega)]
      exact hs.b.ev j (by omega)
    · exact zY_mem hG _ (by simp only [zY, List.mem_cons, List.not_mem_nil, or_false]; omega)
  · refine ⟨hG.hash a 320 h12 (by omega) (by decide) (by omega), Known_writeHash hK a, ?_, ?_,
      writeHash_at0 _ a _ h12 (by omega), writeHash_at8 _ a _ h12 (by omega), ?_⟩
    · rw [writeHash_getReg, hu.keep .x13 (by simp)]; exact hs.b.r.e
    · rw [writeHash_getReg, hu.keep .x30 (by simp)]; exact hs.b.r.tau
    · rw [writeHash_pc, hu.pc, pcOf_add4]; rfl

/-! ## Folds -/

structure FoldIn (c : YCtx) (l : Nat) (v : Val) (s : MachineState) : Prop where
  g : GY c.wl c.pk c.idx s
  k : KnownOK (foldK c.lay l) s
  e : s.getReg .x13 = BitVec.ofNat 64 c.e
  tau : s.getReg .x30 = BitVec.ofNat 64 c.tau
  w448 : s.getMem (BitVec.ofNat 64 448) = BitVec.ofNat 64 (769 + 65536 * c.lay)
  w456 : (s.getMem (BitVec.ofNat 64 456)).toNat % 2 ^ 32 = c.tau
  v0 : s.getMem (BitVec.ofNat 64 320) = vw0 v
  v1 : s.getMem (BitVec.ofNat 64 328) = vw1 v
  vl : v.length = 16
  pc : s.pc = pcOf 4248

structure FoldEnd (c : YCtx) (l : Nat) (v : Val) (s : MachineState) : Prop where
  g : GY c.wl c.pk c.idx s
  k : KnownOK (foldK c.lay l) s
  e : s.getReg .x13 = BitVec.ofNat 64 c.e
  tau : s.getReg .x30 = BitVec.ofNat 64 c.tau
  w448 : s.getMem (BitVec.ofNat 64 448) = BitVec.ofNat 64 (769 + 65536 * c.lay)
  w456 : (s.getMem (BitVec.ofNat 64 456)).toNat % 2 ^ 32 = c.tau
  v0 : s.getMem (BitVec.ofNat 64 320) = vw0 v
  v1 : s.getMem (BitVec.ofNat 64 328) = vw1 v
  vl : v.length = 16
  pc : s.pc = pcOf 4272

theorem fset_step (c : YCtx) (hc : c.ok) (a : BitVec 256) (s : MachineState) (hs : LeafOut c a s) :
    ∃ t, Steps image s 8 8 t ∧ FoldIn c 0 (answerBytes 16 a) t := by
  have hL := layCheck_at c.lay hc.1
  simp only [layCheck, leafCheckY, Bool.and_eq_true] at hL
  obtain ⟨t, ht⟩ := yspec_run hL.1.2.2 s hs.pc hs.k (by simp [fsetSpec]) (by simp)
  have hm : ∀ A, t.getMem A = memEval s [wk 456 (stW0 456 (.reg .x30)), wk 448 (cw (769 + 65536 * c.lay))] A :=
    ht.mem
  have hfr : ∀ A, A < 2 ^ 64 → A ≠ 456 → A ≠ 448 → t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) :=
    fun A hA h1 h2 => by
      rw [hm, wk, wk, memEval_ofNat_ne _ _ _ _ _ hA (by omega) h1, memEval_ofNat_ne _ _ _ _ _ hA (by omega) h2]; rfl
  have htau := c.tau_lt hc
  refine ⟨t, ht.steps, ⟨hs.g.step ht, ht.known, ?_, ?_, ?_, ?_, ?_, ?_, by simp, ht.pc⟩⟩
  · rw [ht.keep .x13 (by simp)]; exact hs.e
  · rw [ht.keep .x30 (by simp)]; exact hs.tau
  · rw [hm, wk, wk, memEval_ofNat_ne _ _ _ _ _ (by omega) (by omega) (by omega),
      memEval_ofNat_eq _ _ _ _ _ (by omega) rfl]; rfl
  · rw [hm, wk, wk, memEval_ofNat_eq _ _ _ _ _ (by omega) rfl]
    simp only [stW0, E.eval, BinOp.eval, ldE, cw, hs.tau]
    rw [merge_w0_toNat, BitVec.toNat_ofNat]
    omega
  · rw [hfr _ (by omega) (by omega) (by omega), hs.a0]; exact (vw0_answer a).symm
  · rw [hfr _ (by omega) (by omega) (by omega), hs.a1]; exact (vw1_answer a).symm

/-- The node input of fold level `l` (current node `v`). -/
def foldHashIn (c : YCtx) (l : Nat) (v : Val) : List Byte :=
  if c.e / 2 ^ l % 2 = 1 then nodeInput c.lay c.tau (l + 1) (c.e / 2 ^ (l + 1)) (witSib c.wl c.lay l) v
  else nodeInput c.lay c.tau (l + 1) (c.e / 2 ^ (l + 1)) v (witSib c.wl c.lay l)

theorem bitE_eval (s : MachineState) (l e : Nat) (he : e < 2 ^ 64) (hl : l < 64)
    (h : s.getReg .x13 = BitVec.ofNat 64 e) : (bitE l).eval s = BitVec.ofNat 64 (e / 2 ^ l % 2) := by
  have h1 := srl_eval s (.reg .x13) e l he hl h
  have : e / 2 ^ l ≤ e := Nat.div_le_self _ _
  exact and_mask_eval' s _ _ 1 (by omega) (by omega) h1

theorem heapE_eval (c : YCtx) (hc : c.ok) (s : MachineState) (l : Nat) (hl : l < c.h)
    (h : s.getReg .x13 = BitVec.ofNat 64 c.e) :
    (heapE c.lay l).eval s = BitVec.ofNat 64 (heapIndex (height c.lay) (l + 1) (c.e / 2 ^ (l + 1))) := by
  have he := c.e_lt hc
  have hb := hT_bounds c.lay hc.1
  unfold YCtx.h at hl
  simp only [heapE, addC_eval]
  rw [srl_eval s (.reg .x13) c.e (l + 1) (by omega) (by omega) h, BitVec.ofNat_add_ofNat, heapIndex,
    ← hT_eq _ hc.1, Nat.add_comm]

theorem heap_lt (c : YCtx) (hc : c.ok) (l : Nat) (hl : l < c.h) :
    heapIndex (height c.lay) (l + 1) (c.e / 2 ^ (l + 1)) < 2 ^ 32 := by
  have he := c.e_lt hc
  have hb := hT_bounds c.lay hc.1
  unfold heapIndex
  rw [← hT_eq _ hc.1]
  have : 2 ^ (hT c.lay - (l + 1)) ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) (by omega)
  have : c.e / 2 ^ (l + 1) ≤ c.e := Nat.div_le_self _ _
  omega

theorem fold_step (c : YCtx) (hc : c.ok) (l : Nat) (hl : l < c.h) (v : Val) (s : MachineState)
    (hs : FoldIn c l v s) :
    ∃ u k, k ≤ 19 ∧ Steps image s k k u ∧ fetch image u = some (.base .ECALL) ∧ u.getReg .x5 = 0 ∧
      hashArgumentsValid u = true ∧ hashInput u = fmt (foldHashIn c l v) ∧
      ∀ a, FoldEnd c l (answerBytes 16 a) (writeHash u a) := by
  have hL := layCheck_at c.lay hc.1
  simp only [layCheck, Bool.and_eq_true] at hL
  have hF := List.all_eq_true.mp hL.2 l (List.mem_range.mpr hl)
  simp only [foldCheckY, Bool.and_eq_true] at hF
  obtain ⟨⟨hTr, hFa⟩, -⟩ := hF
  have he := c.e_lt hc
  have hb := hT_bounds c.lay hc.1
  have hlay := hc.1
  have htau := c.tau_lt hc
  have hl' : l < hT c.lay := hl
  have hbit : (bitE l).eval s = BitVec.ofNat 64 (c.e / 2 ^ l % 2) := bitE_eval s l c.e (by omega) (by omega) hs.e
  have hbit2 : c.e / 2 ^ l % 2 < 2 := Nat.mod_lt _ (by decide)
  have h24 : s.getReg .x24 = BitVec.ofNat 64 (bodyA c.lay) := known_mem hs.k (by simp [foldK, leafK, kv])
  have hsib0 : s.getMem (BitVec.ofNat 64 (sibA c.lay l)) = vw0 (witSib c.wl c.lay l) := by
    unfold sibA; rw [Nat.add_assoc, wit_body c hc s hs.g _ (by omega) (by omega)]
    unfold witSib nChains; rw [vw0_slice, Nat.add_assoc]
  have hsib1 : s.getMem (BitVec.ofNat 64 (sibA c.lay l + 8)) = vw1 (witSib c.wl c.lay l) := by
    unfold sibA; rw [Nat.add_assoc, Nat.add_assoc, wit_body c hc s hs.g _ (by omega) (by omega)]
    unfold witSib nChains; rw [vw1_slice]; congr 2; omega
  have hsl := length_witSib' c hc l hl
  have hheap := heapE_eval c hc s l hl hs.e
  have hhlt := heap_lt c hc l hl
  have main : ∀ d, d = decide (c.e / 2 ^ l % 2 = 1) →
      yspecB (runAt (foldK c.lay l) [] 4248 [.br d]) (foldSpec c.lay l d) [] (foldK c.lay l) [.x13, .x30] = true →
      ∃ u k, k ≤ 19 ∧ Steps image s k k u ∧ fetch image u = some (.base .ECALL) ∧ u.getReg .x5 = 0 ∧
        hashArgumentsValid u = true ∧ hashInput u = fmt (foldHashIn c l v) ∧
        ∀ a, FoldEnd c l (answerBytes 16 a) (writeHash u a) := by
    intro d hd hchk
    obtain ⟨u, hu⟩ := yspec_run hchk s hs.pc hs.k (by
      intro b hb; simp only [foldSpec, List.mem_singleton] at hb; subst hb
      rw [br_ne_cw0, hbit, hd]
      by_cases h1 : c.e / 2 ^ l % 2 = 1
      · rw [h1]; decide
      · have h0 : c.e / 2 ^ l % 2 = 0 := by omega
        rw [h0]; decide) (by simp)
    have hG := hs.g.step hu
    have hK := hu.known
    have h10 : u.getReg .x10 = BitVec.ofNat 64 448 := known_mem hK (by simp [foldK, kv])
    have h11 : u.getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)) := known_mem hK (by simp [foldK, kv])
    have h12 : u.getReg .x12 = BitVec.ofNat 64 320 := known_mem hK (by simp [foldK, kv])
    have hm : ∀ A, u.getMem A = memEval s (foldMem c.lay l d) A := hu.mem
    have hc_ : (foldMem c.lay l d).all (fun p => p.1.base.isNone) = true := by
      cases d <;> simp [foldMem, wk]
    have h456 : u.getMem (BitVec.ofNat 64 456) =
        BitVec.ofNat 64 (c.tau + 2 ^ 32 * heapIndex (height c.lay) (l + 1) (c.e / 2 ^ (l + 1))) := by
      rw [hm, memEval_look_some (by omega) hc_ (by cases d <;> rfl)]
      simp only [stW, E.eval, BinOp.eval, ldE, cw]
      rw [hheap, stMerge_eval _ _ _ hhlt hs.w456]
    have h448 : u.getMem (BitVec.ofNat 64 448) = BitVec.ofNat 64 (769 + 65536 * c.lay) := by
      rw [hm, memEval_look_none (by omega) hc_ (by cases d <;> rfl)]; exact hs.w448
    refine ⟨u, if d then 18 else 19, by split <;> omega, ?_, hu.ecall rfl, gkY_x5 hu.gk,
      hashArgs_ofNat _ _ _ _ h10 h11 h12 (by omega) (by omega) (by omega) (by decide), ?_, fun a => ?_⟩
    · have := hu.steps; cases d <;> exact this
    · rw [hashInput_ofNat _ 448 0 h10 h11 (by decide) (by decide)]
      unfold foldHashIn
      have hj : c.e / 2 ^ (l + 1) < 2 ^ 32 := by
        have : c.e / 2 ^ (l + 1) ≤ c.e := Nat.div_le_self _ _
        omega
      have t0 : BitVec.ofNat 64 (769 + 65536 * c.lay) = BitVec.ofNat 64 (twLo 3 c.lay c.tau 0) := by
        congr 1; unfold twLo; rw [Nat.div_eq_of_lt (by omega : c.tau < 2 ^ 32)]; omega
      have t1 : BitVec.ofNat 64 (c.tau + 2 ^ 32 * heapIndex (height c.lay) (l + 1) (c.e / 2 ^ (l + 1))) =
          BitVec.ofNat 64 (twHi c.tau (heapIndex (height c.lay) (l + 1) (c.e / 2 ^ (l + 1)))) := by
        congr 1; unfold twHi; omega
      subst hd
      by_cases h1 : c.e / 2 ^ l % 2 = 1
      · rw [if_pos h1, fmt_nodeInput_words _ _ _ _ _ _ hsl hs.vl (by omega) (by omega) hj]
        congr 1
        simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero,
          Nat.mul_zero, List.cons.injEq]
        simp only [h1, decide_true] at hm hc_
        refine ⟨h448.trans t0, h456.trans t1, zY_mem hG 464, zY_mem hG 472, ?_, ?_, ?_, ?_, trivial⟩
        · rw [hm, memEval_look_some (by omega) hc_ rfl]; exact hsib0
        · rw [hm, memEval_look_some (by omega) hc_ rfl]; exact hsib1
        · rw [hm, memEval_look_some (by omega) hc_ rfl]; exact hs.v0
        · rw [hm, memEval_look_some (by omega) hc_ rfl]; exact hs.v1
      · rw [if_neg h1, fmt_nodeInput_words _ _ _ _ _ _ hs.vl hsl (by omega) (by omega) hj]
        congr 1
        simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero,
          Nat.mul_zero, List.cons.injEq]
        simp only [h1, decide_false] at hm hc_
        refine ⟨h448.trans t0, h456.trans t1, zY_mem hG 464, zY_mem hG 472, ?_, ?_, ?_, ?_, trivial⟩
        · rw [hm, memEval_look_some (by omega) hc_ rfl]; exact hs.v0
        · rw [hm, memEval_look_some (by omega) hc_ rfl]; exact hs.v1
        · rw [hm, memEval_look_some (by omega) hc_ rfl]; exact hsib0
        · rw [hm, memEval_look_some (by omega) hc_ rfl]; exact hsib1
    · have wf : ∀ A, A < 2 ^ 64 → (A + 8 ≤ 320 ∨ 352 ≤ A) →
          (writeHash u a).getMem (BitVec.ofNat 64 A) = u.getMem (BitVec.ofNat 64 A) :=
        fun A hA h => writeHash_frame u a 320 A h12 hA (by omega) h
      refine ⟨hG.hash a 320 h12 (by omega) (by decide) (by omega), Known_writeHash hK a, ?_, ?_, ?_, ?_,
        (writeHash_at0 _ a _ h12 (by omega)).trans (vw0_answer a).symm,
        (writeHash_at8 _ a _ h12 (by omega)).trans (vw1_answer a).symm, by simp, ?_⟩
      · rw [writeHash_getReg, hu.keep .x13 (by simp)]; exact hs.e
      · rw [writeHash_getReg, hu.keep .x30 (by simp)]; exact hs.tau
      · rw [wf _ (by omega) (by omega)]; exact h448
      · rw [wf _ (by omega) (by omega), h456, BitVec.toNat_ofNat]
        have : c.tau + 2 ^ 32 * heapIndex (height c.lay) (l + 1) (c.e / 2 ^ (l + 1)) < 2 ^ 64 := by omega
        rw [Nat.mod_eq_of_lt this]; omega
      · rw [writeHash_pc, hu.pc, pcOf_add4]; rfl
  by_cases h1 : c.e / 2 ^ l % 2 = 1
  · exact main true (by simp [h1]) hTr
  · exact main false (by simp [h1]) hFa

/-! ## End of a fold level; next layer; the comparison -/

structure FinalIn (wl pk : List Byte) (idx : Nat) (M : Val) (s : MachineState) : Prop where
  g : GY wl pk idx s
  m0 : s.getMem (BitVec.ofNat 64 288) = vw0 M
  m1 : s.getMem (BitVec.ofNat 64 296) = vw1 M
  ml : M.length = 16
  pc : s.pc = pcOf 4281

/-- After the last fold of layer `c.lay`: the next layer's loop head, or the comparison. -/
def LayOut (c : YCtx) (v : Val) (t : MachineState) : Prop :=
  if c.lay = 0 then FinalIn c.wl c.pk c.idx v t else LayIn ⟨c.wl, c.pk, c.idx, c.lay - 1⟩ v t

theorem fend_step (c : YCtx) (hc : c.ok) (l : Nat) (hl : l < c.h) (v : Val) (s : MachineState)
    (hs : FoldEnd c l v s) :
    (l + 1 < c.h → ∃ t, Steps image s 3 3 t ∧ FoldIn c (l + 1) v t) ∧
    (l + 1 = c.h → ∃ t, Steps image s 9 9 t ∧ LayOut c v t) := by
  have hL := layCheck_at c.lay hc.1
  simp only [layCheck, Bool.and_eq_true] at hL
  have hF := List.all_eq_true.mp hL.2 l (List.mem_range.mpr hl)
  simp only [foldCheckY, Bool.and_eq_true] at hF
  have h3 := hF.2
  constructor
  · intro hlt
    have e1 : fendSpec c.lay l = ⟨[], [], 4248, false, 3, [], none⟩ := if_pos hlt
    have e2 : fendPost c.lay l = foldK c.lay (l + 1) := if_pos hlt
    rw [e1, e2] at h3
    obtain ⟨t, ht⟩ := yspec_run h3 s hs.pc hs.k (by simp) (by simp)
    have hm : ∀ A, t.getMem A = s.getMem A := fun A => ht.mem A
    refine ⟨t, ht.steps, ⟨hs.g.step ht, ht.known, ?_, ?_, by rw [hm]; exact hs.w448, by rw [hm]; exact hs.w456,
      by rw [hm]; exact hs.v0, by rw [hm]; exact hs.v1, hs.vl, ht.pc⟩⟩
    · rw [ht.keep .x13 (by simp)]; exact hs.e
    · rw [ht.keep .x30 (by simp)]; exact hs.tau
  · intro heq
    have hne : ¬ (l + 1 < hT c.lay) := by unfold YCtx.h at heq; omega
    have e1 : fendSpec c.lay l = ⟨[], [wk 296 (ldE 328), wk 288 (ldE 320)],
        if c.lay = 0 then 4281 else 4121, false, 9, [], none⟩ := if_neg hne
    have e2 : fendPost c.lay l = if c.lay = 0 then gkY else layK (c.lay - 1) := if_neg hne
    rw [e1, e2] at h3
    obtain ⟨t, ht⟩ := yspec_run h3 s hs.pc hs.k (by simp) (by simp)
    have hm : ∀ A, t.getMem A = memEval s [wk 296 (ldE 328), wk 288 (ldE 320)] A := ht.mem
    have m0 : t.getMem (BitVec.ofNat 64 288) = vw0 v := by
      rw [hm, wk, wk, memEval_ofNat_ne _ _ _ _ _ (by omega) (by omega) (by omega),
        memEval_ofNat_eq _ _ _ _ _ (by omega) rfl]; exact hs.v0
    have m1 : t.getMem (BitVec.ofNat 64 296) = vw1 v := by
      rw [hm, wk, memEval_ofNat_eq _ _ _ _ _ (by omega) rfl]; exact hs.v1
    have hG := hs.g.step ht
    refine ⟨t, ht.steps, ?_⟩
    unfold LayOut
    by_cases h0 : c.lay = 0
    · rw [if_pos h0]
      exact ⟨hG, m0, m1, hs.vl, by rw [ht.pc, if_pos h0]⟩
    · rw [if_neg h0]
      have hk := ht.known
      rw [if_neg h0] at hk
      exact ⟨hG, hk, m0, m1, hs.vl, by rw [ht.pc, if_neg h0]⟩

/-! ## The judgment of the layer section

`GQ s N C A X`: `GoodQ` without an acceptance condition, accepting runs bounded by `A`. Only the
final comparison has `A < C` (its rejecting path is one instruction longer). -/

abbrev GQ (s : MachineState) (N C A : Nat) (X : OracleComp HashSpec Obs) : Prop := GoodQ s N C True A X

theorem GQ.steps' {s t : MachineState} {k c N C A N' C' A' : Nat} {X : OracleComp HashSpec Obs}
    (hst : Steps image s k c t) (h : GQ t N C A X) (hN : N + k ≤ N') (hC : C + c ≤ C') (hA : A + c ≤ A') :
    GQ s N' C' A' X :=
  GoodQ.steps' hst h hN hC (fun q => ⟨q, hA⟩)

theorem GQ.mono {s : MachineState} {N C A N' C' A' : Nat} {X : OracleComp HashSpec Obs}
    (h : GQ s N C A X) (hN : N ≤ N') (hC : C ≤ C') (hA : A ≤ A') : GQ s N' C' A' X :=
  GoodQ.mono h hN hC (fun q => ⟨q, hA⟩)

theorem GQ.hash {s : MachineState} {N C A : Nat} {x : List Byte} {K : Val → OracleComp HashSpec Obs}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hin : hashInput s = fmt x)
    (h : ∀ a, GQ (writeHash s a) N C A (K (answerBytes 16 a))) :
    GQ s (N + 1) (C + 8 * (fmt x).blocks) (A + 8 * (fmt x).blocks) (cc (hash16 x) K) :=
  GoodQ.hash hf ht0 hv hin h

theorem GQ.hashP {s : MachineState} {N C A : Nat} {x : List Byte} {K : Val → OracleComp HashSpec Obs}
    (hx : fmt x = pad64 x) (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hin : hashInput s = pad64 x)
    (h : ∀ a, GQ (writeHash s a) N C A (K (answerBytes 16 a))) :
    GQ s (N + 1) (C + 8 * (pad64 x).blocks) (A + 8 * (pad64 x).blocks) (cc (hash16 x) K) := by
  have := GQ.hash hf ht0 hv (hin.trans hx.symm) h
  rwa [hx] at this

theorem GQ.reject {s : MachineState} {A : Nat} (hf : fetch image s = some (.base .ECALL))
    (h5 : s.getReg .x5 = 1) (h10 : s.getReg .x10 = 1) : GQ s 1 1 A (pure (false, 0)) :=
  GoodQ.reject hf h5 h10

theorem cmp_good (wl pk : List Byte) (hpk : pk.length = 16) (idx : Nat) (M : Val) (s : MachineState)
    (hs : FinalIn wl pk idx M s) : GQ s 10 10 9 (pure (M == pk, 0)) := by
  have hC := cmpCheck_ok
  simp only [cmpCheck, Bool.and_eq_true] at hC
  obtain ⟨⟨r1, r2⟩, r3⟩ := hC
  have hK : KnownOK gkY s := hs.g.k
  have p0 : s.getMem (BitVec.ofNat 64 160) = w64 (pk.take 8) := hs.g.pk.1
  have p1 : s.getMem (BitVec.ofNat 64 168) = w64 (pk.drop 8) := hs.g.pk.2
  have heq := val_eq_iff M pk hs.ml hpk
  by_cases e0 : vw0 M = w64 (pk.take 8)
  · by_cases e1 : vw1 M = w64 (pk.drop 8)
    · obtain ⟨v, hv⟩ := spec_run r1 s hs.pc hK (by
        intro b hb
        simp only [cmpAcc, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl <;>
          simp only [Br.holds, CmpOp.eval, Rv.E.eval, ldE, cw, hs.m0, hs.m1, p0, p1, e0, e1, bne_self_eq_false])
      have hb : (M == pk) = true := beq_iff_eq.mpr (heq.mpr ⟨e0, e1⟩)
      have := Good.steps hv.steps (Good.halt (hv.ecall rfl) (hv.regs (.x5, cw 1) (by simp [cmpAcc])))
      rw [hv.regs (.x10, cw 0) (by simp [cmpAcc])] at this
      rw [hb]
      exact GQ.mono this.toQ (by simp [cmpAcc]) (by simp [cmpAcc]) (by simp [cmpAcc])
    · obtain ⟨v, hv⟩ := spec_run r3 s hs.pc hK (by
        intro b hb
        simp only [cmpR2, rejSpecY, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · simp only [Br.holds, CmpOp.eval, Rv.E.eval, ldE, cw, hs.m1, p1]; simpa using e1
        · simp only [Br.holds, CmpOp.eval, Rv.E.eval, ldE, cw, hs.m0, p0, e0, bne_self_eq_false])
      have hb : (M == pk) = false := by
        rw [beq_eq_false_iff_ne]; intro h; exact e1 (heq.mp h).2
      rw [hb]
      exact GQ.steps' hv.steps (GQ.reject (A := 0) (hv.ecall rfl) (hv.regs (.x5, cw 1) (by simp [cmpR2, rejSpecY]))
        (hv.regs (.x10, cw 1) (by simp [cmpR2, rejSpecY]))) (by simp [cmpR2, rejSpecY])
        (by simp [cmpR2, rejSpecY]) (by simp [cmpR2, rejSpecY])
  · obtain ⟨v, hv⟩ := spec_run r2 s hs.pc hK (by
      intro b hb
      simp only [cmpR1, rejSpecY, List.mem_singleton] at hb
      subst hb
      simp only [Br.holds, CmpOp.eval, Rv.E.eval, ldE, cw, hs.m0, p0]; simpa using e0)
    have hb : (M == pk) = false := by
      rw [beq_eq_false_iff_ne]; intro h; exact e0 (heq.mp h).1
    rw [hb]
    exact GQ.steps' hv.steps (GQ.reject (A := 0) (hv.ecall rfl) (hv.regs (.x5, cw 1) (by simp [cmpR1, rejSpecY]))
      (hv.regs (.x10, cw 1) (by simp [cmpR1, rejSpecY]))) (by simp [cmpR1, rejSpecY])
      (by simp [cmpR1, rejSpecY]) (by simp [cmpR1, rejSpecY])

end SigGolfCandidate.Verify

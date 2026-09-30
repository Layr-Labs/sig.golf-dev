import SigGolfCandidate.Verify.LaySem

/-!
# The layer section: the simulation judgment

Chain step loop (`steps_good`), one chain (`chain_good`), the 32 chains (`chains_good`), the fold
levels (`foldsY_good`), one layer (`layer_good`), all layers with the final comparison
(`layers_good`), and the entry from the PORS root tail (`layers_entry`).

Cycle costs: a chain step costs 11 (`sb`, the hash, the loop test), a chain `18 + 11 (15 - x)`,
so the 32 chains of an accepted encoding (digits summing to 312) cost `32 * 18 + 11 * 168 = 2424`;
a fold level at most 30 (the last one 36).
-/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp

theorem blocks_q' (n : Nat) (ws : List Word) : (queryOfWords n ws).blocks = n + 1 := rfl

/-! ## Chains -/

theorem chainFrom_succ (lay tau e i x : Nat) (v : Val) (hx : x < 15) :
    chainFrom lay tau e i x v =
      hash16 (chainInput lay tau e i (x + 1) v) >>= chainFrom lay tau e i (x + 1) := by
  unfold chainFrom
  rw [show 15 - x = (15 - (x + 1)) + 1 by omega, List.range'_succ, List.foldlM_cons]

theorem chainFrom_15 (lay tau e i : Nat) (v : Val) : chainFrom lay tau e i 15 v = pure v := rfl

theorem blocks_chainY (lay tau e i x : Nat) (v : Val) (hv : v.length = 16) (hx : x < 15) (hi : i < 32) :
    (fmt (chainInput lay tau e i (x + 1) v)).blocks = 1 := by
  rw [fmt_chainInput_words _ _ _ _ _ _ hv (by omega) (by omega) (by omega)]; rfl

theorem steps_good (c : YCtx) (hc : c.ok) (xs : List Nat) (i : Nat) (hi : i < 32) (ends : List Val)
    (K : List Val → OracleComp HashSpec Obs) (N C A : Nat)
    (hK : ∀ v t, v.length = 16 → SdIn c xs i ends v t → GQ t N C A (K (ends ++ [v]))) :
    ∀ k x v s, x + k = 15 → StIn c xs i ends x v s →
      GQ s (N + 4 * k) (C + 11 * k) (A + 11 * k)
        (cc (chainFrom c.lay c.tau c.e i x v) (fun v => K (ends ++ [v]))) := by
  intro k
  induction k with
  | zero => intro x v s hk hs; exact absurd hs.hx (by omega)
  | succ k ih =>
    intro x v s hk hs
    obtain ⟨u, hst, hf, h5, hv, hin, hpost⟩ := step_hash c hc xs i hi ends x v s hs
    rw [chainFrom_succ _ _ _ _ _ _ hs.hx, cc_bind]
    have H : ∀ a, GQ (writeHash u a) (N + 4 * k + 2) (C + 11 * k + 2) (A + 11 * k + 2)
        (cc (chainFrom c.lay c.tau c.e i (x + 1) (answerBytes 16 a)) (fun v => K (ends ++ [v]))) := by
      intro a
      by_cases hx1 : x + 1 < 15
      · obtain ⟨t, hst2, ht⟩ := (hpost a).1 hx1
        exact GQ.steps' hst2 (ih (x + 1) _ t (by omega) ht) (by omega) (by omega) (by omega)
      · have hx15 : x + 1 = 15 := by omega
        obtain ⟨t, hst2, ht⟩ := (hpost a).2 hx15
        rw [hx15, chainFrom_15, cc_pure]
        exact GQ.steps' hst2 (hK _ t (by simp) ht) (by omega) (by omega) (by omega)
    have h3 := GQ.hash (K := fun v => cc (chainFrom c.lay c.tau c.e i (x + 1) v) (fun v => K (ends ++ [v])))
      hf h5 hv hin H
    rw [blocks_chainY _ _ _ _ _ _ hs.vl hs.hx hi] at h3
    exact GQ.steps' hst h3 (by omega) (by omega) (by omega)

theorem chain_good (c : YCtx) (hc : c.ok) (xs : List Nat) (i : Nat) (hi : i < 32) (ends : List Val)
    (K : List Val → OracleComp HashSpec Obs) (N C A : Nat)
    (hK : ∀ v t, v.length = 16 → ChIn c xs (i + 1) (ends ++ [v]) t → GQ t N C A (K (ends ++ [v])))
    (s : MachineState) (hs : ChIn c xs i ends s) :
    GQ s (N + 80) (C + (18 + 11 * (15 - xs.getD i 0))) (A + (18 + 11 * (15 - xs.getD i 0)))
      (cc (chainFrom c.lay c.tau c.e i (xs.getD i 0) (witChain c.wl c.lay i)) (fun v => K (ends ++ [v]))) := by
  have hK' : ∀ v t, v.length = 16 → SdIn c xs i ends v t → GQ t (N + 8) (C + 8) (A + 8) (K (ends ++ [v])) := by
    intro v t hv ht
    obtain ⟨u, hst, hu⟩ := cend_step c hc xs i hi ends v t ht
    exact GQ.steps' hst (hK v u hv hu) (by omega) (by omega) (by omega)
  have hx := hs.b.xlt i hi
  obtain ⟨h15, hlt⟩ := chead_step c hc xs i hi ends s hs
  by_cases hx15 : xs.getD i 0 = 15
  · obtain ⟨t, hst, ht⟩ := h15 hx15
    rw [hx15, chainFrom_15, cc_pure]
    exact GQ.steps' hst (hK' _ t ht.vl ht) (by omega) (by omega) (by omega)
  · obtain ⟨t, hst, ht⟩ := hlt (by omega)
    have := steps_good c hc xs i hi ends K (N + 8) (C + 8) (A + 8) hK' (15 - xs.getD i 0) _ _ t (by omega) ht
    exact GQ.steps' hst this (by omega) (by omega) (by omega)

def chainF (c : YCtx) (xs : List Nat) (ends : List Val) (i : Nat) : OracleComp HashSpec (List Val) := do
  let v ← chainFrom c.lay c.tau c.e i (xs.getD i 0) (witChain c.wl c.lay i)
  pure (ends ++ [v])

def chainsCost (xs : List Nat) (i k : Nat) : Nat :=
  ((List.range' i k).map fun j => 18 + 11 * (15 - xs.getD j 0)).sum

theorem chains_good (c : YCtx) (hc : c.ok) (xs : List Nat) (K : List Val → OracleComp HashSpec Obs)
    (N C A : Nat) (hK : ∀ ends t, ChIn c xs 32 ends t → GQ t N C A (K ends)) :
    ∀ k i, i + k = 32 → ∀ ends s, ChIn c xs i ends s →
      GQ s (N + 80 * k) (C + chainsCost xs i k) (A + chainsCost xs i k)
        (cc ((List.range' i k).foldlM (chainF c xs) ends) K) := by
  intro k
  induction k with
  | zero =>
    intro i hik ends s hs
    obtain rfl : i = 32 := by omega
    simpa [chainsCost] using hK ends s hs
  | succ k ih =>
    intro i hik ends s hs
    rw [List.range'_succ, List.foldlM_cons]
    simp only [chainF, bind_assoc, pure_bind, cc_bind]
    have := chain_good c hc xs i (by omega) ends
      (fun ends => cc ((List.range' (i + 1) k).foldlM (chainF c xs) ends) K)
      (N + 80 * k) (C + chainsCost xs (i + 1) k) (A + chainsCost xs (i + 1) k)
      (fun v t _ ht => by
        have := ih (i + 1) (by omega) (ends ++ [v]) t ht
        simpa [chainF] using this) s hs
    have e : chainsCost xs i (k + 1) = 18 + 11 * (15 - xs.getD i 0) + chainsCost xs (i + 1) k := by
      simp only [chainsCost, List.range'_succ, List.map_cons, List.sum_cons]
    refine GQ.mono this (by omega) ?_ ?_ <;> rw [e] <;> omega

theorem sum_eq_getD (l : List Nat) : l.sum = ((List.range l.length).map (l.getD · 0)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.sum_cons,
      List.map_map, ih]
    rfl

theorem chainsCost_aux (xs : List Nat) (hx : ∀ j, j < 32 → xs.getD j 0 < 16) : ∀ k i, i + k ≤ 32 →
    chainsCost xs i k + 11 * ((List.range' i k).map (xs.getD · 0)).sum = 183 * k := by
  intro k
  induction k with
  | zero => intro i _; rfl
  | succ k ih =>
    intro i hik
    have := ih (i + 1) (by omega)
    have := hx i (by omega)
    simp only [chainsCost, List.range'_succ, List.map_cons, List.sum_cons] at *
    omega

theorem chainsCost_eq (xs : List Nat) (hlen : xs.length = 32) (hx : ∀ j, j < 32 → xs.getD j 0 < 16)
    (hsum : xs.sum = 312) : chainsCost xs 0 32 = 2424 := by
  have h := chainsCost_aux xs hx 32 0 (by omega)
  rw [← List.range_eq_range', ← hlen, ← sum_eq_getD, hsum] at h
  rw [hlen] at h
  omega

/-! ## Folds -/

/-- The body of `foldPath` for layer `c.lay`. -/
def foldStep (c : YCtx) : Val → Nat → OracleComp HashSpec Val := fun v lam =>
  let sib := (witPath c.wl c.lay).getD lam []
  let j := c.e / 2 ^ (lam + 1)
  if c.e / 2 ^ lam % 2 = 1 then hash16 (nodeInput c.lay c.tau (lam + 1) j sib v)
  else hash16 (nodeInput c.lay c.tau (lam + 1) j v sib)

theorem length_witPath' (c : YCtx) (hc : c.ok) : (witPath c.wl c.lay).length = c.h := by
  simp [witPath, YCtx.h, hT_eq _ hc.1]

theorem foldPath_eq' (c : YCtx) (hc : c.ok) (v : Val) :
    foldPath (nodeInput c.lay c.tau) c.e v (witPath c.wl c.lay) = (List.range' 0 c.h).foldlM (foldStep c) v := by
  unfold foldPath
  rw [length_witPath' c hc, List.range_eq_range']
  rfl

theorem foldStep_eq (c : YCtx) (hc : c.ok) (l : Nat) (hl : l < c.h) (v : Val) :
    foldStep c v l = hash16 (foldHashIn c l v) := by
  have hs : (witPath c.wl c.lay).getD l [] = witSib c.wl c.lay l := by
    unfold witPath
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by
      rw [← hT_eq _ hc.1]; exact hl)]
    rfl
  unfold foldStep foldHashIn
  simp only [hs]
  split <;> rfl

theorem blocks_node (c : YCtx) (hc : c.ok) (l : Nat) (hl : l < c.h) (v : Val) (hv : v.length = 16) :
    (fmt (foldHashIn c l v)).blocks = 1 := by
  have he := c.e_lt hc
  have hsl := length_witSib' c hc l hl
  have hj : c.e / 2 ^ (l + 1) < 2 ^ 32 := by
    have : c.e / 2 ^ (l + 1) ≤ c.e := Nat.div_le_self _ _
    omega
  have hlay := hc.1
  have hb := hT_bounds c.lay hc.1
  unfold YCtx.h at hl
  unfold foldHashIn
  split
  · rw [fmt_nodeInput_words _ _ _ _ _ _ hsl hv (by omega) (by omega) hj]; rfl
  · rw [fmt_nodeInput_words _ _ _ _ _ _ hv hsl (by omega) (by omega) hj]; rfl

theorem foldsY_good (c : YCtx) (hc : c.ok) (K : Val → OracleComp HashSpec Obs) (N C A : Nat)
    (hK : ∀ v t, v.length = 16 → LayOut c v t → GQ t N C A (K v)) :
    ∀ k l, l + k = c.h → ∀ v s, FoldIn c l v s → 0 < k →
      GQ s (N + 23 * k + 6) (C + 30 * k + 6) (A + 30 * k + 6)
        (cc ((List.range' l k).foldlM (foldStep c) v) K) := by
  intro k
  induction k with
  | zero => intro l _ v s _ h0; omega
  | succ k ih =>
    intro l hlk v s hs _
    rw [List.range'_succ, List.foldlM_cons, cc_bind, foldStep_eq c hc l (by omega) v]
    obtain ⟨u, kk, hkk, hst, hf, h5, hv, hin, hpost⟩ := fold_step c hc l (by omega) v s hs
    have H : ∀ a, GQ (writeHash u a) (N + 23 * k + 9) (C + 30 * k + 9) (A + 30 * k + 9)
        (cc ((List.range' (l + 1) k).foldlM (foldStep c) (answerBytes 16 a)) K) := by
      intro a
      obtain ⟨h1, h2⟩ := fend_step c hc l (by omega) _ _ (hpost a)
      by_cases hk : k = 0
      · subst hk
        obtain ⟨t, hst3, hout⟩ := h2 (by omega)
        simp only [List.range'_zero, List.foldlM_nil, cc_pure]
        exact GQ.steps' hst3 (hK _ t (by simp) hout) (by omega) (by omega) (by omega)
      · obtain ⟨t, hst3, hin'⟩ := h1 (by omega)
        exact GQ.steps' hst3 (ih (l + 1) (by omega) _ t hin' (by omega)) (by omega) (by omega) (by omega)
    have h3 := GQ.hash (K := fun v => cc ((List.range' (l + 1) k).foldlM (foldStep c) v) K) hf h5 hv hin H
    rw [blocks_node c hc l (by omega) v hs.vl] at h3
    exact GQ.steps' hst h3 (by omega) (by omega) (by omega)

/-! ## One layer -/

def layerSpec (w : List Byte) (idx lay : Nat) (M : Val) : OracleComp HashSpec (Option Val) := do
  let (e, tau) := route idx lay
  let d ← hash16 (encInput lay tau e M (witCounter w lay))
  match decodeDigits d with
  | none => pure none
  | some x => do
    let leaf ← verifyLeaf w lay tau e x
    let root ← foldPath (nodeInput lay tau) e leaf (witPath w lay)
    pure (some root)

theorem verifyLayers_succ (w : List Byte) (idx lay : Nat) (M : Val) :
    verifyLayers w idx (lay + 1) M = layerSpec w idx lay M >>= fun o => match o with
      | none => pure none
      | some r => verifyLayers w idx lay r := by
  simp only [verifyLayers, layerSpec, bind_assoc]
  generalize route idx lay = p
  obtain ⟨e, tau⟩ := p
  simp only []
  refine congrArg (fun f => (hash16 (encInput lay tau e M (witCounter w lay))) >>= f) (funext fun d => ?_)
  cases h : decodeDigits d
  · simp only [pure_bind]
  · simp only [bind_assoc, pure_bind]

def layerCost (lay : Nat) : Nat := headSteps lay + 8 + 196 + 2424 + 6 + 72 + 8 + (30 * hT lay + 6)

theorem layerCost_ge (lay : Nat) : headSteps lay + 8 + 25 ≤ layerCost lay := by
  unfold layerCost; omega

theorem layer_good (c : YCtx) (hc : c.ok) (M : Val) (Kopt : Option Val → OracleComp HashSpec Obs)
    (hnone : Kopt none = pure (false, 0)) (N C A : Nat)
    (hK : ∀ root t, root.length = 16 → LayOut c root t → GQ t N C A (Kopt (some root)))
    (s : MachineState) (hs : LayIn c M s) :
    GQ s (N + 3200) (C + layerCost c.lay) (A + layerCost c.lay) (cc (layerSpec c.wl c.idx c.lay M) Kopt) := by
  obtain ⟨u, hst, hf, h5, hv, hin, hpost⟩ := head_step c hc M s hs
  unfold layerSpec
  rw [c.route_eq hc]
  simp only []
  rw [cc_bind]
  have hhs : headSteps c.lay ≤ 36 := by unfold headSteps; split_ifs <;> omega
  have hlc := layerCost_ge c.lay
  have H : ∀ a, GQ (writeHash u a) (N + 3160) (C + layerCost c.lay - headSteps c.lay - 8)
      (A + layerCost c.lay - headSteps c.lay - 8)
      (cc (match decodeDigits (answerBytes 16 a) with
        | none => pure none
        | some x => do
          let leaf ← verifyLeaf c.wl c.lay c.tau c.e x
          let root ← foldPath (nodeInput c.lay c.tau) c.e leaf (witPath c.wl c.lay)
          pure (some root)) Kopt) := by
    intro a
    obtain ⟨hrej, hacc⟩ := enc_step c hc a _ (hpost a)
    cases hd : decodeDigits (answerBytes 16 a) with
    | none =>
      obtain ⟨t, hst2, hf2, h52, h102⟩ := hrej hd
      simp only [cc_pure, hnone]
      exact GQ.steps' hst2 (GQ.reject (A := 0) hf2 h52 h102) (by omega) (by omega) (by omega)
    | some xs =>
      obtain ⟨t2, hst2, hch⟩ := hacc xs hd
      -- the digits of an accepted encoding
      have hdec := decodeDigits_answer a
      rw [show targetSum = 312 from rfl] at hdec
      have hsum : (digitsOf (a.extractLsb' 0 64).toNat (a.extractLsb' 64 64).toNat).sum = 312 := by
        by_contra h; rw [hdec, if_neg h] at hd; cases hd
      have hx : xs = digitsOf (a.extractLsb' 0 64).toNat (a.extractLsb' 64 64).toNat := by
        rw [hdec, if_pos hsum] at hd; exact (Option.some.inj hd).symm
      have hcost : chainsCost xs 0 32 = 2424 := by
        subst hx
        exact chainsCost_eq _ (length_digitsOf _ _) (fun j hj => digitsOf_lt _ _ j hj) hsum
      simp only [verifyLeaf, bind_assoc, cc_bind]
      have hch32 := chains_good c hc xs
        (fun ends => cc (hash16 (leafInput c.lay c.tau c.e ends)) (fun leaf =>
          cc (foldPath (nodeInput c.lay c.tau) c.e leaf (witPath c.wl c.lay)) (fun root =>
            cc (pure (some root)) Kopt)))
        (N + 400) (C + 6 + 72 + 8 + (30 * hT c.lay + 6)) (A + 6 + 72 + 8 + (30 * hT c.lay + 6))
        (by
          intro ends t3 h3
          obtain ⟨u3, hst3, hf3, h53, hv3, hin3, hpost3⟩ := leaf_step c hc xs ends t3 h3
          have hends : ends.length = 32 := h3.b.elen
          have hvs : ∀ v ∈ ends, v.length = 16 := h3.b.el
          have H3 : ∀ ans, GQ (writeHash u3 ans) (N + 390) (C + 8 + (30 * hT c.lay + 6))
              (A + 8 + (30 * hT c.lay + 6))
              (cc (foldPath (nodeInput c.lay c.tau) c.e (answerBytes 16 ans) (witPath c.wl c.lay))
                (fun root => cc (pure (some root)) Kopt)) := by
            intro ans
            obtain ⟨t4, hst4, hfi⟩ := fset_step c hc ans _ (hpost3 ans)
            rw [foldPath_eq' c hc]
            simp only [cc_pure]
            have hb := hT_bounds c.lay hc.1
            have hfold := foldsY_good c hc (fun root => Kopt (some root)) N C A
              (fun root t hr ht => hK root t hr ht) c.h 0 (by omega) _ t4 hfi (by unfold YCtx.h; omega)
            unfold YCtx.h at hfold
            exact GQ.steps' hst4 hfold (by omega) (by omega) (by omega)
          have h3' := GQ.hashP (x := leafInput c.lay c.tau c.e ends)
            (K := fun leaf => cc (foldPath (nodeInput c.lay c.tau) c.e leaf (witPath c.wl c.lay))
              (fun root => cc (pure (some root)) Kopt))
            (fmt_th _ _ _ _ _ _ (by decide)) hf3 h53 hv3 hin3 H3
          rw [pad64_leafInput _ _ _ _ hends hvs, blocks_q'] at h3'
          exact GQ.steps' hst3 h3' (by omega) (by omega) (by omega))
        32 0 (by omega) [] t2 hch
      rw [hcost] at hch32
      have e1 : List.range nChains = List.range' 0 32 := by rw [List.range_eq_range']; rfl
      rw [e1]
      refine GQ.steps' hst2 (hch32.congr ?_) (by omega) (by unfold layerCost; omega) (by unfold layerCost; omega)
      subst hx
      rfl
  have h3 := GQ.hashP (x := encInput c.lay c.tau c.e M (witCounter c.wl c.lay))
    (K := fun d => cc (match decodeDigits d with
        | none => pure none
        | some x => do
          let leaf ← verifyLeaf c.wl c.lay c.tau c.e x
          let root ← foldPath (nodeInput c.lay c.tau) c.e leaf (witPath c.wl c.lay)
          pure (some root)) Kopt) (fmt_th _ _ _ _ _ _ (by decide)) hf h5 hv hin H
  rw [pad64_encInput _ _ _ _ hs.ml, blocks_q'] at h3
  exact GQ.steps' hst h3 (by omega) (by unfold layerCost at *; omega) (by unfold layerCost at *; omega)

/-! ## All layers -/

def Kfin (pk : List Byte) : Option Val → OracleComp HashSpec Obs
  | none => pure (false, 0)
  | some root => pure (root == pk, 0)

def InLay (wl pk : List Byte) (idx : Nat) : Nat → Val → MachineState → Prop
  | 0 => FinalIn wl pk idx
  | n + 1 => LayIn ⟨wl, pk, idx, n⟩

/-- Cycle bounds of the layers `n-1 .. 0` and the comparison: every run / accepting runs. -/
def layersCost : Nat → Nat
  | 0 => 10
  | n + 1 => layersCost n + layerCost n

def layersCostA : Nat → Nat
  | 0 => 9
  | n + 1 => layersCostA n + layerCost n

theorem layers_good (wl pk : List Byte) (hpk : pk.length = 16) (idx : Nat) (hidx : idx < 2 ^ 34)
    (hwl : wl.length = 6064) :
    ∀ n, n ≤ 6 → ∀ M s, InLay wl pk idx n M s →
      GQ s (3200 * n + 10) (layersCost n) (layersCostA n) (cc (verifyLayers wl idx n M) (Kfin pk)) := by
  intro n
  induction n with
  | zero =>
    intro _ M s hs
    simp only [verifyLayers, cc_pure, Kfin, layersCost, layersCostA]
    exact cmp_good wl pk hpk idx M s hs
  | succ n ih =>
    intro hn M s hs
    rw [verifyLayers_succ, cc_bind]
    have hc : (⟨wl, pk, idx, n⟩ : YCtx).ok := ⟨show n < 6 by omega, hidx, hwl, hpk⟩
    have := layer_good ⟨wl, pk, idx, n⟩ hc M
      (fun o => cc (match o with
        | none => pure none
        | some r => verifyLayers wl idx n r) (Kfin pk)) (by simp [Kfin])
      (3200 * n + 10) (layersCost n) (layersCostA n) (by
        intro root u _ hu
        simp only []
        apply ih (by omega)
        unfold LayOut at hu
        cases n with
        | zero => show FinalIn wl pk idx root u; simpa using hu
        | succ m => show LayIn ⟨wl, pk, idx, m⟩ root u; simpa using hu) s hs
    exact GQ.mono this (by omega) (by simp only [layersCost]; omega) (by simp only [layersCostA]; omega)

theorem layersCost_val : layersCost 6 = 17558 ∧ layersCostA 6 = 17557 := by decide

/-- From the PORS root tail (`layers`, 4096) to the verdict: every run takes at most 17583 cycles,
accepting runs at most 17582. -/
theorem layers_entry (wl pk : List Byte) (hpk : pk.length = 16) (idx : Nat) (hidx : idx < 2 ^ 34)
    (hwl : wl.length = 6064) (M : Val) (s : MachineState) (hs : LaysIn wl pk idx M s) :
    GQ s 19235 17583 17582 (cc (verifyLayers wl idx 6 M) (Kfin pk)) := by
  obtain ⟨t, hst, ht⟩ := pro_step wl pk idx M s hs
  have := layers_good wl pk hpk idx hidx hwl 6 (le_refl _) M t ht
  rw [layersCost_val.1, layersCost_val.2] at this
  exact GQ.steps' hst this (by omega) (by omega) (by omega)

end SigGolfCandidate.Verify

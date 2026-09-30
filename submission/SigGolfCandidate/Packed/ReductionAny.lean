import SigGolfCandidate.Packed.Reduction

/-!
# Total counter compression and one-way strong security

The total compression map is a left inverse of expansion on every packed
signature. Thus a fresh packed forgery expands to a fresh old forgery, even if
some old signing-oracle outputs had out-of-range counters. The converse need
not hold because compression discards high bits of old counters.
-/

namespace SigGolfCandidate.Packed

open SigGolfCandidate.Legacy OracleComp OracleSpec

set_option maxRecDepth 200000
set_option maxHeartbeats 1000000

set_option allowUnsafeReducibility true in
attribute [local reducible] SigGolfCandidate.Legacy.Input SigGolfCandidate.Legacy.Output
  oldSubmission shortSubmission

def liftActionAny {state : Type} : Action sizes state → Action oldSizes state
  | .submit candidate => .submit (liftForgery candidate)
  | .hash input resume => .hash input resume
  | .sign request resume =>
      .sign ⟨request.message, request.cache⟩ (fun answer => resume (answer.map packOldAny))
  | .sample n resume => .sample n resume
  | .step next => .step next

def liftAdversaryAny (A : Adversary sizes) : Adversary oldSizes where
  State := A.State
  initial := A.initial
  step state := liftActionAny (A.step state)

structure TranscriptRelAny (short : Transcript sizes) (long : Transcript oldSizes) : Prop where
  signed : short.signed = long.signed.map (fun e => (e.1, packOldAny e.2))
  signingRequests : short.signingRequests = long.signingRequests
  hashCalls : short.hashCalls = long.hashCalls

/-- If an expanded packed signature occurred in the old transcript, the
original packed signature occurred in the short transcript. -/
theorem signed_old_implies_short {short : Transcript sizes} {long : Transcript oldSizes}
    (h : TranscriptRelAny short long) (message : Message) (signature : Bytes 6398) :
    (message, unpackOld signature) ∈ long.signed →
      (message, signature) ∈ short.signed := by
  intro hm
  rw [h.signed, ← packAny_unpackOld signature]
  exact List.mem_map.mpr ⟨(message, unpackOld signature), hm, rfl⟩

/-- Strong freshness transfers in exactly the direction needed for a security
reduction. -/
theorem freshSignature_imp {short : Transcript sizes} {long : Transcript oldSizes}
    (h : TranscriptRelAny short long) (message : Message) (signature : Bytes 6398) :
    short.freshSignature message signature = true →
      long.freshSignature message (unpackOld signature) = true := by
  intro hshort
  cases hlong : long.signed.contains (message, unpackOld signature) with
  | false =>
      have hn : (message, unpackOld signature) ∉ long.signed := by
        intro hm
        have hc := List.contains_iff_mem.mpr hm
        rw [hlong] at hc
        cases hc
      simpa [Transcript.freshSignature] using hn
  | true =>
      have hm : (message, unpackOld signature) ∈ long.signed :=
        List.contains_iff_mem.mp hlong
      have hs := signed_old_implies_short h message signature hm
      have hn : (message, signature) ∉ short.signed := by
        simpa [Transcript.freshSignature] using hshort
      exact (hn hs).elim

theorem freshMessage_any_eq {short : Transcript sizes} {long : Transcript oldSizes}
    (h : TranscriptRelAny short long) (message : Message) :
    short.freshMessage message = long.freshMessage message := by
  unfold Transcript.freshMessage
  rw [h.signed, List.any_map]
  rfl

theorem record_any_rel {short : Transcript sizes} {long : Transcript oldSizes}
    (h : TranscriptRelAny short long) (message : Message)
    (value : Option (Bytes 6404)) (calls : Nat) :
    TranscriptRelAny (recordVC short message (value.map packOldAny) calls)
      (recordVC long message value calls) := by
  cases value with
  | none =>
      refine ⟨by simpa [recordVC] using h.signed,
        by simpa [recordVC] using h.signingRequests,
        by simpa [recordVC] using congrArg (· + calls) h.hashCalls⟩
  | some σ =>
      refine ⟨?_, ?_, ?_⟩
      · simp only [recordVC, Option.map_some, List.map_cons]
        rw [h.signed]
      · simpa [recordVC] using h.signingRequests
      · simpa [recordVC] using congrArg (· + calls) h.hashCalls

theorem hash_any_rel {short : Transcript sizes} {long : Transcript oldSizes}
    (h : TranscriptRelAny short long) :
    TranscriptRelAny { short with hashCalls := short.hashCalls + 1 }
      { long with hashCalls := long.hashCalls + 1 } := by
  exact ⟨h.signed, h.signingRequests, congrArg (· + 1) h.hashCalls⟩

structure AssumptionsAny (layout : Layout) (oldImages shortImages : Phase → Riscv.Image) : Prop where
  keygen : ∀ sk : SecretKey,
    (observed <$> (shortSubmission layout shortImages).run .keygen sk) =
      (observed <$> (oldSubmission layout oldImages).run .keygen sk)
  sign : ∀ (sk : SecretKey) (cache : Bytes CACHE_BYTES) (message : Message),
    (observed <$> (shortSubmission layout shortImages).run .sign (sk, cache, message)) =
      ((fun r => (r.value.map packOldAny, r.hashCalls)) <$>
        (oldSubmission layout oldImages).run .sign (sk, cache, message))
  expand : ∀ (message : Message) (pk : PublicKey) (signature : Bytes 6398),
    (observed <$> (shortSubmission layout shortImages).run .expand (message, pk, signature)) =
      (observed <$> (oldSubmission layout oldImages).run .expand
        (message, pk, unpackOld signature))
  verify : ∀ (message : Message) (pk : PublicKey) (witness : Bytes 6404),
    (observed <$> (shortSubmission layout shortImages).run .verify (message, pk, witness)) =
      (observed <$> (oldSubmission layout oldImages).run .verify (message, pk, witness))

/-- Both games pay the same hash cost. A short win is also an old win. -/
def AttackRel (short long : AttackResult) : Prop :=
  short.hashCalls = long.hashCalls ∧ (short.won = true → long.won = true)

theorem attackRel_false (shortCalls longCalls : Nat) (h : shortCalls = longCalls) :
    AttackRel ⟨false, shortCalls⟩ ⟨false, longCalls⟩ :=
  ⟨h, by simp⟩

/-- Run one common expansion and verification, returning both games' answers. -/
def checkPair (layout : Layout) (oldImages : Phase → Riscv.Image)
    (pk : PublicKey) (short : Transcript sizes) (long : Transcript oldSizes)
    (candidate : Forgery sizes) : OracleComp HashSpec (AttackResult × AttackResult) :=
  match candidate with
  | .witness message witness =>
      (fun p : Option Unit × Nat =>
        (⟨p.1.isSome && short.freshMessage message, short.hashCalls + p.2⟩,
         ⟨p.1.isSome && long.freshMessage message, long.hashCalls + p.2⟩)) <$>
        (observed <$> (oldSubmission layout oldImages).run .verify (message, pk, witness))
  | .signature message signature => do
      let p ← observed <$> (oldSubmission layout oldImages).run .expand
        (message, pk, unpackOld signature)
      match p.1 with
      | none =>
          pure (⟨false, short.hashCalls + p.2⟩, ⟨false, long.hashCalls + p.2⟩)
      | some witness =>
          (fun q : Option Unit × Nat =>
            (⟨q.1.isSome && short.freshSignature message signature,
                short.hashCalls + p.2 + q.2⟩,
             ⟨q.1.isSome && long.freshSignature message (unpackOld signature),
                long.hashCalls + p.2 + q.2⟩)) <$>
            (observed <$> (oldSubmission layout oldImages).run .verify
              (message, pk, witness))

theorem checkPair_rel {layout : Layout} {oldImages : Phase → Riscv.Image}
    (pk : PublicKey) {short : Transcript sizes} {long : Transcript oldSizes}
    (h : TranscriptRelAny short long) (candidate : Forgery sizes)
    (answer : AttackResult × AttackResult)
    (ha : answer ∈ support (checkPair layout oldImages pk short long candidate)) :
    AttackRel answer.1 answer.2 := by
  cases candidate with
  | witness message witness =>
      simp only [checkPair, support_map] at ha
      obtain ⟨p, _, rfl⟩ := ha
      exact ⟨by rw [h.hashCalls], by
        simp only [Bool.and_eq_true]
        rintro ⟨hv, hs⟩
        exact ⟨hv, by rw [← freshMessage_any_eq h]; exact hs⟩⟩
  | signature message signature =>
      simp only [checkPair] at ha
      obtain ⟨p, _, hrest⟩ := (mem_support_bind_iff _ _ _).mp ha
      cases hp : p.1 with
      | none =>
          simp only [hp] at hrest
          simp only [support_pure, Set.mem_singleton_iff] at hrest
          subst answer
          exact attackRel_false _ _ (by rw [h.hashCalls])
      | some witness =>
          simp only [hp] at hrest
          rw [support_map] at hrest
          obtain ⟨q, _, rfl⟩ := hrest
          refine ⟨by rw [h.hashCalls], ?_⟩
          simp only [Bool.and_eq_true]
          rintro ⟨hv, hs⟩
          exact ⟨hv, freshSignature_imp h message signature hs⟩

theorem checkPair_fst {layout : Layout} {oldImages shortImages : Phase → Riscv.Image}
    (H : AssumptionsAny layout oldImages shortImages) (pk : PublicKey)
    {short : Transcript sizes} {long : Transcript oldSizes}
    (candidate : Forgery sizes) :
    (Prod.fst <$> checkPair layout oldImages pk short long candidate) =
      (shortSubmission layout shortImages).checkForgery pk short candidate := by
  cases candidate with
  | witness message witness =>
      rw [check_witness_observed, H.verify message pk witness]
      simp only [checkPair, Functor.map_map]
  | signature message signature =>
      rw [check_signature_observed, H.expand message pk signature]
      simp only [checkPair, map_bind]
      apply bind_congr
      intro p
      cases hp : p.1 with
      | none => simp only [hp]; rfl
      | some witness =>
          simp only [hp]
          rw [H.verify message pk witness]
          simp only [Functor.map_map]

theorem checkPair_snd {layout : Layout} {oldImages : Phase → Riscv.Image}
    (pk : PublicKey) {short : Transcript sizes} {long : Transcript oldSizes}
    (candidate : Forgery sizes) :
    (Prod.snd <$> checkPair layout oldImages pk short long candidate) =
      (oldSubmission layout oldImages).checkForgery pk long (liftForgery candidate) := by
  cases candidate with
  | witness message witness =>
      simp only [liftForgery]
      rw [check_witness_observed]
      simp only [checkPair, Functor.map_map]
  | signature message signature =>
      simp only [liftForgery]
      rw [check_signature_observed]
      simp only [checkPair, map_bind]
      apply bind_congr
      intro p
      cases hp : p.1 with
      | none => simp only [hp]; rfl
      | some witness =>
          simp only [hp]
          simp only [Functor.map_map]

/-- A common execution of the two interactive games. Hashes, private coins,
key generation, signing, expansion, and verification are sampled once. -/
def interactPair (layout : Layout) (oldImages : Phase → Riscv.Image)
    (A : Adversary sizes) (sk : SecretKey) (pk : PublicKey) :
    Nat → A.State → Transcript sizes → Transcript oldSizes →
      OracleComp World (AttackResult × AttackResult)
  | 0, _, short, long =>
      pure (⟨false, short.hashCalls⟩, ⟨false, long.hashCalls⟩)
  | rounds + 1, state, short, long =>
      match A.step state with
      | .submit candidate =>
          liftM (checkPair layout oldImages pk short long candidate)
      | .hash input resume => do
          let answer ← liftM (HashSpec.query input)
          interactPair layout oldImages A sk pk rounds (resume answer)
            { short with hashCalls := short.hashCalls + 1 }
            { long with hashCalls := long.hashCalls + 1 }
      | .sample n resume => do
          let answer ← liftM (unifSpec.query n)
          interactPair layout oldImages A sk pk rounds (resume answer) short long
      | .step next =>
          interactPair layout oldImages A sk pk rounds next short long
      | .sign request resume => do
          if short.signingRequests < LIFETIME then
            let result ← liftM ((oldSubmission layout oldImages).run .sign
              (sk, request.cache, request.message))
            interactPair layout oldImages A sk pk rounds (resume (result.value.map packOldAny))
              (recordVC short request.message (result.value.map packOldAny) result.hashCalls)
              (recordVC long request.message result.value result.hashCalls)
          else
            pure (⟨false, short.hashCalls⟩, ⟨false, long.hashCalls⟩)

theorem interactPair_rel {layout : Layout} {oldImages : Phase → Riscv.Image}
    (A : Adversary sizes) (sk : SecretKey) (pk : PublicKey) :
    ∀ rounds (state : A.State) (short : Transcript sizes) (long : Transcript oldSizes),
      TranscriptRelAny short long →
      ∀ answer ∈ support (interactPair layout oldImages A sk pk rounds state short long),
        AttackRel answer.1 answer.2 := by
  intro rounds
  induction rounds with
  | zero =>
      intro state short long h answer ha
      simp only [interactPair, support_pure, Set.mem_singleton_iff] at ha
      subst answer
      exact attackRel_false _ _ h.hashCalls
  | succ rounds ih =>
      intro state short long h answer ha
      cases hstep : A.step state with
      | submit candidate =>
          simp only [interactPair, hstep] at ha
          change answer ∈ support ((checkPair layout oldImages pk short long candidate).liftComp World) at ha
          exact checkPair_rel pk h candidate answer
            ((OracleComp.mem_support_liftComp_iff _ _).mp ha)
      | hash input resume =>
          simp only [interactPair, hstep] at ha
          obtain ⟨sample, _, hrest⟩ := (mem_support_bind_iff _ _ _).mp ha
          exact ih (resume sample) _ _ (hash_any_rel h) answer hrest
      | sample n resume =>
          simp only [interactPair, hstep] at ha
          obtain ⟨sample, _, hrest⟩ := (mem_support_bind_iff _ _ _).mp ha
          exact ih (resume sample) _ _ h answer hrest
      | step next =>
          simp only [interactPair, hstep] at ha
          exact ih next _ _ h answer ha
      | sign request resume =>
          by_cases hk : short.signingRequests < LIFETIME
          · simp only [interactPair, hstep, hk, if_true] at ha
            obtain ⟨result, _, hrest⟩ := (mem_support_bind_iff _ _ _).mp ha
            exact ih (resume (result.value.map packOldAny)) _ _
              (record_any_rel h request.message result.value result.hashCalls) answer hrest
          · simp only [interactPair, hstep, hk, if_false, support_pure,
              Set.mem_singleton_iff] at ha
            subst answer
            exact attackRel_false _ _ h.hashCalls

theorem interactPair_fst {layout : Layout} {oldImages shortImages : Phase → Riscv.Image}
    (H : AssumptionsAny layout oldImages shortImages) (A : Adversary sizes)
    (sk : SecretKey) (pk : PublicKey) :
    ∀ rounds (state : A.State) (short : Transcript sizes) (long : Transcript oldSizes),
      TranscriptRelAny short long →
      (Prod.fst <$> interactPair layout oldImages A sk pk rounds state short long) =
        (shortSubmission layout shortImages).interact A sk pk rounds state short := by
  intro rounds
  induction rounds with
  | zero =>
      intro state short long h
      simp only [interactPair, Submission.interact, map_pure]
  | succ rounds ih =>
      intro state short long h
      cases hstep : A.step state with
      | submit candidate =>
          simp only [interactPair, hstep, Submission.interact]
          rw [← liftM_map, checkPair_fst H pk candidate]
      | hash input resume =>
          simp only [interactPair, hstep, Submission.interact, map_bind]
          apply bind_congr
          intro answer
          exact ih (resume answer) _ _ (hash_any_rel h)
      | sample n resume =>
          simp only [interactPair, hstep, Submission.interact, map_bind]
          apply bind_congr
          intro answer
          exact ih (resume answer) _ _ h
      | step next =>
          simp only [interactPair, hstep, Submission.interact]
          exact ih next _ _ h
      | sign request resume =>
          by_cases hk : short.signingRequests < LIFETIME
          · simp only [interactPair, hstep, hk, if_true, map_bind]
            let newX : OracleComp HashSpec (RunResult (Bytes 6398)) :=
              (shortSubmission layout shortImages).run .sign
                (sk, request.cache, request.message)
            let oldX : OracleComp HashSpec (RunResult (Bytes 6404)) :=
              (oldSubmission layout oldImages).run .sign
                (sk, request.cache, request.message)
            have hshort :
                (shortSubmission layout shortImages).interact A sk pk (rounds + 1)
                  state short =
                  (liftM newX : OracleComp World _) >>= fun r =>
                    (shortSubmission layout shortImages).interact A sk pk rounds
                      (resume r.value)
                      (recordVC short request.message r.value r.hashCalls) := by
              simp only [Submission.interact, hstep, Submission.signingOracle,
                hk, if_true, record_eq_recordVC]
              rfl
            rw [hshort]
            change ((liftM oldX : OracleComp World _) >>= fun r =>
                Prod.fst <$> interactPair layout oldImages A sk pk rounds
                  (resume (r.value.map packOldAny))
                  (recordVC short request.message (r.value.map packOldAny) r.hashCalls)
                  (recordVC long request.message r.value r.hashCalls)) = _
            calc
              _ = (liftM oldX : OracleComp World _) >>= fun r =>
                    (shortSubmission layout shortImages).interact A sk pk rounds
                      (resume (r.value.map packOldAny))
                      (recordVC short request.message (r.value.map packOldAny)
                        r.hashCalls) := by
                apply bind_congr
                intro r
                exact ih (resume (r.value.map packOldAny)) _ _
                  (record_any_rel h request.message r.value r.hashCalls)
              _ = (liftM ((fun r : RunResult (Bytes 6404) =>
                    (r.value.map packOldAny, r.hashCalls)) <$> oldX) :
                    OracleComp World _) >>= fun p =>
                    (shortSubmission layout shortImages).interact A sk pk rounds
                      (resume p.1) (recordVC short request.message p.1 p.2) :=
                (liftM_bind_map oldX
                  (fun r : RunResult (Bytes 6404) =>
                    (r.value.map packOldAny, r.hashCalls))
                  (fun p : Option (Bytes 6398) × Nat =>
                    (shortSubmission layout shortImages).interact A sk pk rounds
                      (resume p.1) (recordVC short request.message p.1 p.2))).symm
              _ = (liftM (observed <$> newX) : OracleComp World _) >>= fun p =>
                    (shortSubmission layout shortImages).interact A sk pk rounds
                      (resume p.1) (recordVC short request.message p.1 p.2) := by
                rw [H.sign sk request.cache request.message]
              _ = _ := (liftM_bind_observed newX _).symm
          · simp only [interactPair, hstep, hk, if_false]
            have hkL : ¬ short.signingRequests < LIFETIME := hk
            simp only [Submission.interact, hstep, hkL, if_false, h.hashCalls,
              map_pure]

theorem interactPair_snd {layout : Layout} {oldImages : Phase → Riscv.Image}
    (A : Adversary sizes) (sk : SecretKey) (pk : PublicKey) :
    ∀ rounds (state : A.State) (short : Transcript sizes) (long : Transcript oldSizes),
      TranscriptRelAny short long →
      (Prod.snd <$> interactPair layout oldImages A sk pk rounds state short long) =
        (oldSubmission layout oldImages).interact (liftAdversaryAny A) sk pk
          rounds state long := by
  intro rounds
  induction rounds with
  | zero =>
      intro state short long h
      simp only [interactPair, Submission.interact, map_pure, h.hashCalls]
  | succ rounds ih =>
      intro state short long h
      cases hstep : A.step state with
      | submit candidate =>
          simp only [interactPair, hstep, Submission.interact, liftAdversaryAny,
            liftActionAny]
          rw [← liftM_map, checkPair_snd pk candidate]
      | hash input resume =>
          simp only [interactPair, hstep, Submission.interact, liftAdversaryAny,
            liftActionAny, map_bind]
          apply bind_congr
          intro answer
          exact ih (resume answer) _ _ (hash_any_rel h)
      | sample n resume =>
          simp only [interactPair, hstep, Submission.interact, liftAdversaryAny,
            liftActionAny, map_bind]
          apply bind_congr
          intro answer
          exact ih (resume answer) _ _ h
      | step next =>
          simp only [interactPair, hstep, Submission.interact, liftAdversaryAny,
            liftActionAny]
          exact ih next _ _ h
      | sign request resume =>
          by_cases hk : short.signingRequests < LIFETIME
          · have hkL : long.signingRequests < LIFETIME := by
              simpa [h.signingRequests] using hk
            simp only [interactPair, hstep, hk, if_true, map_bind,
              Submission.interact, liftAdversaryAny, liftActionAny,
              hkL, Submission.signingOracle, record_eq_recordVC]
            apply bind_congr
            intro r
            exact ih (resume (r.value.map packOldAny)) _ _
              (record_any_rel h request.message r.value r.hashCalls)
          · have hkL : ¬ long.signingRequests < LIFETIME := by
              simpa [h.signingRequests] using hk
            simp only [interactPair, hstep, hk, hkL, if_false, map_pure,
              Submission.interact, liftAdversaryAny, liftActionAny, h.hashCalls]

end SigGolfCandidate.Packed

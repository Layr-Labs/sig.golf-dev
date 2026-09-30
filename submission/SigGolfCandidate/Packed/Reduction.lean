import SigGolfCandidate.Packed.Codec
import SigGolfCandidate.Legacy.Security

/-!
# Security reduction for packed signatures

An adversary against the short-signature submission can be run against the
existing certified 6404-byte submission: compress every signing-oracle answer
and expand its final signature forgery. The canonical range of successful old
signatures gives the round trip needed for strong freshness.
-/

namespace SigGolfCandidate.Packed

open SigGolfCandidate.Legacy OracleComp OracleSpec

set_option maxRecDepth 200000
set_option maxHeartbeats 1000000

set_option allowUnsafeReducibility true in
attribute [local reducible] SigGolfCandidate.Legacy.Input SigGolfCandidate.Legacy.Output

abbrev oldSizes : Sizes := ⟨6404, 6404, CACHE_BYTES⟩

/-- Generic bytecode containers for the transport theorem. In the final
instantiation, the baseline images are the already certified images. -/
def oldSubmission (layout : Layout) (images : Phase → Riscv.Image) : Submission where
  sizes := oldSizes
  layout := layout
  image := images

def shortSubmission (layout : Layout) (images : Phase → Riscv.Image) : Submission where
  sizes := sizes
  layout := layout
  image := images

set_option allowUnsafeReducibility true in
attribute [local reducible] oldSubmission shortSubmission

def liftForgery : Forgery sizes → Forgery oldSizes
  | .witness message witness => .witness message witness
  | .signature message signature => .signature message (unpackOld signature)

def liftAction {state : Type} : Action sizes state → Action oldSizes state
  | .submit candidate => .submit (liftForgery candidate)
  | .hash input resume => .hash input resume
  | .sign request resume =>
      .sign ⟨request.message, request.cache⟩ (fun answer => resume (answer.map packOld))
  | .sample n resume => .sample n resume
  | .step next => .step next

def liftAdversary (A : Adversary sizes) : Adversary oldSizes where
  State := A.State
  initial := A.initial
  step state := liftAction (A.step state)

/-- Successful old signing-oracle outputs are canonical, including for caches
chosen by the attacker. This invariant is maintained by the simulation. -/
structure TranscriptRel (short : Transcript sizes) (long : Transcript oldSizes) : Prop where
  signed : short.signed = long.signed.map (fun e => (e.1, packOld e.2))
  signingRequests : short.signingRequests = long.signingRequests
  hashCalls : short.hashCalls = long.hashCalls
  canonical : ∀ e ∈ long.signed, CanonicalWitness (Ref.expandRef e.2)

theorem signed_mem_iff {short : Transcript sizes} {long : Transcript oldSizes}
    (h : TranscriptRel short long) (message : Message) (signature : Bytes 6398) :
    (message, signature) ∈ short.signed ↔
      (message, unpackOld signature) ∈ long.signed := by
  constructor
  · intro hm
    rw [h.signed] at hm
    obtain ⟨e, he, hp⟩ := List.mem_map.mp hm
    rcases e with ⟨m, σ⟩
    simp only at hp
    have hm' : m = message := congrArg Prod.fst hp
    have hs' : packOld σ = signature := congrArg Prod.snd hp
    have hc : CanonicalWitness (Ref.expandRef σ) := h.canonical (m, σ) he
    have hround : unpackOld (packOld σ) = σ := unpack_packOld σ hc
    have hpair : (message, unpackOld signature) = (m, σ) := by
      apply Prod.ext
      · exact hm'.symm
      · exact (congrArg unpackOld hs'.symm).trans hround
    rw [hpair]
    exact he
  · intro hm
    have hc := h.canonical _ hm
    have hr := unpack_packOld (unpackOld signature) hc
    have hp : packOld (unpackOld signature) = signature := unpackOld_injective hr
    rw [h.signed, ← hp]
    exact List.mem_map.mpr ⟨(message, unpackOld signature), hm, rfl⟩

theorem freshSignature_eq {short : Transcript sizes} {long : Transcript oldSizes}
    (h : TranscriptRel short long) (message : Message) (signature : Bytes 6398) :
    short.freshSignature message signature =
      long.freshSignature message (unpackOld signature) := by
  unfold Transcript.freshSignature
  congr 1
  apply Bool.eq_iff_iff.mpr
  simpa only [List.contains_iff_mem] using signed_mem_iff h message signature

theorem freshMessage_eq {short : Transcript sizes} {long : Transcript oldSizes}
    (h : TranscriptRel short long) (message : Message) :
    short.freshMessage message = long.freshMessage message := by
  unfold Transcript.freshMessage
  rw [h.signed, List.any_map]
  rfl

/-- The part of `Transcript.record` observed by the game. -/
def recordVC {sz : Sizes} (T : Transcript sz) (message : Message)
    (value : Option (Bytes sz.signature)) (calls : Nat) : Transcript sz :=
  { signed := match value with
      | none => T.signed
      | some signature => (message, signature) :: T.signed
    signingRequests := T.signingRequests + 1
    hashCalls := T.hashCalls + calls }

theorem record_eq_recordVC {sz : Sizes} (T : Transcript sz) (message : Message)
    (result : RunResult (Bytes sz.signature)) :
    T.record message result = recordVC T message result.value result.hashCalls := rfl

theorem record_rel {short : Transcript sizes} {long : Transcript oldSizes}
    (h : TranscriptRel short long) (message : Message)
    (value : Option (Bytes 6404)) (calls : Nat)
    (hcanon : ∀ σ, value = some σ → CanonicalWitness (Ref.expandRef σ)) :
    TranscriptRel (recordVC short message (value.map packOld) calls)
      (recordVC long message value calls) := by
  cases value with
  | none =>
    refine ⟨by simpa [recordVC] using h.signed,
      by simpa [recordVC] using h.signingRequests,
      by simpa [recordVC] using congrArg (· + calls) h.hashCalls, ?_⟩
    simpa [recordVC] using h.canonical
  | some σ =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [recordVC, Option.map_some, List.map_cons]
      rw [h.signed]
    · simpa [recordVC] using h.signingRequests
    · simpa [recordVC] using congrArg (· + calls) h.hashCalls
    · intro e he
      rcases List.mem_cons.mp he with he | he
      · subst e
        exact hcanon σ rfl
      · exact h.canonical e he

/-- Only values and hash-call counts affect the security game. -/
def observed {α : Type} (result : RunResult α) : Option α × Nat :=
  (result.value, result.hashCalls)

structure Assumptions (layout : Layout) (oldImages shortImages : Phase → Riscv.Image) : Prop where
  keygen : ∀ sk : SecretKey,
    (observed <$> (shortSubmission layout shortImages).run .keygen sk) =
      (observed <$> (oldSubmission layout oldImages).run .keygen sk)
  sign : ∀ (sk : SecretKey) (cache : Bytes CACHE_BYTES) (message : Message),
    (observed <$> (shortSubmission layout shortImages).run .sign (sk, cache, message)) =
      ((fun r => (r.value.map packOld, r.hashCalls)) <$>
        (oldSubmission layout oldImages).run .sign (sk, cache, message))
  expand : ∀ (message : Message) (pk : PublicKey) (signature : Bytes 6398),
    (observed <$> (shortSubmission layout shortImages).run .expand (message, pk, signature)) =
      (observed <$> (oldSubmission layout oldImages).run .expand
        (message, pk, unpackOld signature))
  verify : ∀ (message : Message) (pk : PublicKey) (witness : Bytes 6404),
    (observed <$> (shortSubmission layout shortImages).run .verify (message, pk, witness)) =
      (observed <$> (oldSubmission layout oldImages).run .verify (message, pk, witness))
  canonical : ∀ (sk : SecretKey) (cache : Bytes CACHE_BYTES) (message : Message)
    (result : RunResult (Bytes 6404)),
    result ∈ support ((oldSubmission layout oldImages).run .sign (sk, cache, message)) →
    ∀ σ, result.value = some σ → CanonicalWitness (Ref.expandRef σ)

theorem check_witness_observed (sub : Submission) (pk : PublicKey)
    (T : Transcript sub.sizes) (message : Message) (witness : Bytes sub.sizes.witness) :
    sub.checkForgery pk T (.witness message witness) =
      (fun p : Option Unit × Nat =>
        (⟨p.1.isSome && T.freshMessage message, T.hashCalls + p.2⟩ : AttackResult)) <$>
        (observed <$> sub.run .verify (message, pk, witness)) := by
  simp only [Submission.checkForgery, observed, Functor.map_map]
  rw [map_eq_bind_pure_comp]
  rfl

theorem check_signature_observed (sub : Submission) (pk : PublicKey)
    (T : Transcript sub.sizes) (message : Message) (signature : Bytes sub.sizes.signature) :
    sub.checkForgery pk T (.signature message signature) =
      (observed <$> sub.run .expand (message, pk, signature)) >>= fun p =>
        match p.1 with
        | none => pure ⟨false, T.hashCalls + p.2⟩
        | some witness =>
            (fun q : Option Unit × Nat =>
              (⟨q.1.isSome && T.freshSignature message signature,
                T.hashCalls + p.2 + q.2⟩ : AttackResult)) <$>
              (observed <$> sub.run .verify (message, pk, witness)) := by
  unfold Submission.checkForgery
  rw [bind_map_left]
  apply bind_congr
  intro result
  rcases result with ⟨value, finished, cycles, calls, blocks⟩
  cases value with
  | none => rfl
  | some witness =>
    simp only [observed, Functor.map_map]
    rw [map_eq_bind_pure_comp]
    rfl

theorem checkForgery_eq {layout : Layout} {oldImages shortImages : Phase → Riscv.Image}
    (H : Assumptions layout oldImages shortImages) (pk : PublicKey)
    {short : Transcript sizes} {long : Transcript oldSizes}
    (h : TranscriptRel short long) (candidate : Forgery sizes) :
    (shortSubmission layout shortImages).checkForgery pk short candidate =
      (oldSubmission layout oldImages).checkForgery pk long (liftForgery candidate) := by
  cases candidate with
  | witness message witness =>
    simp only [liftForgery]
    rw [check_witness_observed, check_witness_observed,
      H.verify message pk witness, freshMessage_eq h message, h.hashCalls]
  | signature message signature =>
    simp only [liftForgery]
    rw [check_signature_observed, check_signature_observed,
      H.expand message pk signature]
    apply bind_congr
    intro p
    cases p.1 with
    | none => simp only [h.hashCalls]
    | some witness =>
      dsimp only
      rw [H.verify message pk witness, freshSignature_eq h message signature, h.hashCalls]

theorem hash_rel {short : Transcript sizes} {long : Transcript oldSizes}
    (h : TranscriptRel short long) :
    TranscriptRel { short with hashCalls := short.hashCalls + 1 }
      { long with hashCalls := long.hashCalls + 1 } := by
  exact ⟨h.signed, h.signingRequests, congrArg (· + 1) h.hashCalls, h.canonical⟩

theorem liftM_bind_observed {α β : Type} (X : OracleComp HashSpec (RunResult α))
    (K : Option α × Nat → OracleComp World β) :
    ((liftM X : OracleComp World _) >>= fun r => K (observed r)) =
      ((liftM (observed <$> X) : OracleComp World _) >>= K) := by
  rw [liftM_map, bind_map_left]

theorem liftM_bind_map {α β γ : Type} (X : OracleComp HashSpec α)
    (f : α → β) (K : β → OracleComp World γ) :
    ((liftM (f <$> X) : OracleComp World _) >>= K) =
    ((liftM X : OracleComp World _) >>= fun r => K (f r)) := by
  rw [liftM_map, bind_map_left]

theorem interact_eq {layout : Layout} {oldImages shortImages : Phase → Riscv.Image}
    (H : Assumptions layout oldImages shortImages) (A : Adversary sizes)
    (sk : SecretKey) (pk : PublicKey) :
    ∀ rounds (state : A.State) (short : Transcript sizes) (long : Transcript oldSizes),
      TranscriptRel short long →
      (shortSubmission layout shortImages).interact A sk pk rounds state short =
        (oldSubmission layout oldImages).interact (liftAdversary A) sk pk rounds state long := by
  intro rounds
  induction rounds with
  | zero =>
    intro state short long h
    simp only [Submission.interact, h.hashCalls]
  | succ rounds ih =>
    intro state short long h
    cases hstep : A.step state with
    | submit candidate =>
      simp only [Submission.interact, hstep, liftAdversary, liftAction]
      exact congrArg (fun X : OracleComp HashSpec AttackResult =>
        (liftM X : OracleComp World AttackResult)) (checkForgery_eq H pk h candidate)
    | hash input resume =>
      simp only [Submission.interact, hstep, liftAdversary, liftAction]
      apply bind_congr
      intro answer
      exact ih (resume answer) _ _ (hash_rel h)
    | sample n resume =>
      simp only [Submission.interact, hstep, liftAdversary, liftAction]
      apply bind_congr
      intro answer
      exact ih (resume answer) _ _ h
    | step next =>
      simp only [Submission.interact, hstep, liftAdversary, liftAction]
      exact ih next _ _ h
    | sign request resume =>
      by_cases hk : short.signingRequests < LIFETIME
      · have hkL : long.signingRequests < LIFETIME := by
          simpa [h.signingRequests] using hk
        simp only [Submission.interact, hstep, liftAdversary, liftAction,
          hk, hkL, if_true, Submission.signingOracle, record_eq_recordVC]
        let newX : OracleComp HashSpec (RunResult (Bytes 6398)) :=
          (shortSubmission layout shortImages).run .sign (sk, request.cache, request.message)
        let oldX : OracleComp HashSpec (RunResult (Bytes 6404)) :=
          (oldSubmission layout oldImages).run .sign (sk, request.cache, request.message)
        change ((liftM newX : OracleComp World _) >>= fun r =>
            (shortSubmission layout shortImages).interact A sk pk rounds (resume r.value)
              (recordVC short request.message r.value r.hashCalls)) =
          ((liftM oldX : OracleComp World _) >>= fun r =>
            (oldSubmission layout oldImages).interact (liftAdversary A) sk pk rounds
              (resume (r.value.map packOld))
              (recordVC long request.message r.value r.hashCalls))
        calc
          _ = (liftM (observed <$> newX) : OracleComp World _) >>= fun p =>
                (shortSubmission layout shortImages).interact A sk pk rounds (resume p.1)
                  (recordVC short request.message p.1 p.2) :=
            liftM_bind_observed newX _
          _ = (liftM ((fun r : RunResult (Bytes 6404) =>
                (r.value.map packOld, r.hashCalls)) <$> oldX) : OracleComp World _) >>= fun p =>
                (shortSubmission layout shortImages).interact A sk pk rounds (resume p.1)
                  (recordVC short request.message p.1 p.2) := by
            rw [H.sign sk request.cache request.message]
          _ = (liftM oldX : OracleComp World _) >>= fun r =>
                (shortSubmission layout shortImages).interact A sk pk rounds
                  (resume (r.value.map packOld))
                  (recordVC short request.message (r.value.map packOld) r.hashCalls) :=
            liftM_bind_map oldX _ _
          _ = _ := by
            apply OracleComp.bind_congr_of_forall_mem_support
            intro r hr
            have hr' : r ∈ support oldX := by
              change r ∈ support (oldX.liftComp World) at hr
              exact (OracleComp.mem_support_liftComp_iff oldX r).mp hr
            exact ih (resume (r.value.map packOld)) _ _
              (record_rel h request.message r.value r.hashCalls
                (fun σ hv => H.canonical sk request.cache request.message r hr' σ hv))
      · have hkL : ¬ long.signingRequests < LIFETIME := by
          simpa [h.signingRequests] using hk
        simp only [Submission.interact, hstep, liftAdversary, liftAction,
          hk, hkL, if_false, h.hashCalls]

def keygenTail (sub : Submission) (A : Adversary sub.sizes) (rounds : Nat)
    (sk : SecretKey) (p : Option (PublicKey × Bytes sub.sizes.cache) × Nat) :
    OracleComp World AttackResult :=
  match p.1 with
  | none => pure ⟨false, p.2⟩
  | some (pk, cache) =>
      sub.interact A sk pk rounds (A.initial pk cache) { hashCalls := p.2 }

theorem securityExperiment_observed (sub : Submission) (A : Adversary sub.sizes)
    (rounds : Nat) :
    sub.securityExperiment A rounds =
      withRandomness (do
        let sk ← liftM sampleSecretKey
        let p ← liftM (observed <$> sub.run .keygen sk)
        keygenTail sub A rounds sk p) := by
  unfold Submission.securityExperiment
  congr 1
  apply bind_congr
  intro sk
  simp only [liftM_map, bind_map_left]
  apply bind_congr
  intro result
  rcases result with ⟨value, finished, cycles, calls, blocks⟩
  cases value with
  | none => rfl
  | some pair =>
    rcases pair with ⟨pk, cache⟩
    rfl

theorem securityExperiment_eq {layout : Layout} {oldImages shortImages : Phase → Riscv.Image}
    (H : Assumptions layout oldImages shortImages) (A : Adversary sizes)
    (rounds : Nat) :
    (shortSubmission layout shortImages).securityExperiment A rounds =
      (oldSubmission layout oldImages).securityExperiment (liftAdversary A) rounds := by
  rw [securityExperiment_observed, securityExperiment_observed]
  congr 1
  apply bind_congr
  intro sk
  rw [H.keygen sk]
  apply bind_congr
  intro p
  rcases p with ⟨value, calls⟩
  cases value with
  | none => rfl
  | some pair =>
    rcases pair with ⟨pk, cache⟩
    simpa only [keygenTail, liftAdversary] using
      (interact_eq H A sk pk rounds (A.initial pk cache)
        { hashCalls := calls } { hashCalls := calls }
        ⟨rfl, rfl, rfl, by simp⟩)

theorem secure {layout : Layout} {oldImages shortImages : Phase → Riscv.Image}
    (H : Assumptions layout oldImages shortImages)
    (hOld : (oldSubmission layout oldImages).Secure) :
    (shortSubmission layout shortImages).Secure := by
  intro A rounds Q hQ
  rw [securityExperiment_eq H A rounds]
  exact hOld (liftAdversary A) rounds Q hQ

end SigGolfCandidate.Packed

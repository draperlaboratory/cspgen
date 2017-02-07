Require Import While_Definitions.
Require Import CSP_OpSem.
Require Import Coq.Structures.Equalities.
Require Import ZArith.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Numbers.BinNums.
Require Import List.

(* Sad fact: I need proof irrelevance, at least for proofs of (j <= k) where
   j, k : Z.  *)
Axiom le_irrel : forall (j k : Z) (Hle1 Hle2 : (j <= k) % Z), Hle1 = Hle2.

Hint Extern 2 => match goal with
  | [ H : ~ True |- _ ] => destruct H; exact I
  | [ H : False |- _ ] => inversion H
  end.

Module Type ArithRange.
  Parameter minInt : Z.
  Parameter maxInt : Z.
  
  Axiom min_le_0 : (minInt <= 0)%Z.
  Axiom max_ge_0 : (0 <= maxInt)%Z.
End ArithRange.

Module WhileToCSP (Import AR : ArithRange).
  Import Z.
  Open Scope Z.
  (* Here we set up the representation of values and events in the CSP model.
     In the model, an int is either unknown or a known value in some range from
     m to n, where m <= 0 <= n.  The only events are reads and writes to the
     memory.  The domain of the environment for the CSP process consists of the
     names of the processes representing each memory cell at each value.

     Note that our "var" type is infinite.  In practice, any particular While
     program can only use a finite number of variables.  When we construct the
     actual environment and representation of memory as CSP processes, this fact
     will be key.
  *)
  Inductive IntRepr : Set :=
  | IRKnown : forall k : Z, (minInt <= k) -> (k <= maxInt) -> IntRepr
  | IRUnknown : IntRepr.

  Inductive cspevent : Set :=
  | CERead  : var -> IntRepr -> cspevent
  | CEWrite : var -> IntRepr -> cspevent.

  Module CSPEventType <: Typ.
    Definition t := cspevent.
  End CSPEventType.

  Inductive env_names : Set :=
  | VarState : var -> IntRepr -> env_names.

  Module EnvNamesType <: Typ.
    Definition t := env_names.
  End EnvNamesType.

  Module Export CSPOS := OpSem (CSPEventType) (EnvNamesType).

  Definition min_le_max : minInt <= maxInt :=
    le_trans minInt 0 maxInt min_le_0 max_ge_0.

  (* Next we have some helper functions for dealing with the range of values
     represented by IntRepr.  A common case is to have an external choice over
     reading or writing any particular value to a variable.

     The definition of this is a little tricky, because the argument that it
     terminates is not completely obvious.  We want to define:

           p (maxInt) [] p (maxInt - 1) [] p (maxInt - 2) [] ... [] p (minInt)

     But we can't directly do recursion over ints in this way.  Instead, we do
     the recursion over a nat n, where (0 <= n <= maxInt - minInt).  So if
     the current argument is n, the clause for this step is (p (n + minInt)).
   *)
  Theorem le_add_positive : forall j k, 0 <= k -> j <= j + k.
  Proof.  intros. omega.  Qed.

  Fixpoint knownIntChoice (n : nat)
                          (n_Range : (of_nat n <= maxInt - minInt))
                          (p : IntRepr -> Proc) : Proc :=
    (match n as y return n = y -> Proc with
     | O    => fun _ =>
         p (IRKnown minInt (le_refl _) (le_trans _ _ _ min_le_0 max_ge_0))
     | S n' => fun n_eq => 
         PExtChoice
           (p (IRKnown (minInt + (of_nat n))
                       (le_add_positive _ _ (Zle_0_nat _))
                       (match le_add_le_sub_l _ _ _ with
                        | conj _ f => f n_Range
                        end)))
              (knownIntChoice n'
                 (le_trans _ _ _
                    (inj_le _ _
                      (eq_ind_r (fun x => (n' <= x)%nat)
                                (le_S _ _ (le_n _)) n_eq))
                    n_Range)
                 p)
     end) Logic.eq_refl.

  Theorem of_nat_to_nat_le :
    of_nat (to_nat (maxInt - minInt)) <= maxInt - minInt.
  Proof.
    rewrite Z2Nat.id.
    - apply le_refl.
    - apply Zle_minus_le_0.
      apply le_trans with (m := 0).
      + exact min_le_0.
      + exact max_ge_0.
  Qed.        

  Definition extChoiceInt (p : IntRepr -> Proc) : Proc :=
    PExtChoice
      (p IRUnknown)
      (knownIntChoice (to_nat (maxInt - minInt)) of_nat_to_nat_le p).
    
  Definition bound_Z (z : Z) : IntRepr :=
    match Z_le_dec minInt z with
    | left Hmin =>
      match Z_le_dec z maxInt with
      | left Hmax => IRKnown z Hmin Hmax
      | right _ => IRUnknown
      end
    | right _    => IRUnknown
    end.
    
  Definition lift_Z_fun (f : Z -> Z -> Z) (j k : IntRepr) : IntRepr :=
    match j, k with
    | IRUnknown , _ => IRUnknown
    | _ , IRUnknown => IRUnknown
    | IRKnown n _ _, IRKnown m _ _ => bound_Z (f n m)
    end.

  Definition lift_Z_test (f : Z -> Z -> bool) (j k : IntRepr) : IntRepr :=
    match j, k with
    | IRUnknown , _ => IRUnknown
    | _ , IRUnknown => IRUnknown
    | IRKnown n _ _, IRKnown m _ _ => bound_Z (if f n m then 1 else 0)
    end.

  Definition lift_Z_not (j : IntRepr) : IntRepr :=
    match j with
    | IRUnknown => IRUnknown
    | IRKnown z _ _ => (bound_Z (if eqb z 0 then 1 else 0))
    end.
  
  Fixpoint compile_exp (e : exp) (k : IntRepr -> Proc) : Proc :=
    match e with
    | EVar x => extChoiceInt (fun v => PPrefix (CERead x v) (k v))
    | ENum v => k (bound_Z v)
    | EPlus e1 e2 => compile_exp e1 (fun v1 => compile_exp e2 (fun v2 =>
      k (lift_Z_fun Z.add v1 v2)))
    | EMinus e1 e2 => compile_exp e1 (fun v1 => compile_exp e2 (fun v2 =>
      k (lift_Z_fun Z.sub v1 v2)))
    | ETimes e1 e2 => compile_exp e1 (fun v1 => compile_exp e2 (fun v2 =>
      k (lift_Z_fun Z.mul v1 v2)))
    | EEq e1 e2 => compile_exp e1 (fun v1 => compile_exp e2 (fun v2 =>
      k (lift_Z_test Z.eqb v1 v2)))
    | ELTE e1 e2 => compile_exp e1 (fun v1 => compile_exp e2 (fun v2 =>
      k (lift_Z_test Z.leb v1 v2)))
    | ENot e => compile_exp e (fun v1 => k (lift_Z_not v1))
    | EOr e1 e2 => compile_exp e1 (fun v1 => compile_exp e2 (fun v2 =>
      k (lift_Z_test (fun z1 z2 => negb (andb (eqb z1 0) (eqb z2 0))) v1 v2)))
    | EAnd e1 e2 => compile_exp e1 (fun v1 => compile_exp e2 (fun v2 =>
      k (lift_Z_test (fun z1 z2 => negb (orb (eqb z1 0) (eqb z2 0))) v1 v2)))
    end.

  Fixpoint compile (c : cmd) (k : Proc) : Proc :=
  match c with
  | CSkip => k
  | CAssn x e => compile_exp e 
                     (fun v => PPrefix (CEWrite x v) k)
  | CSeq c1 c2 => compile c1 (compile c2 k)
  | CIf e c1 c2 => compile_exp e (fun v =>
     match v with
     | IRKnown z _ _ => if Z.eqb z 0 then compile c2 k else compile c1 k
     | IRUnknown => PIntChoice (compile c1 k) (compile c2 k)
     end)
  | CWhile e c => PMu (compile_exp e (fun v =>
     match v with 
     | IRKnown z _ _ =>
       if Z.eqb z 0 then (lift k 0) else compile c (PBVar 0)
     | IRUnknown =>
       PIntChoice (compile c (PBVar 0)) (lift k 0)
     end))
  end.
End WhileToCSP.

Module CompilerProofs (Import AR : ArithRange).
  Import Z.
  Open Scope Z.

  Module Import Comp := (WhileToCSP (AR)).

  (* This maps free variables to their implementations.  In the current model,
     there is a free variable for each representable value of each variable. *)
  Definition VarImpl (var : nat) (val : IntRepr) :=
    PExtChoice (PPrefix (CERead var val) (PFVar (VarState var val)))
               (extChoiceInt (fun val' => 
                 PPrefix (CEWrite var val') (PFVar (VarState var val')))).
    

  Definition WhileEnv : Env := fun nm => 
  match nm with
  | VarState var val => VarImpl var val
  end.

  (* Traces and approximations.  We begin by building a simple theory of traces.
     This includes a translation of While program traces to CSP traces, and some
     relations for describing when two traces are comparable. *)

  Definition whileToCSPEvent (we : wevent) : Sigma :=
    match we with
    | WEvRead x z => CERead x (bound_Z z)
    | WEvWrite x z => CEWrite x (bound_Z z)
    end.

  Definition whileToCSPTrace (wtrace  : list wevent) : Trace :=
    map whileToCSPEvent wtrace.

  Inductive ApproxIntRepr : IntRepr -> IntRepr -> Prop :=
  | AIRKnown     : forall n l1 l2 l3 l4,
      ApproxIntRepr (IRKnown n l1 l2) (IRKnown n l3 l4)
  | AIRApprox    : forall ir, ApproxIntRepr ir IRUnknown.

  Hint Constructors ApproxIntRepr.

  Theorem ApproxIntRepr_refl : forall ir,
    ApproxIntRepr ir ir.
  Proof.
    destruct ir; eauto.
  Qed.    
  Hint Resolve ApproxIntRepr_refl.

  Theorem ApproxIntRepr_trans : forall ir1 ir2 ir3,
    ApproxIntRepr ir1 ir2 -> ApproxIntRepr ir2 ir3 -> ApproxIntRepr ir1 ir3.
  Proof.
    intros ir1 ir2 ir3 H1 H2; inversion H1; subst; inversion H2; subst; eauto.
  Qed.

  Hint Extern 2 =>
    match goal with
    | [ H1 : ApproxIntRepr ?i1 ?i2,
        H2 : ApproxIntRepr ?i2 ?i3 |- ApproxIntRepr ?i1 ?i3 ]
      => exact (ApproxIntRepr_trans _ _ _ H1 H2)
    end.
  
  Theorem lift_Z_fun_approx : forall f i1 i1' i2 i2',
      ApproxIntRepr i1 i1'
   -> ApproxIntRepr i2 i2'
   -> ApproxIntRepr (lift_Z_fun f i1 i2) (lift_Z_fun f i1' i2').
  Proof.
    intros f i1 i1' i2 i2' HIRA1 HIRA2;
    inversion HIRA1; subst; inversion HIRA2; subst; eauto;
    repeat match goal with
    | [ i : IntRepr |- _ ] => destruct i; eauto
    end.
  Qed.

  Theorem lift_Z_test_approx : forall f i1 i1' i2 i2',
      ApproxIntRepr i1 i1'
   -> ApproxIntRepr i2 i2'
   -> ApproxIntRepr (lift_Z_test f i1 i2) (lift_Z_test f i1' i2').
  Proof.
    intros f i1 i1' i2 i2' HIRA1 HIRA2;
    inversion HIRA1; subst; inversion HIRA2; subst; eauto;
    repeat match goal with
    | [ i : IntRepr |- _ ] => destruct i; eauto
    end.
  Qed.

  Theorem lift_Z_not_approx : forall i1 i1',
      ApproxIntRepr i1 i1'
   -> ApproxIntRepr (lift_Z_not i1) (lift_Z_not i1').
  Proof.
    intros i1 i2 HIRA1; inversion HIRA1; subst; eauto.
  Qed.  

  Hint Resolve lift_Z_fun_approx lift_Z_test_approx lift_Z_not_approx.

  Inductive ApproxEvent : Sigma -> Sigma -> Prop :=
  | AERead : forall x v v', 
        ApproxIntRepr v v'
     -> ApproxEvent (CERead x v) (CERead x v')
  | AEWrite : forall x v v',
        ApproxIntRepr v v'
     -> ApproxEvent (CEWrite x v) (CEWrite x v').

  Hint Constructors ApproxEvent.

  Theorem ApproxEvent_refl : forall c, ApproxEvent c c.
  Proof.
    intros c; destruct c; eauto.
  Qed.   

  Theorem ApproxEvent_trans : forall c1 c2 c3, 
      ApproxEvent c1 c2 -> ApproxEvent c2 c3 -> ApproxEvent c1 c3.
  Proof.
    inversion 1; inversion 1; subst; eauto.
  Qed.   

  Hint Resolve ApproxEvent_refl.

  Inductive ApproxTrace : Trace -> Trace -> Prop :=
  | ATNil  : ApproxTrace nil nil
  | ATACons : forall ev ev' trace trace',
         ApproxEvent ev ev'
      -> ApproxTrace trace trace'
      -> ApproxTrace (ev :: trace) (ev' :: trace').

  Hint Constructors ApproxTrace.

  Theorem ApproxTrace_append : forall t1 t2 t1' t2',
         ApproxTrace t1 t1'
      -> ApproxTrace t2 t2'
      -> ApproxTrace (t1 ++ t2) (t1' ++ t2').
  Proof.
    induction 1; intros; simpl; eauto.
  Qed.    

  Theorem ApproxTrace_refl : forall t,
      ApproxTrace t t.
  Proof.
    intros t.  induction t; eauto.
  Qed.

  Hint Resolve ApproxTrace_refl ApproxTrace_append.

  Theorem ApproxTrace_trans : forall t1 t2 t3,
    ApproxTrace t1 t2 -> ApproxTrace t2 t3 -> ApproxTrace t1 t3.
  Proof.
    intros t1 t2 t3 HAT. revert t3.
    induction HAT; inversion 1; subst; eauto using ApproxEvent_trans.
  Qed.    
    
  (* Here begins our long struggle with characterizing the types of processes
     that are valid representations of a while program's memory.  The basic idea
     is that we call out a very particular class of processes - a bunch of
     variables running in unsynchronized parallel - and call these a valid
     memory.

     The particulars are a little messy.  When we actually define a memory, the
     "variable" processes will be defined by reference into WhileEnv.  But any
     of these may at any time take a tau step to unfold this definition from
     WhileEnv.  So, either form needs to be a valid memory.
   *)

  Inductive ValidVarRep : nat -> IntRepr -> Proc -> Prop :=
  | VVRFolded : forall n ir, ValidVarRep n ir (PFVar (VarState n ir))
  | VVRUnfolded : forall n ir, ValidVarRep n ir (VarImpl n ir).

  Inductive ApproxVar (n : nat) : Proc -> Proc -> Prop :=
  | AVLift : forall v v' ir ir',
        ValidVarRep n ir v
     -> ValidVarRep n ir' v'
     -> ApproxIntRepr ir ir'
     -> ApproxVar n v v'.

  Inductive EquivVar : nat -> Proc -> Proc -> Prop := 
  | EVLift : forall n v v' ir,
        ValidVarRep n ir v
     -> ValidVarRep n ir v'
     -> EquivVar n v v'.
  Hint Constructors EquivVar.

  Theorem EquivVar_trans : forall n v1 v2 v3,
      EquivVar n v1 v2 -> EquivVar n v2 v3 -> EquivVar n v1 v3.
  Proof.
    intros n v1 v2 v3 HAV1; revert v3; induction HAV1; eauto;
    intros v3 HAV2; inversion HAV2; subst; eauto.

    econstructor.
    eassumption.
    inversion H0; subst; inversion H1; subst; eauto.
  Qed.

  Hint Extern 2 =>
    match goal with
    | [ H1 : EquivVar ?n ?v1 ?v2,
        H2 : EquivVar ?n ?v2 ?v3 |- EquivVar ?n ?v1 ?v3 ]
      => exact (EquivVar_trans _ _ _ _ H1 H2)
    end.

  Theorem EquivVar_sym : forall n v1 v2,
    EquivVar n v1 v2 -> EquivVar n v2 v1.
  Proof.
    inversion 1; subst; eauto.
  Qed.

  Hint Extern 1 =>
    match goal with
    | [ H : EquivVar _ ?v1 ?v2 |- EquivVar _ ?v2 ?v1 ]
      => exact (EquivVar_sym _ _ _ H)
    end.

  Theorem ApproxVar_respects_EquivVar_left : forall n v1 v2 v1',
       ApproxVar n v1 v2
    -> EquivVar n v1 v1'
    -> ApproxVar n v1' v2.
  Proof.
    inversion 1; subst; inversion 1; subst; eauto.
    eapply AVLift; eauto.  inversion H0; subst; inversion H4; subst; eauto.
  Qed.     

  Theorem ApproxVar_respects_EquivVar_right : forall n v1 v2 v2',
       ApproxVar n v1 v2
    -> EquivVar n v2 v2'
    -> ApproxVar n v1 v2'.
  Proof.
    inversion 1; subst; inversion 1; subst; eauto.
    eapply AVLift; eauto.  inversion H1; subst; inversion H4; subst; eauto.
  Qed.     
    
  Inductive ApproxMem : nat -> Proc -> Proc -> Prop :=
  | AMZero : ApproxMem O PStop PStop
  | AMSucc : forall n v v' m m',
         ApproxVar n v v'
      -> ApproxMem n m m'
      -> ApproxMem (S n) (PGenPar v noEvents m)
                         (PGenPar v' noEvents m').
     
  Hint Constructors ValidVarRep ApproxVar ApproxMem EquivVar.

  Inductive ValidMemRep : nat -> Proc -> Prop := 
  | VMZero : ValidMemRep O PStop
  | VMSucc : forall n ir v m, 
         ValidMemRep n m 
      -> ValidVarRep n ir v
      -> ValidMemRep (S n) (PGenPar v noEvents m).

  Hint Constructors ValidMemRep.

  Theorem ApproxMem_Valid_left : forall n m1 m2,
     ApproxMem n m1 m2 -> ValidMemRep n m1.
  Proof.
    induction 1; eauto.  inversion H; eauto.
  Qed.   

  Theorem ApproxMem_Valid_right : forall n m1 m2,
     ApproxMem n m1 m2 -> ValidMemRep n m2.
  Proof.
    induction 1; eauto.  inversion H; eauto.
  Qed.   
  
  Hint Extern 1 => match goal with
  | [ HA : ApproxMem _ ?m1 _ |- ValidMemRep _ ?m1 ] =>
    exact (ApproxMem_Valid_left _ _ _ HA)
  | [ HA : ApproxMem _ _ ?m2 |- ValidMemRep _ ?m2 ] =>
    exact (ApproxMem_Valid_right _ _ _ HA)
  end.

  Theorem ApproxMem_refl : forall n m,
      ValidMemRep n m -> ApproxMem n m m.
  Proof.  
    intros n m HValid; induction HValid; eauto.
  Qed.

  Hint Resolve ApproxMem_refl.

  Inductive EquivMem : nat -> Proc -> Proc -> Prop :=
  | EMZero : EquivMem O PStop PStop
  | EMSucc : forall n v v' m m',
         EquivVar n v v'
      -> EquivMem n m m'
      -> EquivMem (S n) (PGenPar v noEvents m)
                        (PGenPar v' noEvents m').

  Hint Constructors EquivMem.

  Theorem EquivMem_refl : forall n m,
      ValidMemRep n m -> EquivMem n m m.
  Proof.  
    intros n m HValid; induction HValid; eauto.
  Qed.

  Hint Resolve EquivMem_refl.

  Theorem EquivMem_trans : forall n mem1 mem2 mem3,
     EquivMem n mem1 mem2 -> EquivMem n mem2 mem3 -> EquivMem n mem1 mem3.
  Proof.  
    intros n mem1 mem2 mem3 HAM1; generalize dependent mem3.
    induction HAM1; eauto; intros mem3 HAM2; inversion HAM2; subst; eauto.
  Qed.

  Theorem EquivMem_sym : forall n mem1 mem2,
    EquivMem n mem1 mem2 -> EquivMem n mem2 mem1.
  Proof.
    induction 1; eauto.
  Qed.

  Hint Extern 1 =>
    match goal with
    | [ H : EquivMem _ ?v1 ?v2 |- EquivMem _ ?v2 ?v1 ]
      => exact (EquivMem_sym _ _ _ H)
    end.

  Theorem EquivMem_Valid_left : forall n m1 m2,
    EquivMem n m1 m2 -> ValidMemRep n m1.
  Proof.
    induction 1; eauto.
    inversion H; eauto.
  Qed.

  Theorem EquivMem_Valid_right : forall n m1 m2,
    EquivMem n m1 m2 -> ValidMemRep n m2.
  Proof.
    induction 1; eauto.
    inversion H; eauto.
  Qed.

  Hint Extern 1 => match goal with
  | [ HA : EquivMem _ ?m1 _ |- ValidMemRep _ ?m1 ] =>
    exact (EquivMem_Valid_left _ _ _ HA)
  | [ HA : EquivMem _ _ ?m2 |- ValidMemRep _ ?m2 ] =>
    exact (EquivMem_Valid_right _ _ _ HA)
  end.
  
  Theorem ApproxMem_respects_EquivMem_left : forall nfvs m1 m2 m1',
       ApproxMem nfvs m1 m2
    -> EquivMem nfvs m1 m1'
    -> ApproxMem nfvs m1' m2.
  Proof.
    intros nfvs m1 m2 m1' HAM; revert m1'; induction HAM; intros m1' HEM;
    eauto; inversion HEM; subst; 
    eauto using ApproxVar_respects_EquivVar_left.
  Qed.

  Theorem ApproxMem_respects_EquivMem_right : forall nfvs m1 m2 m2',
       ApproxMem nfvs m1 m2
    -> EquivMem nfvs m2 m2'
    -> ApproxMem nfvs m1 m2'.
  Proof.
    intros nfvs m1 m2 m2' HAM; revert m2'; induction HAM; intros m2' HEM;
    inversion HEM; subst;
    eauto using ApproxVar_respects_EquivVar_right.
  Qed.
  
  Definition ApproxProc (p m p' m' : Proc) : Prop :=
    forall t,
         OpSemTraces WhileEnv (PGenPar p allEvents m) t
      -> exists t', ApproxTrace t t'
                 /\ OpSemTraces WhileEnv (PGenPar p' allEvents m') t'.

  (* A version of ApproxProc which 
          a) is restricted to traces under a given length and 
          b) unfolds OpSemTraces
  *)
  Definition ApproxProcN (n : nat) (p m p' m' : Proc) : Prop :=
    forall evs q,
         (length evs <= n) % nat
      -> MStep WhileEnv (PGenPar p allEvents m) evs q
      -> exists evs' q',
             ApproxTrace (observableEvents evs) (observableEvents evs')
          /\ MStep WhileEnv (PGenPar p' allEvents m') evs' q'.

  Transparent ApproxProc ApproxProcN.
  Hint Unfold ApproxProc ApproxProcN.

  Theorem ApproxProc_ApproxProcN : forall n p1 m1 p2 m2,
        ApproxProc p1 m1 p2 m2
     -> ApproxProcN n p1 m1 p2 m2.
  Proof.
    unfold ApproxProc; unfold ApproxProcN; intros.
    apply TStepsTo in H1.
    apply H in H1.
    destruct H1 as [? [? ?]].
    inversion H2; subst; eauto.
  Qed.

  Theorem ApproxProcN_ApproxProc : forall p1 m1 p2 m2,
       (forall n, ApproxProcN n p1 m1 p2 m2)
    -> ApproxProc p1 m1 p2 m2.
  Proof.
    unfold ApproxProc; intros p1 m1 p2 m2 HAPN evs HOST.
    inversion HOST; subst.
    apply (HAPN (length evs0)) in H; eauto.
    destruct H as [evs' [q' [? ?]]].
    exists (observableEvents evs'); eauto.
  Qed.

  Hint Extern 1 =>
  match goal with 
  | [ H : Step _ PStop _ _ |- _ ] => inversion H
  end.


  (***********************************************************************
   *** Begin tricky extChoiceInt reasoning
   ***********************************************************************)
  
  (* This next few proofs are tricky!  It is where we prove something about
     extChoiceInt.  Figuring out how to make the induction we do in these
     proofs possible was a tricky bit of proof engineering involving several
     revisions of extChoiceInt and some intricate set up in the proofs
     themsevles. *)

  Theorem extChoiceInt_Sigma_step_inversion : forall D p s p',
       Step D (extChoiceInt p) (EvSigma s) p'
    -> exists ir, Step D (p ir) (EvSigma s) p'.
  Proof.
    intros D p e p' HStep.
    unfold extChoiceInt in HStep.
    inversion HStep; subst; eauto.
    clear HStep.

    remember of_nat_to_nat_le as pf.
    clear Heqpf.
    remember (to_nat (maxInt - minInt)) as n.
    clear Heqn.
    generalize dependent p'.  revert H5.  revert D p e pf.

    induction n; intros; simpl in *; eauto.

    inversion H2; subst; eauto.
  Qed.

  Theorem extChoiceInt_Tau_step_inversion : forall D p p',
       Step D (extChoiceInt p) EvTau p'
    -> exists ir, exists p'', Step D (p ir) EvTau p''.
  Proof.
    intros D p p' HStep.
    unfold extChoiceInt in HStep.
    inversion HStep; subst; eauto.
    - destruct H5; auto.
    - clear HStep.

      remember of_nat_to_nat_le as pf.
      clear Heqpf.
      remember (to_nat (maxInt - minInt)) as n.
      clear Heqn.
      generalize dependent p2'.  revert D p pf.
      
      induction n; intros; simpl in *; eauto.
      inversion H1; subst; eauto.
  Qed.

  (* Note that the non-empty trace here is critical.  That is, the following
     isn't a theorem:

          forall D pChoice t i q, 
               MStep D (pChoice i) t q 
            -> MStep D (extChoiceInt pChoice) t q.

     There's a counterexample when t = nil, since (pChoice i) multisteps to
     itself, but (extChoiceInt pChoice) doesn't step to (pChoice i).

     Luckily, in the case when t = nil, the OpSemTraces version holds anyway
     because nil is a trace of everything. *)
  Theorem MStep_extChoiceInt : forall D pChoice i evs q,
        MStep D (pChoice i) evs q
     -> observableEvents evs <> nil
     -> MStep D (extChoiceInt pChoice) evs q.
  Proof.
    intros. unfold extChoiceInt. destruct i.
    - apply MStep_PExtChoice_Right; auto.
      remember of_nat_to_nat_le as rangePf.
      clear HeqrangePf.
      remember (to_nat (maxInt - minInt)) as range.
      assert ((to_nat (k - minInt) <= range) % nat).
        subst. apply Z2Nat.inj_le; eauto; try omega.
      clear Heqrange.
      generalize dependent k.  revert rangePf.
      induction range; intros; eauto.
      + simpl.
        match goal with
        | [ HNatLE : (to_nat (?k - minInt) <= O) % nat |- _ ] =>
          replace O with (to_nat 0) in HNatLE by eauto;
          apply Z2Nat.inj_le in HNatLE; eauto; try omega;
          assert (k = minInt) by omega; subst
        end.
        assert (l = le_refl minInt) by (auto using le_irrel).
        assert (l0 = le_trans minInt 0 maxInt min_le_0 max_ge_0)
            by (auto using le_irrel).
        subst.  assumption.
      + simpl.
        apply le_lt_or_eq in H1.
        destruct H1.
        * apply MStep_PExtChoice_Right; eauto.
          eapply IHrange; eauto.  omega.
        * apply MStep_PExtChoice_Left; auto.
          assert (k = minInt + pos (Pos.of_succ_nat range))
            by (rewrite Zpos_P_of_succ_nat;
                rewrite <- Nat2Z.inj_succ;
                rewrite <- H1; clear H1;
                rewrite Z2Nat.id; omega).
          subst.
          match goal with
          [ HExact : MStep _ (pChoice (IRKnown ?ir ?p1 ?p2)) ?t ?q
           |- MStep _ (pChoice (IRKnown ?ir ?p1' ?p2')) ?t ?q ] =>
            replace p1' with p1 by (auto using le_irrel);
            replace p2' with p2 by (auto using le_irrel);
            exact HExact
          end.
    - apply MStep_PExtChoice_Left; assumption.
  Qed.

  Hint Extern 2 => match goal with
  | [ |- _ :: _ <> nil ] => intros HContra; inversion HContra
  | [ |- nil <> _ :: _ ] => intros HContra; inversion HContra
  end.

  Theorem OpSemTraces_extChoiceInt : forall D pChoice t i,
        OpSemTraces D (pChoice i) t
     -> OpSemTraces D (extChoiceInt pChoice) t.
  Proof.
    intros D pChoice t i HOST.
    destruct t; eauto.
    inversion HOST; subst.
    eapply TStepsTo.  eapply MStep_extChoiceInt; eauto.
    rewrite H; eauto.
  Qed.

  Theorem extChoiceInt_extensional : forall k1 k2,
       (forall ir, k1 ir = k2 ir)
    -> extChoiceInt k1 = extChoiceInt k2.
  Proof.
    intros k1 k2 HEq.
    unfold extChoiceInt; f_equal; eauto.

    remember of_nat_to_nat_le as pf.
    clear Heqpf.
    remember (to_nat (maxInt - minInt)) as n.
    clear Heqn.  
    induction n; simpl; eauto.
    f_equal; eauto.
  Qed.    

  Theorem open_extChoiceInt : forall u n k,
      {n ~> u} (extChoiceInt k) = extChoiceInt (fun v => {n ~> u} (k v)).
  Proof.
    intros u n k; unfold extChoiceInt; simpl.
    f_equal; eauto.

    remember of_nat_to_nat_le as pf.
    clear Heqpf.
    remember (to_nat (maxInt - minInt)) as m.
    clear Heqm.  
    induction m; simpl; eauto.
    f_equal; eauto.
  Qed.


  (***********************************************************************
   *** End tricky extChoiceInt reasoning
   ***********************************************************************)
  Theorem ValueInVar_may_be_read : forall n v ir,
    ValidVarRep n ir v -> 
    exists evs, MStep WhileEnv v evs v
             /\ observableEvents evs = CERead n ir :: nil.
  Proof.
    inversion 1; subst.
    - exists (EvTau :: EvSigma (CERead n ir) :: nil); split; eauto.
      apply MSStep with (p' := WhileEnv (VarState n ir)); eauto.
      simpl. unfold VarImpl; eauto.
    - exists (EvSigma (CERead n ir) :: EvTau :: nil); split; eauto.
      unfold VarImpl; apply MSStep with (p' := PFVar (VarState n ir)); eauto.
  Qed.

  Theorem ValueInVar_may_be_written : forall n v ir ir',
       ValidVarRep n ir v
    -> exists evs, MStep WhileEnv v evs (PFVar (VarState n ir'))
                /\ observableEvents evs = CEWrite n ir' :: nil.
  Proof.
    intros. inversion H; subst.
    - exists (EvTau :: EvSigma (CEWrite n ir') :: nil); split; eauto.
      apply MStep_trans with (p2 := VarImpl n ir) (t1 := EvTau :: nil); eauto.
      unfold VarImpl.  apply MStep_PExtChoice_Right; simpl; eauto.
      apply MStep_extChoiceInt with (i := ir'); simpl; eauto.
   - exists (EvSigma (CEWrite n ir') :: nil); split; eauto.
     unfold VarImpl. apply MStep_PExtChoice_Right; simpl; eauto.
      apply MStep_extChoiceInt with (i := ir'); simpl; eauto.
  Qed.

  Theorem ValidVar_step_inversion : forall v ev v' n ir,
       Step WhileEnv v ev v'
    -> ValidVarRep n ir v
    -> (   (ev = EvTau /\ ValidVarRep n ir v')
        \/ (ev = EvSigma (CERead n ir) /\ ValidVarRep n ir v')
        \/ (exists ir', ev = EvSigma (CEWrite n ir') /\ ValidVarRep n ir' v')).
  Proof.
    intros v ev v' n ir HStep; revert n ir;
    remember WhileEnv as D; revert HeqD;
    induction HStep; intros; subst; eauto;
    match goal with
    | [ H : ValidVarRep _ _ _ |- _ ] => inversion H; subst; simpl; eauto
    end.

    - inversion HStep; eauto.
    - destruct e; try solve [destruct H; auto]; clear H.
      apply extChoiceInt_Sigma_step_inversion in HStep.
      destruct HStep as [? ?].
      inversion H; subst; eauto.
    - inversion HStep.
    - apply extChoiceInt_Tau_step_inversion in HStep.
      destruct HStep as [? [? ?]].
      inversion H0.
  Qed.

  Theorem write_updates_valid_var : forall v v' n ir ir',
       Step WhileEnv v (EvSigma (CEWrite n ir)) v'
    -> ValidVarRep n ir' v
    -> ValidVarRep n ir v'.
  Proof.
    intros.
    eapply ValidVar_step_inversion in H; eauto.
    destruct H.
    - destruct H.  inversion H.
    - destruct H.  
      + destruct H.  inversion H.
      + destruct H as [? [? ?]].  inversion H; subst; eauto.
  Qed.

  Theorem ValidMem_step : forall ev mem mem' n,
       Step WhileEnv mem ev mem'
    -> ValidMemRep n mem
    -> ValidMemRep n mem'.
  Proof.
    intros ev mem mem' n HStep. revert n.
    remember WhileEnv as D.  revert HeqD.
    induction HStep; intros; subst; eauto;
    match goal with
    | [ H : ValidMemRep _ _ |- _ ] => inversion H; subst; eauto
    end; try solve [match goal with
      | [ HStep : Step _ ?p _ ?p', HVVar : ValidVarRep _ _ ?p
         |- ValidMemRep _ (PGenPar ?p' _ _) ] =>
      destruct (ValidVar_step_inversion _ _ _ _ _ HStep HVVar)
            as [[? ?] | [[? ?] | [? [? ?]]]]; subst; eauto
    end].
  Qed.

  Fixpoint writeToMem (n : var) (i : IntRepr) (p : Proc) : Proc :=
    match p with
    | PGenPar (PFVar (VarState n' i')) s p' =>
      match nat_compare n n' with
      | Lt => PGenPar (PFVar (VarState n' i')) s (writeToMem n i p')
      | Eq => PGenPar (PFVar (VarState n' i)) s p'
      | Gt => PGenPar (PFVar (VarState n' i')) s p'
      end
    | PGenPar (PExtChoice (PPrefix (CERead n' i') _) _) s p' =>
      match nat_compare n n' with
      | Lt => PGenPar (VarImpl n' i') s (writeToMem n i p')
      | Eq => PGenPar (PFVar (VarState n' i)) s p'
      | Gt => PGenPar (VarImpl n' i') s p'
      end
    | p' => p'
    end.

  Definition updateMem (ev : Sigma) (p : Proc) : Proc :=
    match ev with
    | CERead _ _ => p
    | CEWrite x i => writeToMem x i p
    end.

  Theorem write_over_mem_id : forall n1 n2 ir mem,
       ValidMemRep n1 mem
    -> (n1 <= n2)%nat
    -> writeToMem n2 ir mem = mem.
  Proof.
    intros n1 n2 ir mem HValid.
    revert n2 ir.
    induction HValid; intros; eauto.
    inversion H; subst; simpl in *; eauto;
    remember (nat_compare n2 n) as ncmp;
    destruct ncmp; simpl; eauto; apply Logic.eq_sym in Heqncmp.

    + apply nat_compare_eq in Heqncmp. subst.
      omega. 
    + apply nat_compare_lt in Heqncmp.  omega.
    + apply nat_compare_eq in Heqncmp. subst. omega.
    + apply nat_compare_lt in Heqncmp.  omega.
  Qed.

  Theorem no_writing_to_small_mem : forall m m' n1 n2 ir,
      ValidMemRep n1 m
   -> (n1 <= n2)%nat
   -> Step WhileEnv m (EvSigma (CEWrite n2 ir)) m'
   -> False.
  Proof.           
    intros m m' n1 n2 ir HValidMem; revert m' n2 ir.
    induction HValidMem; intros m' n2 ir' HLE HFalse; eauto.
    inversion HFalse; subst; eauto.
    - inversion H; subst.  inversion H6 ; subst.
      unfold VarImpl in H6.  inversion H6; subst; eauto.  inversion H3.
      apply extChoiceInt_Sigma_step_inversion in H3.
      destruct H3.  inversion H0; subst.
      omega.
    - eapply IHHValidMem with (n2 := n2); eauto. omega.
  Qed.

  Theorem write_updates_valid_mem : forall v v' m m' n ir ir',
       Step WhileEnv
            (PGenPar v noEvents m)
            (EvSigma (CEWrite n ir))
            (PGenPar v' noEvents m')
    -> ValidMemRep n m
    -> ValidVarRep n ir' v
    -> (ValidVarRep n ir v' /\ m' = m).
  Proof.
    intros v v' m m' n ir ir' HStep HVMem HVVar.
    inversion HStep; subst; eauto using write_updates_valid_var.
    - apply no_writing_to_small_mem with (n1 := n) in H2; eauto.
  Qed.

  Theorem Forall_true : forall {A : Type} (P : Prop) (l : list A),
     P -> Forall (fun _ => P) l.
  Proof.
    induction l; eauto.
  Qed.

  Hint Resolve Forall_true.

  Theorem mem_may_be_written : forall nvar ir nfvs mem,
       ValidMemRep nfvs mem
    -> (nvar < nfvs)%nat
    -> exists evs, MStep WhileEnv mem evs (writeToMem nvar ir mem)
                /\ observableEvents evs = CEWrite nvar ir :: nil.
  Proof.
    intros nvar ir nfvs mem HVM; revert nvar ir; induction HVM; eauto;
    intros; match goal with
    | [ HLT : (_ < _)%nat |- _ ] => inversion HLT; subst
    end.

    - replace (writeToMem n ir0 (PGenPar v noEvents m))
         with (PGenPar (PFVar (VarState n ir0)) noEvents m)
           by (inversion H; subst; simpl;
               destruct (nat_compare_eq_iff n n) as [_ HNEq];
               rewrite HNEq; simpl; eauto).
      destruct (ValueInVar_may_be_written _ _ _ ir0 H) as [evs [? ?]];
      exists evs; split; eauto.
      apply MStep_GenPar_LeftSolo; eauto.
    - assert ((nvar < n) % nat) by omega.
      replace (writeToMem nvar ir0 (PGenPar v noEvents m))
         with (PGenPar v noEvents (writeToMem nvar ir0 m))
           by (inversion H; subst; simpl;
               destruct (nat_compare_lt nvar n) as [HNLt _];
               rewrite HNLt; eauto).
      destruct (IHHVM _ ir0 H1) as [evs [? ?]];
      exists evs; split; eauto.
      apply MStep_GenPar_RightSolo; eauto.
  Qed.

  Theorem stepped_mem_is_updated : forall n mem p ev,
       ValidMemRep n mem
    -> Step WhileEnv mem (EvSigma ev) p
    -> EquivMem n (updateMem ev mem) p.
  Proof.
    intros n mem p ev HValid.
    revert p ev.
    induction HValid;
      intros; eauto.

    inversion H0; subst; simpl; eauto.
    - inversion H; subst; try solve [inversion H7].
      unfold VarImpl in H7.
      inversion H7; subst.
      + inversion H4; subst; simpl; eauto.
      + apply extChoiceInt_Sigma_step_inversion in H4.
        destruct H4 as [ir' HStepPrefix].
        inversion HStepPrefix; subst.
        simpl.
        destruct (nat_compare_eq_iff n n) as [? HNEq].
        rewrite HNEq; simpl; eauto.

    - inversion H; subst; destruct ev; subst; simpl;
      apply IHHValid in H7; simpl in H7; eauto.
      + remember (nat_compare n0 n) as ncomp.
        destruct ncomp; simpl; eauto.
        * assert (n0 = n) by (eauto using nat_compare_eq).
          subst.
          constructor; eauto.
          eapply write_updates_valid_mem in H0; eauto.
          destruct H0 as [H01 H02]; inversion H01; subst; eauto.
          rewrite write_over_mem_id with (n1 := n) in H7; eauto.
        * constructor; eauto.
          rewrite write_over_mem_id with (n1 := n) in H7; eauto.
          apply Logic.eq_sym in Heqncomp.
          apply nat_compare_gt in Heqncomp.
          omega.
      + remember (nat_compare n0 n) as ncomp.
        destruct ncomp; simpl; eauto.
        * assert (n0 = n) by (eauto using nat_compare_eq).
          subst.
          constructor; eauto.
          eapply write_updates_valid_mem in H0; eauto.
          destruct H0 as [H01 H02]; inversion H01; subst; eauto.
          rewrite write_over_mem_id with (n1 := n) in H7; eauto.
        * constructor; eauto.
          rewrite write_over_mem_id with (n1 := n) in H7; eauto.
          apply Logic.eq_sym in Heqncomp.
          apply nat_compare_gt in Heqncomp.
          omega.
  Qed.

  Theorem tau_stepped_mem_is_not_updated : forall n mem p,
       ValidMemRep n mem
    -> Step WhileEnv mem EvTau p
    -> EquivMem n mem p.
  Proof.
    intros n mem p HValid; revert p; induction HValid; intros mem' HStep;
    eauto.

    inversion HStep; subst; eauto.
    constructor; eauto.
    eapply ValidVar_step_inversion in H5; eauto.
    destruct H5 as [ [? ?] | [ [? _] | [? [? _] ] ] ]; subst; eauto.
    inversion H0.  inversion H0.
  Qed.

  Hint Extern 1 => match goal with
    | [ H : (fvs_exp (?c ?e1 ?e2) <= ?n) % nat
        |- (fvs_exp ?e1 <= ?n) % nat ] =>
      try solve
        [apply (Le.le_trans _ (Peano.max (fvs_exp e1) (fvs_exp e2)));
               [apply Max.le_max_l | assumption]]
    | [ H : (fvs_exp (?c ?e1 ?e2) <= ?n) % nat
        |- (fvs_exp ?e2 <= ?n) % nat ] =>
      try solve
        [apply (Le.le_trans _ (Peano.max (fvs_exp e1) (fvs_exp e2)));
               [apply Max.le_max_r | assumption]]
    | [ H : (Peano.max ?n1 ?n2 <= ?n3)%nat |- (?n1 <= ?n3)%nat ] =>
      try solve [apply (Le.le_trans _ (Peano.max n1 n2));
                  [apply Max.le_max_l | assumption ] ]
    | [ H : (Peano.max ?n1 ?n2 <= ?n3)%nat |- (?n2 <= ?n3)%nat ] =>
      try solve [apply (Le.le_trans _ (Peano.max n1 n2));
                  [apply Max.le_max_r | assumption ] ]
  end.
    
  Theorem bound_lift_fun_commute : forall f n m,
      ApproxIntRepr (bound_Z (f n m))
                    (lift_Z_fun f (bound_Z n) (bound_Z m)).
  Proof.
    intros f n m.
    unfold bound_Z.
    destruct (Z_le_dec minInt (f n m)); simpl; eauto;
    destruct (Z_le_dec (f n m) maxInt); simpl; eauto;
    destruct (Z_le_dec minInt n); simpl; eauto;
    destruct (Z_le_dec n maxInt); simpl; eauto;
    destruct (Z_le_dec minInt m); simpl; eauto;
    destruct (Z_le_dec m maxInt); simpl; eauto;
    unfold bound_Z;
    destruct (Z_le_dec minInt (f n m)); simpl; eauto;
    destruct (Z_le_dec (f n m) maxInt); simpl; eauto;
    match goal with
    | [ H1 : ~ ?P, H2 : ?P |- _ ] => destruct H1; assumption
    end.
  Qed.

  Hint Resolve bound_lift_fun_commute.

  Theorem bound_lift_eq_true : forall n,
      ApproxIntRepr (bound_Z 1) (lift_Z_test eqb n n).
  Proof.
    intros n.
    unfold lift_Z_test.
    destruct n; simpl; eauto.
    rewrite eqb_refl; eauto.
  Qed.    

  Theorem bound_lift_eq_false : forall n m,
      n <> m
   -> ApproxIntRepr (bound_Z 0) (lift_Z_test eqb (bound_Z n) (bound_Z m)).
  Proof.
    intros n m HNeq.
    unfold lift_Z_test.
    unfold bound_Z.
    destruct (Z_le_dec minInt n); simpl; eauto;
    destruct (Z_le_dec n maxInt); simpl; eauto;
    destruct (Z_le_dec minInt m); simpl; eauto;
    destruct (Z_le_dec m maxInt); simpl; eauto.
    apply eqb_neq in HNeq.  rewrite HNeq.  eauto.
  Qed.    

  Hint Resolve bound_lift_eq_true bound_lift_eq_false.

  Theorem update_preserves_EquivMem : forall mem1 mem2 ev n,
       EquivMem n mem1 mem2
    -> EquivMem n (updateMem ev mem1) (updateMem ev mem2).
  Proof.
    intros mem1 mem2 ev n HEquiv.
    revert ev.
    induction HEquiv; intros ev.
    - destruct ev; eauto.
    - inversion H; subst; eauto.
      inversion H0; inversion H1; destruct ev; subst; simpl; eauto;
      destruct (nat_compare n2 n); eauto;
      constructor; eauto;
      exact (IHHEquiv (CEWrite n2 i)).
  Qed.
    
  Theorem write_preserves_ApproxMem : forall nfvs m1 m2 nvar ir1 ir2,
       ApproxMem nfvs m1 m2 
    -> ApproxIntRepr ir1 ir2
    -> ApproxMem nfvs (writeToMem nvar ir1 m1) (writeToMem nvar ir2 m2).
  Proof.
    intros nfvs m1 m2 nvar ir1 ir2 HAM; revert ir1 ir2 nvar;
    induction HAM; intros ir1 ir2 nvar HAIR; eauto.

    inversion H; subst.
    inversion H0; inversion H1; subst; simpl; eauto;
    match goal with
    | [ |- context[nat_compare ?n1 ?n2] ] =>
      destruct (nat_compare n1 n2); eauto
    end.
  Qed.

  Theorem write_preserves_EquivMem : forall nfvs m1 m2 nvar ir,
       EquivMem nfvs m1 m2 
    -> EquivMem nfvs (writeToMem nvar ir m1) (writeToMem nvar ir m2).
  Proof.
    intros nfvs m1 m2 nvar ir HEM;
    induction HEM; eauto.

    inversion H; subst.
    inversion H0; inversion H1; subst; simpl; eauto;
    match goal with
    | [ |- context[nat_compare ?n1 ?n2] ] =>
      destruct (nat_compare n1 n2); eauto
    end.
  Qed.                             

  Theorem update_preserves_ApproxMem : forall ev1 ev2 nfvs m1 m2,
       ApproxMem nfvs m1 m2 
    -> ApproxEvent ev1 ev2
    -> ApproxMem nfvs (updateMem ev1 m1) (updateMem ev2 m2).
  Proof.
    intros ev1 ev2 nfvs m1 m2 HAM; revert ev1 ev2;
    induction HAM; intros ev1 ev2 HAE; inversion HAE; subst; eauto.

    - simpl. eauto.
    - apply write_preserves_ApproxMem; eauto.
  Qed.

  Hint Resolve write_preserves_EquivMem update_preserves_EquivMem 
               write_preserves_ApproxMem update_preserves_ApproxMem.

  Theorem EquivVar_mirror_step : forall n v1 v2 c v1',
       EquivVar n v1 v2
    -> Step WhileEnv v1 (EvSigma c) v1'
    -> exists evs v2', MStep WhileEnv v2 evs v2'
                    /\ EquivVar n v1' v2'
                    /\ observableEvents evs = c :: nil.
  Proof.
    intros.
    inversion H; subst.
    assert (HStepOptions := ValidVar_step_inversion _ _ _ _ _ H0 H1).
    destruct HStepOptions as
        [[HEvEq ?] | [[HEvEq ?] | [ir' [HEvEq ?]]]];
    inversion HEvEq; subst; clear HEvEq.
    - destruct (ValueInVar_may_be_read _ _ _ H2) as [? [? ?]]; eauto 7.
    - destruct (ValueInVar_may_be_written _ _ _ ir' H2) as [? [? ?]]; eauto 7. 
  Qed.

  Theorem EquivMem_mirror_step : forall n mem1 mem2 c mem1',
       EquivMem n mem1 mem2
    -> Step WhileEnv mem1 (EvSigma c) mem1'
    -> exists evs mem2', MStep WhileEnv mem2 evs mem2'
                      /\ EquivMem n mem1' mem2'
                      /\ observableEvents evs = c :: nil.
  Proof.
    intros n mem1 mem2 c mem1' HEM;
    revert c mem1';
    induction HEM; intros; eauto.
    match goal with
    | [ HStep : Step _ _ _ _ |- _ ] => inversion HStep; subst
    end; eauto.

    - destruct (EquivVar_mirror_step _ _ _ _ _ H H7)
            as [evs [v2' [HStepv2 [HEV' Hobs]]]].
      exists evs; exists (PGenPar v2' noEvents m'); split; eauto.
      eauto using MStep_GenPar_LeftSolo.
    - apply IHHEM in H7.  clear IHHEM.
      destruct H7 as [evs [m2' [? [? ?]]]].
      exists evs; exists (PGenPar v' noEvents m2'); split; eauto.
      eauto using MStep_GenPar_RightSolo.
  Qed.
  
  Hint Extern 3 => 
    match goal with 
    | [ HAM : ApproxMem _ ?m1 ?m2,
        HEM1 : EquivMem _ ?m1' (writeToMem ?x ?i1 ?m1),
        HEM2 : EquivMem _ ?m2' (writeToMem ?x ?i2 ?m2)
       |- ApproxMem _ ?m1' ?m2' ] =>
      apply write_preserves_ApproxMem
       with (nvar := x) (ir1 := i1) (ir2 := i2)
         in HAM; [ | eauto ];
      apply EquivMem_sym in HEM1;
      apply EquivMem_sym in HEM2;
      let HAM1 := fresh HAM in
      let HAM2 := fresh HAM in 
      assert (HAM1 := ApproxMem_respects_EquivMem_left _ _ _ _ HAM HEM1);
      assert (HAM2 := ApproxMem_respects_EquivMem_right _ _ _ _ HAM1 HEM2);
      exact HAM2
    end.

  Theorem observableEvents_append : forall evs1 evs2,
      observableEvents (evs1 ++ evs2) 
    = observableEvents evs1 ++ observableEvents evs2.
  Proof.
    induction evs1; intros; simpl; eauto.
    destruct a; eauto.
    rewrite <- app_comm_cons.
    f_equal. eauto.
  Qed.

  Theorem OpSemTraces_trans : forall D p t1 t2 q,
       MStep D p t1 q
    -> OpSemTraces D q t2
    -> OpSemTraces D p (observableEvents t1 ++ t2).
  Proof.
    intros.  inversion H0. subst.
    rewrite <- observableEvents_append; eauto using MStep_trans.
  Qed.

  Theorem OpSemTraces_respects_EquivMem : forall n m1 m2 p t,
       EquivMem n m1 m2
    -> OpSemTraces WhileEnv (PGenPar p allEvents m1) t
    -> OpSemTraces WhileEnv (PGenPar p allEvents m2) t.
  Proof.
    intros n m1 m2 p t HEM HOST;
    generalize dependent m2; revert n;
    inversion HOST; subst; clear HOST.
    remember (PGenPar p allEvents m1) as pInMem.
    generalize dependent m1.  revert p.
    remember WhileEnv as D.  revert HeqD.

    induction H; intros; subst; eauto.
    inversion H; subst; auto.
    - destruct (EquivMem_mirror_step _ _ _ _ _ HEM H8)
            as [evs' [m2' [HMSm2 [HEM' HHobs]]]].
      replace (EvSigma c :: evs) with ((EvSigma c :: nil) ++ evs) by reflexivity.
      rewrite observableEvents_append.
      assert (exists evs3, SyncedInterleavings allEvents (EvSigma c :: nil) evs' evs3)
          by (eauto using allEvents_syncable).    
      destruct H1 as [evs3 HSI].
      assert (MStep WhileEnv (PGenPar p0 allEvents m2) evs3
                             (PGenPar p1' allEvents m2'))
          by (eauto using MStep_PGenPar_SI).
      rewrite (SI_all_observable_left _ _ _ HSI).
      apply OpSemTraces_trans with (q := PGenPar p1' allEvents m2'); eauto.
      
    - replace (EvTau :: evs) with ((EvTau :: nil) ++ evs) by auto. 
      rewrite observableEvents_append.
      apply OpSemTraces_trans with (q := PGenPar p1' allEvents m2); eauto.
      apply MStep_GenPar_LeftSolo; simpl; eauto.
    - apply (IHMStep Logic.eq_refl _ _ Logic.eq_refl n).
      eapply tau_stepped_mem_is_not_updated in H7;
          eauto using EquivMem_trans, EquivMem_sym.
  Qed.
  
  Inductive ValueInMem : nat -> Proc -> IntRepr -> Prop :=
  | VIMHere : forall n i v p',
         ValidVarRep n i v
      -> ValueInMem n (PGenPar v noEvents p') i
  | VIMThere : forall n n' v p' i i',
         ValueInMem n p' i
      -> ValidVarRep n' i' v
      -> ValueInMem n (PGenPar v noEvents p') i.
  Hint Constructors ValueInMem.

  Theorem mem_CERead_ValueInMem : forall n mem n' ir mem',
        ValidMemRep n mem
     -> Step WhileEnv mem (EvSigma (CERead n' ir)) mem'
     -> ValueInMem n' mem ir.
  Proof.
    intros n mem n' ir mem' HValid; revert n' ir mem';
    induction HValid; intros;
    match goal with
    | [ HStep : Step _ _ _ _ |- _ ] => inversion HStep; subst; eauto
    end.

    - match goal with
      | [ HStep : Step _ ?v _ _, HVV : ValidVarRep _ _ ?v |- _ ] =>
        destruct (ValidVar_step_inversion _ _ _ _ _ HStep HVV)
              as [ [HContra ?] | [ [ HVarEq ? ] | [? [HContra ?] ] ] ];
        [  inversion HContra
         | inversion HVarEq; subst; eauto
         | inversion HContra ]
      end.
  Qed.

  Theorem ValueInMem_respects_EquivMem : forall n mem1 mem2 nvar irvar,
       EquivMem n mem1 mem2
    -> (ValueInMem nvar mem1 irvar <-> ValueInMem nvar mem2 irvar).
  Proof.
    intros; split; intro HVIM;
    [ generalize dependent mem2 | generalize dependent mem1 ]; revert n;
    induction HVIM; intros; eauto;
    match goal with
    | [ HEM : EquivMem _ _ _ |- _ ] => inversion HEM; subst;
      match goal with
      | [ HEV : EquivVar _ _ _ |- _ ] => inversion HEV; subst;
        repeat (match goal with
        | [ HVV : ValidVarRep _ _ _ |- _ ] => inversion HVV; clear HVV; subst
        end); eauto
      end
    end.
  Qed.
      
  Theorem ValueInMem_may_be_read : forall n mem ir,
       ValueInMem n mem ir 
    -> exists evs,
           MStep WhileEnv mem evs mem
        /\ observableEvents evs = (CERead n ir :: nil).
  Proof.
    induction 1.
    - apply ValueInVar_may_be_read in H.
      destruct H as [ evs [? ?]]; exists evs; split; eauto using MStep_GenPar_LeftSolo.
    - destruct IHValueInMem as [evs [? ?]]; exists evs; split; eauto using MStep_GenPar_RightSolo.
  Qed.

  Theorem ValueInMem_respects_ApproxMem : forall nmem nvar m1 m2 ir,
       ApproxMem nmem m1 m2
    -> ValueInMem nvar m1 ir
    -> exists ir', ApproxIntRepr ir ir' /\ ValueInMem nvar m2 ir'.
  Proof.
    intros nmem nvar m1 m2 ir HAM; revert nvar ir;
    induction HAM; intros; eauto;
    match goal with
    | [ HVIM : ValueInMem _ _ _ |- _ ] => inversion HVIM; subst
    end.

    - inversion H; subst.
      inversion H5; subst; inversion H1; subst; inversion H2; subst; eauto.
    - destruct (IHHAM _ _ H4) as [ir' [HAIR HVIM]].
      exists ir'; inversion H; subst; eauto.
  Qed.


  Theorem traceInversion_PGenPar_allEvents : forall t D p1 p2,
       OpSemTraces D (PGenPar p1 allEvents p2) t
    -> (   OpSemTraces D p1 t
        /\ OpSemTraces D p2 t).
  Proof.
    inversion 1; subst.
    apply MStep_Inversion_PGenPar in H0.
    destruct H0 as [? [? [? [? [? [? [? ?]]]]]]]; subst; eauto.
    rewrite <- (SI_all_observable_right _ _ _ H3) at 2.
    rewrite <- (SI_all_observable_left _ _ _ H3).
    eauto.
  Qed.

  Theorem OpSemTraces_PGenPar_allEvents : forall t D p1 p2,
       OpSemTraces D p1 t
    -> OpSemTraces D p2 t
    -> OpSemTraces D (PGenPar p1 allEvents p2) t.
  Proof.
    intros t D p1 p2 HOST1 HOST2;
    inversion HOST1; subst; inversion HOST2; subst;
    clear HOST1 HOST2.
    apply Logic.eq_sym in H0.
    destruct (allEvents_syncable _ _ H0) as [? ?].
    rewrite (SI_all_observable_right _ _ _ H2).
    assert (HMS := MStep_PGenPar_SI _ _ _ _ _ _ _ _ _ H2 H H1).
    eauto.
  Qed.    
  
  Theorem OpSemTraces_PPrefix : forall D p t ev,
        OpSemTraces D p t
     -> OpSemTraces D (PPrefix ev p) (ev :: t).
  Proof.
    inversion 1; subst; eauto.
    replace (ev :: observableEvents evs)
       with (observableEvents (EvSigma ev :: evs))
         by auto.
    eauto.
  Qed.

  Theorem MStep_InMemory_extChoiceInt : forall D pChoice i mem evs q,
        MStep D (PGenPar (pChoice i) allEvents mem) evs q
     -> observableEvents evs <> nil
     -> MStep D (PGenPar (extChoiceInt pChoice) allEvents mem) evs q.
  Proof.
    intros.
    apply MStep_Inversion_PGenPar in H.
    destruct H as [evs1 [p1' [evs2 [p2' [HEq [HMS1 [HMS2 HSI]]]]]]].
    subst.
    rewrite <- (SI_all_observable_left _ _ _ HSI) in H0.
    eauto using MStep_PGenPar_SI, MStep_extChoiceInt.
  Qed.

  Theorem MStep_InMemory_PPrefix_CERead : forall p mem evs q n ir,
       MStep WhileEnv (PGenPar p allEvents mem) evs q
    -> ValueInMem n mem ir
    -> exists evshead,
            observableEvents evshead = CERead n ir :: nil
         /\ MStep WhileEnv
                  (PGenPar (PPrefix (CERead n ir) p) allEvents mem)
                  (evshead ++ evs)
                  q.
  Proof.
    intros.
    apply MStep_Inversion_PGenPar in H.
    destruct H as [ev1 [p1' [evs2 [mem' [HEq [HMS1' [HMS2' HSI]]]]]]].
    subst.

    apply ValueInMem_may_be_read in H0.
    destruct H0 as [evsheadMem [HMS2 HObsEq2]].
    assert (MStep WhileEnv (PPrefix (CERead n ir) p) (EvSigma (CERead n ir) :: nil) p)
        as HMS1
        by eauto.

    destruct (allEvents_syncable (EvSigma (CERead n ir) :: nil) evsheadMem)
          as [evshead HSIHead]; eauto.

    exists evshead. split.
    - rewrite <- (SI_all_observable_left _ _ _ HSIHead).
      simpl; eauto.
    - apply MStep_trans with (p2 := PGenPar p allEvents mem);
      eauto using MStep_PGenPar_SI.
  Qed.    
    
  Theorem OpSemTraces_InMemory_extChoiceInt : forall D pChoice t i mem,
        OpSemTraces D (PGenPar (pChoice i) allEvents mem) t
     -> OpSemTraces D (PGenPar (extChoiceInt pChoice) allEvents mem) t.
  Proof.
    intros;
    apply traceInversion_PGenPar_allEvents in H;
    destruct H;
    eauto using OpSemTraces_PGenPar_allEvents, OpSemTraces_extChoiceInt.
  Qed.

  Theorem OpSemTraces_InMemory_PPrefix_CERead : forall p mem t n ir,
       OpSemTraces WhileEnv (PGenPar p allEvents mem) t
    -> ValueInMem n mem ir
    -> OpSemTraces WhileEnv
                   (PGenPar (PPrefix (CERead n ir) p) allEvents mem)
                   (CERead n ir :: t).
  Proof.
    intros;
    apply traceInversion_PGenPar_allEvents in H; destruct H.
    apply OpSemTraces_PGenPar_allEvents; eauto using OpSemTraces_PPrefix.
    inversion H1; subst.
    destruct (ValueInMem_may_be_read _ _ _ H0) as [? [? ?]]; eauto.
    match goal with
    | [ HMS : MStep _ ?mem _ ?mem',
        HEq : _ = ?c :: nil
       |- OpSemTraces _ ?mem (?c :: observableEvents ?cs) ] =>
      replace (c :: observableEvents cs) 
         with ((c :: nil) ++ observableEvents cs)
           by auto;
      rewrite <- HEq;
      eapply OpSemTraces_trans; eauto
    end.
  Qed.

  Theorem traceInversion_InMemory_extChoiceInt : forall D fproc mem t,
       OpSemTraces D (PGenPar (extChoiceInt fproc) allEvents mem) t
    -> (forall ir p', Step D (fproc ir) EvTau p' -> False)
    -> exists ir, 
         OpSemTraces D (PGenPar (fproc ir) allEvents mem) t.
  Proof.
    intros. destruct t0; [ exists IRUnknown; eauto | ].
    inversion H; clear H.
    remember (PGenPar (extChoiceInt fproc) allEvents mem) as p.
    generalize dependent fproc. 
    generalize dependent c. revert mem t0.
    induction H2; intros; subst.
    - inversion H1.
    - destruct ev. 
      + inversion H1; subst; clear H1.  clear IHMStep.
        inversion H; subst; eauto.
        apply extChoiceInt_Sigma_step_inversion in H7.
        destruct H7 as [ir HStepFProc].
        exists ir.
        apply TStepsTo with (q := q).
        eapply MSStep.
        * apply SGenParSync; eauto.
        * eauto.
      + simpl in H1; subst. inversion H; subst.
        * apply extChoiceInt_Tau_step_inversion in H8.
          destruct H8 as [? [? HContra]].
          apply H0 in HContra.  auto.
        * destruct (IHMStep _ _ _ H1 _ H0 Logic.eq_refl) as [? ?].
          exists x; eauto.
          inversion H3; subst.
          simpl; rewrite <- H4. 
          replace (observableEvents evs0) with (observableEvents (EvTau :: evs0))
               by auto.
          apply TStepsTo with (q := q0). 
          eapply MSStep. 
          apply SGenParTau2; eauto.
          eauto.
  Qed.

  Theorem traceInversion_InMemory_PPrefix : forall ev p mem t n,
       OpSemTraces WhileEnv
         (PGenPar (PPrefix ev p) allEvents mem)
         t
    -> ValidMemRep n mem
    -> (   (t = nil)
        \/ (exists ttail, exists mem', exists evshead,
               (t = ev :: ttail)
            /\ MStep WhileEnv (PGenPar (PPrefix ev p) allEvents mem)
                              evshead
                              (PGenPar p allEvents mem')
            /\ observableEvents evshead = ev :: nil
            /\ (forall nvar irvar, ev = CERead nvar irvar -> ValueInMem nvar mem irvar)
            /\ EquivMem n (updateMem ev mem) mem'
            /\ OpSemTraces WhileEnv
                           (PGenPar p allEvents mem')
                           ttail)).
  Proof.
    intros ev p mem t n HTraces HValid.
    inversion HTraces.  clear HTraces.
    remember (PGenPar (PPrefix ev p) allEvents mem) as ppar;
    remember WhileEnv as D;
    revert HeqD Heqppar;
    revert HValid;
    revert mem ev n p.
    induction H; intros; subst; eauto.
    destruct ev.

    - right.
      match goal with
      | [ HStepGenPar : Step _ (PGenPar (PPrefix _ _) _ _) _ _
         |- _ ] => inversion HStepGenPar; subst; auto
      end;
      match goal with
      | [ HStepPrefix : Step _ (PPrefix _ _) (EvSigma _) _ 
         |- _ ] => inversion HStepPrefix; subst
      end;
      match goal with
      | [ HValid : ValidMemRep _ ?mem1,
          HMemStep : Step _ ?mem1 (EvSigma ?c) ?mem2            
         |- exists _ _ _, observableEvents (EvSigma ?c :: ?tail) = ?c :: _ /\ _ ] =>
        exists (observableEvents tail); exists mem2; exists (EvSigma c :: nil)
      end;
      repeat (split; intros; subst;
              eauto using stepped_mem_is_updated, mem_CERead_ValueInMem).
    - match goal with
      | [ HStepGenPar : Step _ (PGenPar (PPrefix _ _) _ _) _ _
         |- _ ] => inversion HStepGenPar; subst; auto
      end.
      + match goal with
        | [ HStepPrefix : Step _ (PPrefix _ _) EvTau _ |- _ ] =>
          inversion HStepPrefix
        end.
      + destruct (IHMStep Logic.eq_refl p2' ev0 n p0); eauto using ValidMem_step;
        clear IHMStep.
        right.  destruct H0 as [tIH [memIH [evsheadIH [? [? [? [? [? ?]]]]]]]].
        exists tIH, memIH, (EvTau :: evsheadIH).
        (repeat split);
        eauto 10 using EquivMem_trans, tau_stepped_mem_is_not_updated.

        intros.  subst.
        eapply tau_stepped_mem_is_not_updated in H6; eauto.
        assert (HVIM := H4 _ _ Logic.eq_refl).
        destruct (ValueInMem_respects_EquivMem _ _ _ nvar irvar H6); eauto.
  Qed.

  Theorem compile_exp_approx_refl : forall n e m1 m2 k1 k2,
        (fvs_exp e <= n)%nat
     -> ApproxMem n m1 m2
     -> (forall i1 i2 m1 m2,
             ApproxIntRepr i1 i2
          -> ApproxMem n m1 m2
          -> ApproxProc (k1 i1) m1 (k2 i2) m2)
     -> ApproxProc (compile_exp e k1) m1 (compile_exp e k2) m2.
  Proof.
    intros nfvs e; induction e; intros m1 m2 k1 k2 Hfvs HAM HAP; eauto.
    - simpl.
      unfold ApproxProc. intros.

      apply traceInversion_InMemory_extChoiceInt in H;
        [ | intros ? ? HContra; inversion HContra ].
      destruct H as [ir HOST].
      apply traceInversion_InMemory_PPrefix with (n := nfvs) in HOST; auto.
      destruct HOST; [ subst; eauto | ].
      destruct H as [ttail [mem' [evshead [HEq [HMStep [HObs [HVIM' [HEM HOST]]]]]]]]; subst.
      assert (HVIM := HVIM' _ _ Logic.eq_refl); clear HVIM'.
      simpl in *.
                      
      destruct (ValueInMem_respects_ApproxMem _ _ _ _ _ HAM HVIM)
            as [ir' [HAIR HVIM']].

      assert (HAProc := HAP _ _ _ _ HAIR HAM); clear HAP.
      unfold ApproxProc in HAProc.

      eapply OpSemTraces_respects_EquivMem with (m2 := m1) in HOST; eauto.

      apply HAProc in HOST; clear HAProc.
      destruct HOST as [ttail' [HAT HOST]].
      
      exists (CERead n ir' :: ttail').
      split; eauto.

      apply OpSemTraces_InMemory_extChoiceInt with (i := ir').
      apply OpSemTraces_InMemory_PPrefix_CERead; eauto.
  Qed.
  
  (* This is a strengthened version of the previous theorem, in that it requires
     less knowledge about k1 and k2 (in particular, they need only approximate each
     other for some finite number of events. 

     We need it to prove compile_approx_refl, for commands, where only the
     strengthened version goes through directly.
  *)

  Theorem MStepInversion_InMemory_extChoiceInt : forall D fproc mem evs q,
       MStep D (PGenPar (extChoiceInt fproc) allEvents mem) evs q
    -> (forall ir p', Step D (fproc ir) EvTau p' -> False)
    -> (   observableEvents evs = nil
        \/ exists ir,
              MStep D (PGenPar (fproc ir) allEvents mem) evs q).
  Proof.
    intros D fproc mem evs q HMS HNotTau.
    remember (PGenPar (extChoiceInt fproc) allEvents mem) as p.
    generalize dependent fproc. revert mem.
    induction HMS; intros mem fproc HEq HNotNil; subst; eauto.

    inversion H; subst; eauto.
    - right. inversion H; subst; clear H; eauto.
      apply extChoiceInt_Sigma_step_inversion in H9.
      destruct H9 as [ir HStepFProc].
      exists ir.
      eapply MSStep.
        * apply SGenParSync; eauto.
        * eauto.
    - apply extChoiceInt_Tau_step_inversion in H6.
      destruct H6 as [? [? ?]].
      edestruct HNotNil; eauto.
    - destruct (IHHMS _ _ Logic.eq_refl HNotNil) as [? | [ir ?]]; simpl; eauto.
      right. exists ir.
      apply MSStep with (p' := PGenPar (fproc ir) allEvents p2'); eauto.
  Qed.

  Theorem MStepInversion_InMemory_PPrefix : forall nfvs ev p mem evs q,
       MStep WhileEnv (PGenPar (PPrefix ev p) allEvents mem) evs q
    -> ValidMemRep nfvs mem
    -> (   (observableEvents evs = nil)
        \/ (exists evshead, exists evstail, exists mem',
               evs = evshead ++ evstail
            /\ observableEvents evshead = ev :: nil
            /\ MStep WhileEnv (PGenPar (PPrefix ev p) allEvents mem)
                              evshead
                              (PGenPar p allEvents mem')
            /\ (forall nvar irvar, ev = CERead nvar irvar -> ValueInMem nvar mem irvar)
            /\ EquivMem nfvs (updateMem ev mem) mem'
            /\ MStep WhileEnv (PGenPar p allEvents mem') evstail q)).
  Proof.
    intros nfvs ev p mem evs q HMS.
    remember (PGenPar (PPrefix ev p) allEvents mem) as ppar;
    remember WhileEnv as D; revert HeqD Heqppar.
    revert ev p mem.
    induction HMS; intros pev ptail mem HEq1 HEq2 HVM; subst; eauto.
    inversion H; subst; eauto.

    - inversion H4; subst. right.
      exists (EvSigma c :: nil); exists evs; exists p2'.
      repeat split; eauto.
      + intros; subst.  eauto using mem_CERead_ValueInMem. 
      + eauto using stepped_mem_is_updated.
    - inversion H6.
    - assert (HEM := tau_stepped_mem_is_not_updated _ _ _ HVM H6).
      destruct (IHHMS _ _ _ Logic.eq_refl Logic.eq_refl)
            as [? | [evshead [evstail [mem' [? [? [? [? [? ?]]]]]]]]];
        subst; eauto.
      right. exists (EvTau :: evshead); exists evstail; exists mem'.
      repeat split; eauto.
      + intros; subst. simpl in H4.
        destruct (ValueInMem_respects_EquivMem _ _ _ nvar irvar HEM); eauto.
      + eauto using EquivMem_trans.
  Qed.

  Theorem ApproxProcN_CERead_cong : forall nfvs n nlen m1 m2 k1 k2,
       (n < nfvs)%nat
    -> ApproxMem nfvs m1 m2
    -> (forall i1 i2 m1 m2,
            ApproxIntRepr i1 i2
         -> ApproxMem nfvs m1 m2
         -> ApproxProcN nlen (k1 i1) m1 (k2 i2) m2)
    -> ApproxProcN nlen
         (extChoiceInt (fun v => PPrefix (CERead n v) (k1 v))) m1
         (extChoiceInt (fun v => PPrefix (CERead n v) (k2 v))) m2.
  Proof.
    unfold ApproxProcN.
    intros nfvs n nlen m1 m2 k1 k2 HFVS HAM HAPCont evs q HLen HMS.

    destruct (MStepInversion_InMemory_extChoiceInt _ _ _ _ _ HMS)
          as [ ? | [ ir HMS' ] ]. 
    - intros ? ? HContra; inversion HContra.
    - rewrite H; exists nil; simpl; eauto.
    - destruct (MStepInversion_InMemory_PPrefix nfvs _ _ _ _ _ HMS')
        as [? | [evshead [evstail [mem' [HEq1 [HEq2
                    [HMSHead [HVIM [HEM HMSTail]]]]]]]]]; eauto.
      + rewrite H. exists nil. eauto.
      + subst. simpl in *.
        destruct (ValueInMem_respects_ApproxMem _ _ _ _ _
                       HAM (HVIM _ _ Logic.eq_refl))
              as [ir' [HAIR HVIM']].
        assert (ApproxMem nfvs mem' m2) as HAM'
          by (eauto using ApproxMem_respects_EquivMem_left).
        assert ((length evstail <= nlen)%nat) as HLenTail
          by (rewrite app_length in HLen; omega).
        destruct (HAPCont _ _ _ _ HAIR HAM' _ _ HLenTail HMSTail)
              as [evstail' [q' [HAT HMSTail']]].
        clear HAPCont.

        assert (HPrefix := MStep_InMemory_PPrefix_CERead _ _ _ _ _ _
                                                         HMSTail' HVIM').
        destruct HPrefix as [evshead' [HObsHead HMSPrefix']].
        exists (evshead' ++ evstail'); exists q'; split.
        * repeat (rewrite observableEvents_append); eauto.
          apply ApproxTrace_append; eauto.
          rewrite HObsHead; eauto.
          rewrite HEq2; eauto.
        * apply MStep_InMemory_extChoiceInt with (i := ir'); eauto.
          rewrite observableEvents_append.
          rewrite HObsHead.
          simpl. intros HContra. inversion HContra.
  Qed.

  Theorem ApproxProcN_Cong_PPrefix_CEWrite : forall nlen nfvs nvar ir1 ir2 k1 k2 m1 m2,
       ApproxIntRepr ir1 ir2
    -> ApproxMem nfvs m1 m2
    -> (nvar < nfvs)% nat
    -> (forall m1' m2',
             EquivMem nfvs m1' (writeToMem nvar ir1 m1)
          -> EquivMem nfvs m2' (writeToMem nvar ir2 m2)
          -> ApproxProcN nlen k1 m1' k2 m2')
    -> ApproxProcN nlen (PPrefix (CEWrite nvar ir1) k1) m1 
                        (PPrefix (CEWrite nvar ir2) k2) m2.
  Proof.
    intros nlen nfvs nvar ir1 ir2 k1 k2 m1 m2 HAIR HAM HFvs HAP.
    unfold ApproxProcN in *. intros evs q HLen HMS.
    eapply MStepInversion_InMemory_PPrefix in HMS; eauto.
    destruct HMS as [? | [evshead [evstail [m1'
                             [HEq1 [HEq2 [HMSHead [HVIM [HEM HMSTail]]]]]]]]].

    - rewrite H; exists nil; eauto.
    - subst.
      apply HAP with (m2' := writeToMem nvar ir2 m2) in HMSTail; eauto.
      + destruct HMSTail as [evstail' [q' [HAT' HMS2']]].
        destruct (mem_may_be_written nvar ir2 nfvs m2) 
          as [evsMem [? ?]]; eauto.
        destruct (allEvents_syncable (EvSigma (CEWrite nvar ir2) :: nil)
                                     evsMem)
          as [evshead' HSI]; eauto.
        exists (evshead' ++ evstail'). exists q'. split.
        * repeat (rewrite observableEvents_append).
          rewrite HEq2.
          rewrite <- (SI_all_observable_left _ _ _ HSI).
          simpl.  eauto.
        * apply MStep_trans with (p2 := PGenPar k2 allEvents (writeToMem nvar ir2 m2));
            eauto.
          eapply MStep_PGenPar_SI; eauto.
      + rewrite app_length in HLen. omega.
  Qed.

  Theorem ApproxProc_Cong_PPrefix_CEWrite : forall nfvs nvar ir1 ir2 k1 k2 m1 m2,
       ApproxIntRepr ir1 ir2
    -> ApproxMem nfvs m1 m2
    -> (nvar < nfvs)% nat
    -> (forall m1' m2',
             EquivMem nfvs m1' (writeToMem nvar ir1 m1)
          -> EquivMem nfvs m2' (writeToMem nvar ir2 m2)
          -> ApproxProc k1 m1' k2 m2')
    -> ApproxProc (PPrefix (CEWrite nvar ir1) k1) m1 
                  (PPrefix (CEWrite nvar ir2) k2) m2.
  Proof.
    intros. apply ApproxProcN_ApproxProc.
    intros.
    apply (ApproxProcN_Cong_PPrefix_CEWrite _ nfvs); 
    eauto using ApproxProc_ApproxProcN.
  Qed.


  Theorem compile_exp_approx_refl_strengthened : forall nfvs e nlen m1 m2 k1 k2,
        (fvs_exp e <= nfvs)%nat
     -> ApproxMem nfvs m1 m2
     -> (forall i1 i2 m1 m2 ,
             ApproxIntRepr i1 i2
          -> ApproxMem nfvs m1 m2
          -> ApproxProcN nlen (k1 i1) m1 (k2 i2) m2)
     -> ApproxProcN nlen (compile_exp e k1) m1 (compile_exp e k2) m2.
  Proof.
      intros nfvs e; induction e;
      intros nlen m1 m2 k1 k2 HFvs HAM HAPCont; eauto.

      subst; simpl in *.
      apply (ApproxProcN_CERead_cong nfvs); eauto.
  Qed.

  Hint Extern 2 => match goal with
  | [ H : ApproxMem ?nfvs ?m1 ?m2 |- ApproxProc _ ?m1 _ ?m2 ] => 
    apply compile_exp_approx_refl with (n := nfvs)
  end.

  Theorem compile_exp_respects_nil_step : forall n e st e' m1 m2 k1 k2,
       e / st ==a>[ None ] e'
    -> (fvs_exp e <= n)%nat
    -> ApproxMem n m1 m2
    -> (forall i1 i2 m1 m2,
             ApproxIntRepr i1 i2
          -> ApproxMem n m1 m2
          -> ApproxProc (k1 i1) m1 (k2 i2) m2)
    -> ApproxProc (compile_exp e' k1) m1 (compile_exp e k2) m2.
  Proof.
    intros nfvs e st e' m1 m2 k1 k2 HStep; revert m1 m2 k1 k2;
    remember None as wopt; revert Heqwopt;
    induction HStep; intros Heqwopt m1 m2 k1 k2 Hfvs HAM HAP; simpl; subst; eauto;
    try solve [inversion Heqwopt];
    eapply HAP; eauto;
    try match goal with
    | [ |- ApproxIntRepr (bound_Z _)
                         (lift_Z_test _ (bound_Z ?n) (bound_Z ?m)) ] =>
      unfold bound_Z at 2 3;
      destruct (Z_le_dec minInt n);
      destruct (Z_le_dec n maxInt);
      destruct (Z_le_dec minInt m);
      destruct (Z_le_dec m maxInt); eauto;
      simpl;
      try (rewrite leb_compare; destruct (n ?= m); simpl; eauto;
      match goal with
      | [ HContra : ?x <> ?x |- _ ] => destruct HContra; reflexivity
      | [ HContra : Eq = Gt |- _ ] => inversion HContra
      | [ HContra : Lt = Gt |- _ ] => inversion HContra
      end)
    | [ |- ApproxIntRepr (bound_Z _) (lift_Z_not (bound_Z ?n)) ] =>
      unfold bound_Z at 2;
      destruct (Z_le_dec minInt n);
      destruct (Z_le_dec n maxInt); eauto;
      simpl; destruct n; simpl in *; eauto;
      match goal with
      | [ HContra : ?x <> ?x |- _ ] => destruct HContra; reflexivity
      end
    end.
    - destruct n; destruct m; simpl in *; eauto.
      destruct H as [HContra | HContra]; destruct HContra; reflexivity.
    - destruct n; destruct m; simpl in *; eauto;
      destruct H as [HContra | HContra]; inversion HContra.
    - destruct n; destruct m; simpl in *; eauto;
      try match goal with
      | [ HContra : ?x <> ?x |- _ ] => destruct HContra; reflexivity
      end.
  Qed.

  Theorem ApproxProcN_Tau_right : forall nlen p1 m1 p2 m2 p2',
         ApproxProcN nlen p1 m1 p2' m2
      -> Step WhileEnv p2 EvTau p2'
      -> ApproxProcN nlen p1 m1 p2 m2.
  Proof.
    unfold ApproxProcN; intros.
    apply H in H2; eauto.
    destruct H2 as [evs' [q' [? ?]]].
    exists (EvTau :: evs'). exists q'. simpl; split; eauto.
    apply MSStep with (p' := PGenPar p2' allEvents m2); eauto.
  Qed.

  Theorem ApproxProc_Tau_right : forall p1 m1 p2 m2 p2',
         ApproxProc p1 m1 p2' m2
      -> Step WhileEnv p2 EvTau p2'
      -> ApproxProc p1 m1 p2 m2.
  Proof.
    unfold ApproxProc; intros.
    apply H in H1; eauto.
    destruct H1 as [t' [? ?]].
    exists t'. simpl; split; eauto.
    inversion H2; subst.
    replace (observableEvents evs)
       with (observableEvents (EvTau :: evs)) by reflexivity.
    apply TStepsTo with (q := q).
    apply MSStep with (p' := PGenPar p2' allEvents m2); eauto.
  Qed.

  Theorem ApproxProcN_Tau_left : forall nfvs nlen p1 m1 p2 m2,
       ApproxMem nfvs m1 m2
    -> (forall p1' ev m1 m2,
             Step WhileEnv p1 ev p1'
          -> ApproxMem nfvs m1 m2
          -> ev = EvTau /\ ApproxProcN nlen p1' m1 p2 m2)
    -> ApproxProcN (S nlen) p1 m1 p2 m2.
  Proof.
    unfold ApproxProcN; intros nfvs nlen p1 m1 p2 m2 HAM HAP evs q HLen HMS.
    remember (PGenPar p1 allEvents m1) as p.
    remember WhileEnv as D.
    revert Heqp HeqD.  revert HAM. revert HAP. revert p1 m1.
    revert p2 m2.
    induction HMS; subst; eauto.  intros; subst.
    inversion H; subst; simpl in *; eauto.
    - apply (HAP _ _ m1 m2) in H4; eauto.
      destruct H4 as [HContra ?]; inversion HContra.
    - apply (HAP _ _ m1 m2) in H6; eauto. destruct H6 as [_ ?].
      apply H0 with (q := q); eauto; omega.
    - assert ((length evs <= S nlen)%nat) by omega.
      apply (IHHMS H0 _ _ p1 p2'); eauto.
      eapply tau_stepped_mem_is_not_updated in H6; eauto.
      apply ApproxMem_respects_EquivMem_left with (m1 := m1); eauto.
  Qed.

  Theorem ApproxProcN_Cong_PIntChoice : forall nfvs nlen p1 p1' p2 p2' m1 m2,
         (forall m1 m2, ApproxMem nfvs m1 m2
                     -> ApproxProcN nlen p1 m1 p2 m2)
      -> (forall m1 m2, ApproxMem nfvs m1 m2
                        -> ApproxProcN nlen p1' m1 p2' m2)
      -> ApproxMem nfvs m1 m2
      -> ApproxProcN nlen (PIntChoice p1 p1') m1 (PIntChoice p2 p2') m2.
  Proof.
    unfold ApproxProcN. 
    intros nfvs nlen p1 p1' p2 p2' m1 m2 HAP1 HAP2 HAM evs q HLen HMS.
    
    remember (PGenPar (PIntChoice p1 p1') allEvents m1) as p.
    remember WhileEnv as D.
    revert HeqD; generalize dependent m1.

    induction HMS; intros; subst; eauto.
    inversion H; subst; eauto.

    - match goal with
      | [ H : Step _ (PIntChoice _ _) (EvSigma _) _ |- _ ] => inversion H
      end.
    - match goal with
      | [ H : Step _ (PIntChoice _ _) EvTau _ |- _ ] =>
        inversion H; subst; simpl in *
      end;
      match goal with
      | [ HAP : forall _ _, ApproxMem _ _ _ -> forall _ _, _ 
                   -> MStep _ (PGenPar ?p _ _) _ _ -> _,
          HS : MStep _ (PGenPar ?p _ _) _ _,
          HAM : ApproxMem _ _ _ |- _ ] =>
        apply (HAP _ _ HAM) in HS; clear HAP; eauto; try omega;
        destruct HS as [evs' [q' [HAT' HMS']]];
        exists (EvTau :: evs'); exists q'; simpl; split; eauto;
        eapply MSStep; eauto; eapply SGenParTau1; eauto
      end.
    - apply IHHMS with (m1 := p2'0); simpl in *; eauto; try omega.
      eapply tau_stepped_mem_is_not_updated in H6;
      eauto using ApproxMem_respects_EquivMem_left.
  Qed.      

  Theorem ApproxProc_Cong_PIntChoice : forall nfvs p1 p1' p2 p2' m1 m2,
         (forall m1 m2, ApproxMem nfvs m1 m2
                     -> ApproxProc p1 m1 p2 m2)
      -> (forall m1 m2, ApproxMem nfvs m1 m2
                     -> ApproxProc p1' m1 p2' m2)
      -> ApproxMem nfvs m1 m2
      -> ApproxProc (PIntChoice p1 p1') m1 (PIntChoice p2 p2') m2.
  Proof.
    intros.
    apply ApproxProcN_ApproxProc.
    intros.
    
    apply (ApproxProcN_Cong_PIntChoice nfvs); eauto using ApproxProc_ApproxProcN.
  Qed.

  Theorem ApproxProcN_Cong_PMu : forall nfvs nlen p1 m1 p2 m2,
       ApproxMem nfvs m1 m2
    -> (forall m1 m2, ApproxMem nfvs m1 m2
                   -> ApproxProcN nlen ({0 ~> PMu p1} p1) m1 ({0 ~> PMu p2} p2) m2)
    -> ApproxProcN (S nlen) (PMu p1) m1 (PMu p2) m2.
  Proof.
    intros.
    apply ApproxProcN_Tau_right with (p2' := {0 ~> PMu p2} p2); eauto.
    apply (ApproxProcN_Tau_left nfvs); eauto.
    intros.  inversion H1; subst; eauto.
  Qed.

  Theorem compile_exp_extensional : forall e k1 k2,
        (forall ir, k1 ir = k2 ir)
     -> compile_exp e k1 = compile_exp e k2.
  Proof.
    induction e; intros; eauto.
    - simpl. apply extChoiceInt_extensional; intros; f_equal; eauto.
  Qed.
      
  Theorem open_compile_exp : forall u e n k,
      {n ~> u} (compile_exp e k) = compile_exp e (fun ir => {n ~> u} (k ir)).
  Proof.
    induction e; intros; try solve [simpl in *; eauto;
      repeat (match goal with
      | [ IH : forall _ _, {_ ~> _} (compile_exp ?e _) = _
         |- {_ ~>_} (compile_exp ?e _) = _ ] =>
        rewrite IH; simpl; eauto
      | [ |- compile_exp ?e _ = compile_exp ?e _ ] =>
        apply compile_exp_extensional; intros; simpl; eauto
      end)].

    - replace (compile_exp (EVar n) k)
         with (extChoiceInt (fun v => PPrefix (CERead n v) (k v))) by eauto.
      rewrite open_extChoiceInt. simpl.  eauto.
  Qed.

  Theorem open_compile : forall c u n k,
      {n ~> u} (compile c k) = compile c ({n ~> u} k).
  Proof.
    induction c; intros; try solve [simpl in *; eauto;
      repeat (match goal with
      | [ IH : forall _ _ _, {_ ~> _} (compile ?c _) = _
         |- context[{_ ~> _} (compile ?c _)] ] =>
        rewrite IH; simpl; eauto
      | [ |- {_ ~> _} (compile_exp ?e _) = compile_exp ?e _ ] =>
        rewrite open_compile_exp; simpl;
        apply compile_exp_extensional; intros; simpl; eauto
      end)].

    - simpl in *.
      rewrite open_compile_exp.
      apply compile_exp_extensional. 
      intros. 
      destruct ir; simpl; eauto.
      + destruct (k0 =? 0); eauto.
      + f_equal; eauto.

    - simpl.
      f_equal.
      rewrite open_compile_exp; apply compile_exp_extensional; intros.
      destruct ir; eauto.
      + destruct (k0 =? 0).
        * rewrite open_lift_commute; eauto; try omega.
        * rewrite IHc. simpl. eauto.
      + simpl.  f_equal.
        * rewrite IHc.  eauto.
        * rewrite open_lift_commute; eauto; try omega.
  Qed.
  
  Theorem ApproxProcN_0 : forall p1 m1 p2 m2,
      ApproxProcN 0 p1 m1 p2 m2.
  Proof.
    unfold ApproxProcN; intros.
    inversion H0; subst; eauto.
    simpl in H; omega.
  Qed.
  Hint Resolve ApproxProcN_0.

  Theorem downward_closure : forall n m p1 m1 p2 m2,
        ApproxProcN n p1 m1 p2 m2
     -> (m <= n)%nat
     -> ApproxProcN m p1 m1 p2 m2.
  Proof.
    unfold ApproxProcN; intros.
    eapply H; eauto.
    omega.
  Qed.

  (* For convenience/clarity, Here I state the version of the theorem we're
     actually going to prove.  That is, this statement is set up already to
     provide the generalized IH.  There are three key differences vs the pretty
     version.

     1) We've explicitly named the nat we're going to do strong induction on.

     2) We've weakened the assumption about the continuations to talk only about
        traces of a particular length. 

     3) We've unfolded the definition of ApproxProc, to avoid having to do that
        repeatedly. *)
  Theorem compile_cmd_approx_refl_strengthened : forall nfvs nlen c m1 m2 k1 k2,
        (fvs_cmd c <= nfvs)%nat
     -> ApproxMem nfvs m1 m2
     -> (forall m1 m2, 
                 ApproxMem nfvs m1 m2 
                 -> ApproxProcN nlen k1 m1 k2 m2)
     -> ApproxProcN nlen (compile c k1) m1 (compile c k2) m2.
  Proof.
    intros nfvs; induction nlen using lt_wf_ind;
    induction c; intros m1 m2 k1 k2 HFvs HAM HAPCont; simpl in *; eauto.
    
    - apply (compile_exp_approx_refl_strengthened nfvs); eauto.
      intros.
      apply (ApproxProcN_Cong_PPrefix_CEWrite) with (nfvs := nfvs); eauto.
    - apply (compile_exp_approx_refl_strengthened nfvs); eauto.
      intros. apply Max.max_lub_r in HFvs.
      inversion H0; subst.
      + destruct (n =? 0); eauto.
      + destruct i1.
        * destruct (k =? 0); eauto using ApproxProcN_Tau_right. 
        * apply (ApproxProcN_Cong_PIntChoice nfvs); eauto.
    - destruct nlen; eauto.
      apply (ApproxProcN_Cong_PMu nfvs); eauto.
      intros.
      repeat (rewrite open_compile_exp).
      apply (compile_exp_approx_refl_strengthened nfvs); eauto.
      intros.
      inversion H1; subst.
      + destruct (n =? 0).
        * repeat (rewrite open_under_lift).
          apply downward_closure with (n := S nlen); eauto.
        * repeat (rewrite open_compile); eauto.
          simpl.
          apply H; eauto.  intros.
          apply H with (c := CWhile e c); eauto.
          intros. 
          apply downward_closure with (n := S nlen); eauto.
      + simpl.  destruct i1.  
        * destruct (k =? 0).
          -- repeat (rewrite open_under_lift).
             rewrite open_compile. simpl.
             match goal with
             | [ |- ApproxProcN _ _ _ (PIntChoice ?a ?b) _ ] =>
               apply ApproxProcN_Tau_right with (p2' := b)
             end; eauto.
             apply downward_closure with (n := S nlen); eauto.
          -- match goal with
             | [ |- ApproxProcN _ _ _ (PIntChoice ?a ?b) _ ] =>
               apply ApproxProcN_Tau_right with (p2' := a)
             end; eauto.
             repeat (rewrite open_compile).
             apply H; eauto. intros. 
             simpl. apply H with (c := CWhile e c); eauto.
             intros; apply downward_closure with (n := S nlen); eauto.
          
        * simpl.  apply (ApproxProcN_Cong_PIntChoice nfvs); intros; eauto.
          -- repeat (rewrite open_compile).
             simpl. apply H; eauto. intros.
             apply H with (c := CWhile e c); eauto.
             intros. apply downward_closure with (n := S nlen); eauto.

          -- repeat (rewrite open_under_lift).
             apply downward_closure with (n := S nlen); eauto.
  Qed.

  Theorem compile_cmd_approx_refl : forall nfvs c m1 m2 k1 k2,
        (fvs_cmd c <= nfvs)%nat
     -> ApproxMem nfvs m1 m2
     -> (forall m1 m2, ApproxMem nfvs m1 m2 -> ApproxProc k1 m1 k2 m2)
     -> ApproxProc (compile c k1) m1 (compile c k2) m2.
  Proof.
    intros; unfold ApproxProc; intros.
    inversion H2. subst.
    apply (compile_cmd_approx_refl_strengthened nfvs (length evs) _ _ m2 _ k2) in H3;
      eauto using ApproxProc_ApproxProcN.
    destruct H3 as [? [? [? ?]]].  eauto.
  Qed.

  Theorem compile_cmd_respects_nil_step : forall n c st c' st' m1 m2 k1 k2,
       c / st ==>[ None ] c' / st'
    -> (fvs_cmd c <= n)%nat
    -> ApproxMem n m1 m2
    -> (forall m1 m2, ApproxMem n m1 m2 -> ApproxProc k1 m1 k2 m2)
    -> ApproxProc (compile c' k1) m1 (compile c k2) m2.
  Proof.
    intros nfvs c st c' st' m1 m2 k1 k2 HStep; revert m1 m2 k1 k2;
    remember None as wopt; revert Heqwopt;
    induction HStep; intros Heqwopt m1 m2 k1 k2 Hfvs HMA HRI; subst;
    try solve [ simpl; inversion Heqwopt].

    - simpl in *.
      eapply (compile_exp_respects_nil_step nfvs); eauto.  
      intros; eauto.
      apply (ApproxProc_Cong_PPrefix_CEWrite nfvs); eauto.

    - simpl in *. apply IHHStep; eauto.
      intros.  apply (compile_cmd_approx_refl nfvs); eauto.

    - simpl in *. apply (compile_cmd_approx_refl nfvs); eauto.

    - simpl in *.
      eapply (compile_exp_respects_nil_step nfvs); intros; eauto.
      apply Max.max_lub_r in Hfvs.
      inversion H0; subst; eauto.
      + destruct (n =? 0); 
        apply (compile_cmd_approx_refl nfvs); eauto. 
      + destruct i1; subst.
        * destruct (k =? 0); eauto.
          -- apply ApproxProc_Tau_right with (p2' := compile c3 k2);
             eauto using (compile_cmd_approx_refl nfvs).
          -- apply ApproxProc_Tau_right with (p2' := compile c2 k2);
             eauto using (compile_cmd_approx_refl nfvs).
        * apply (ApproxProc_Cong_PIntChoice nfvs);
             eauto using (compile_cmd_approx_refl nfvs).
          
    - simpl in *.
      unfold bound_Z.
      apply Max.max_lub_r in Hfvs.
      destruct (Z_le_dec minInt 0).
      destruct (Z_le_dec 0 maxInt).
      + simpl.
        apply (compile_cmd_approx_refl nfvs); eauto.
      + destruct (n max_ge_0).
      + destruct (n min_le_0).

    - simpl in *.
      unfold bound_Z.
      destruct (Z_le_dec minInt n).
      destruct (Z_le_dec n maxInt).
      + apply eqb_neq in H.
        rewrite H.
        apply (compile_cmd_approx_refl nfvs); eauto.
      + apply ApproxProc_Tau_right with (p2' := compile c2 k2); eauto.
        apply (compile_cmd_approx_refl nfvs); eauto.
      + apply ApproxProc_Tau_right with (p2' := compile c2 k2); eauto.
        apply (compile_cmd_approx_refl nfvs); eauto.

    - simpl in *.
      match goal with
      | [ |- ApproxProc _ _ (PMu ?p) _ ] => 
        apply ApproxProc_Tau_right with (p2' := {0 ~> PMu p} p)
      end; eauto.
      rewrite open_compile_exp.
      apply (compile_exp_approx_refl nfvs); intros; eauto.
      inversion H; subst.
      + remember (n =? 0) as neq.
        destruct neq; subst.
        * rewrite open_under_lift.  eauto.
        * rewrite open_compile. simpl.
          apply (compile_cmd_approx_refl nfvs); intros; eauto.
          apply (compile_cmd_approx_refl nfvs (WHILE c1 DO c2 END)); intros; eauto.
      + destruct i1.
        * remember (k =? 0) as neq; destruct neq; subst.
          -- simpl. rewrite open_under_lift.
             apply ApproxProc_Tau_right with (p2' := k2); eauto.
          -- simpl. rewrite open_compile; simpl.
             eapply ApproxProc_Tau_right; [ | apply SIntChoice1 ].
             apply (compile_cmd_approx_refl nfvs); intros; eauto.
             apply (compile_cmd_approx_refl nfvs (WHILE c1 DO c2 END)); eauto.

        * simpl. rewrite open_under_lift.
          rewrite open_compile. simpl.
          apply (ApproxProc_Cong_PIntChoice nfvs); eauto.
          intros.
          apply (compile_cmd_approx_refl nfvs); intros; eauto. 
          apply (compile_cmd_approx_refl nfvs (WHILE c1 DO c2 END)); eauto.
  Qed.

  Theorem ApproxProc_PStop : forall m1 m2 p',
      ApproxProc PStop m1 p' m2.
  Proof.
    unfold ApproxProc; intros.
    inversion H. subst.
    remember (PGenPar PStop allEvents m1) as p.
    generalize dependent m1. clear H.
    induction H0; intros; subst; eauto.
    destruct ev.
    - inversion H; subst; eauto.
    - simpl. inversion H; subst; eauto.
  Qed.
  
  Hint Resolve ApproxProc_PStop.
    
  (* This constructs a process that approximates the memory state of a
     While program.  It is an approximation in two ways:

     1) The "state" type we use in the While language records a value
        for every variable name.  But any program only uses a finite
        subset of the possible variables.  So, MemProc's first
        argument is nat indicating how many variables should be
        modelled.

     2) MemProc uses our IntRepr type instead of actual integers.  So,
        the values are abstracted away if they are outside the
        supported range.
   *)
  Fixpoint PIteratedParallel (n : nat) (p : nat -> Proc) : Proc :=
    match n with
    | O => PStop
    | S n' => PGenPar (p n') (fun _ => False) (PIteratedParallel n' p)
    end.
    
  Definition MemProc (n : nat) (st : state) : Proc :=
    PIteratedParallel n (fun k => PFVar (VarState k (bound_Z (st k)))).

  Inductive ValidMemTranslation (st : state) : nat -> Proc -> Prop :=
  | VMTZero : ValidMemTranslation st O PStop
  | VMTSucc : forall n v ir m,
          ApproxIntRepr (bound_Z (st n)) ir
       -> ValidVarRep n ir v
       -> ValidMemTranslation st n m
       -> ValidMemTranslation st (S n) (PGenPar v noEvents m).
  Hint Constructors ValidMemTranslation.
  
  Theorem MemProc_ValidMemTranslation : forall st n,
      ValidMemTranslation st n (MemProc n st).
  Proof.
    unfold MemProc.
    intros. induction n; eauto.
    simpl.
    apply VMTSucc with (ir := bound_Z (st n)); intros; eauto.
  Qed.

  Theorem ValidMemTranslation_ValidMemRep : forall st n p,
     ValidMemTranslation st n p -> ValidMemRep n p.
  Proof.
    induction 1; intros; eauto.
  Qed.

  Hint Extern 2 => match goal with
  | [ H : ValidMemTranslation _ ?n ?p |- ValidMemRep ?n ?p ] =>
    exact (ValidMemTranslation_ValidMemRep _ _ _ H)
  end.

  Theorem none_step_same_state : forall c1 st1 c2 st2,
       c1 / st1 ==>[None] c2 / st2
    -> st1 = st2.
  Proof.
    intros c1 st1 c2 st2 HStep.
    remember None as ev.
    revert Heqev.
    induction HStep; intros; eauto.
    inversion Heqev.
  Qed.

  Theorem read_step_same_state : forall c1 st1 x n c2 st2,
       c1 / st1 ==>[Some (WEvRead x n)] c2 / st2
    -> st1 = st2.
  Proof.
    intros c1 st1 x n c2 st2 HStep.
    remember (Some (WEvRead x n)) as ev.
    revert Heqev.
    induction HStep; intros; eauto. 
    inversion Heqev.
  Qed.

  Theorem exp_steps_dont_write : forall e1 st1 x n e2,
    ~ (e1 / st1 ==a>[Some (WEvWrite x n)] e2).
  Proof.
    intros e1 st1 x n e2 HStep.
    remember (Some (WEvWrite x n)) as ev.
    revert Heqev.
    induction HStep; intros HEq; subst; eauto;
      try solve [inversion HEq].
  Qed.

  Theorem write_step_updates_state : forall c1 st1 x n c2 st2,
       c1 / st1 ==>[Some (WEvWrite x n)] c2 / st2
    -> st_update st1 x n = st2.
  Proof.
    intros c1 st1 x n c2 st2 HStep.
    remember (Some (WEvWrite x n)) as ev.
    revert Heqev.
    induction HStep; intros HEq; subst; eauto; 
      try solve [inversion HEq; subst; eauto].
    - destruct (exp_steps_dont_write _ _ _ _ _ H).
    - destruct (exp_steps_dont_write _ _ _ _ _ H).
  Qed.

  Theorem update_above_preserves_ValidMemTranslation : forall mem k n st1 z,
       ValidMemTranslation st1 n mem
    -> (n <= k)%nat
    -> ValidMemTranslation (st_update st1 k z) n mem.
  Proof.
    intros mem k n st1 z HVMT; revert k z; induction HVMT;
    intros; subst; eauto.
    
    assert (st_update st1 k z n = st1 n) as Hstu_eq.
    { unfold st_update.
      destruct (Nat.eqb_neq k n) as [_ HNeq].
      rewrite HNeq; eauto. omega. }

    apply VMTSucc with (ir := ir); eauto.
    - rewrite Hstu_eq. eauto.
    - apply IHHVMT. omega.
  Qed.

  Hint Resolve update_above_preserves_ValidMemTranslation.

  Theorem ValidMemTranslation_ValueInMem : forall st n x mem,
       ValidMemTranslation st n mem
    -> (x < n)%nat
    -> exists ir, ApproxIntRepr (bound_Z (st x)) ir
               /\ ValueInMem x mem ir.
  Proof.        
    intros st n x mem HVMT HLT.
    generalize dependent x. induction HVMT; intros; eauto.
    inversion HLT.
    inversion HLT; subst; eauto.
    assert ((x < n)%nat) by omega.
    apply IHHVMT in H1.
    destruct H1 as [ir' [HAIR HVIM]]. eauto.
  Qed.
    
  Theorem Some_step_updates_mem_translation : forall c1 st1 wev cev c2 st2 n mem,
        c1 / st1 ==>[Some wev] c2 / st2
     -> ValidMemTranslation st1 n mem
     -> ApproxEvent (whileToCSPEvent wev) cev
     -> ValidMemTranslation st2 n (updateMem cev mem).
  Proof.
    destruct wev; simpl in *; intros.
    - apply read_step_same_state in H; subst.
      inversion H1; subst; eauto.
    - apply write_step_updates_state in H; subst.
      clear c1 c2. generalize dependent n. revert z cev.
      induction H0; inversion 1; subst; eauto.
      inversion H0; subst; simpl; eauto.
      + remember ((n0 ?= n)%nat) as neq.
        apply Logic.eq_sym in Heqneq; destruct neq; simpl; eauto.
        * apply nat_compare_eq in Heqneq; subst.
          apply VMTSucc with (ir := v'); eauto.
          unfold st_update. rewrite <- beq_nat_refl. eauto.
        * apply VMTSucc with (ir := ir); eauto.
          -- unfold st_update.
             apply nat_compare_Lt_lt in Heqneq.
             destruct (Nat.eqb_neq n0 n) as [_ HNeq].
             rewrite HNeq; eauto; omega.
          -- apply (IHValidMemTranslation _ (CEWrite n0 v')); eauto.
        * apply nat_compare_Gt_gt in Heqneq.
          apply VMTSucc with (ir := ir); eauto.
          -- unfold st_update.
             destruct (Nat.eqb_neq n0 n) as [_ HNeq].
             rewrite HNeq; eauto; omega.
          -- assert (IH := IHValidMemTranslation z (CEWrite n0 v') n0 H2). 
             clear IHValidMemTranslation.
             simpl in IH.
             rewrite write_over_mem_id with (n1 := n) in IH; eauto.
             omega.

      + remember ((n0 ?= n)%nat) as neq.
        apply Logic.eq_sym in Heqneq; destruct neq; simpl; eauto.
        * apply nat_compare_eq in Heqneq; subst.
          apply VMTSucc with (ir := v'); eauto.
          unfold st_update. rewrite <- beq_nat_refl. eauto.
        * apply VMTSucc with (ir := ir); eauto.
          -- unfold st_update.
             apply nat_compare_Lt_lt in Heqneq.
             destruct (Nat.eqb_neq n0 n) as [_ HNeq].
             rewrite HNeq; eauto; omega.
          -- apply (IHValidMemTranslation _ (CEWrite n0 v')); eauto.
        * apply nat_compare_Gt_gt in Heqneq.
          apply VMTSucc with (ir := ir); eauto.
          -- unfold st_update.
             destruct (Nat.eqb_neq n0 n) as [_ HNeq].
             rewrite HNeq; eauto; omega.
          -- assert (IH := IHValidMemTranslation z (CEWrite n0 v') n0 H2). 
             clear IHValidMemTranslation.
             simpl in IH.
             rewrite write_over_mem_id with (n1 := n) in IH; eauto.
             omega.
             (* XXXX these two + bullets are just copy/pasted.  we need to generalize this *)
  Qed.

  Inductive ConsistentMemEvent : Sigma -> Proc -> Prop :=
  | CMERead : forall n mem ir,
         ValueInMem n mem ir
      -> ConsistentMemEvent (CERead n ir) mem
  | CMEWrite : forall nfvs n mem ir,
         ValidMemRep nfvs mem
      -> (n < nfvs)%nat
      -> ConsistentMemEvent (CEWrite n ir) mem.
  Hint Constructors ConsistentMemEvent.

  Theorem compile_exp_respects_event_step : forall nfvs e st wev e' m1 m2 k1 k2,
       e / st ==a>[ Some wev ] e'
    -> (fvs_exp e <= nfvs)%nat
    -> ValidMemTranslation st nfvs m1
    -> ApproxMem nfvs m1 m2
    -> (forall i1 i2 m1 m2,
             ApproxIntRepr i1 i2
          -> ApproxMem nfvs m1 m2
          -> ApproxProc (k1 i1) m1 (k2 i2) m2)
    -> exists ev, 
            ApproxEvent (whileToCSPEvent wev) ev
         /\ ConsistentMemEvent ev m1
         /\ ApproxProc (PPrefix ev (compile_exp e' k1)) m1 
                       (compile_exp e k2) m2.
  Proof.
    intros nfvs e st wev e' m1 m2 k1 k2 HStep; revert m1 m2 k1 k2;
    remember (Some wev) as wopt; generalize dependent wev.

    induction HStep; intros wev wev_eq m1 m2 k1 k2 HFvs HVMT HAM HACont;
    try (match goal with
    | [ HOpt : _ = Some _ |- _ ] => 
      inversion HOpt; subst; try (clear HOpt)
    end); eauto.
    
    simpl in *.
    destruct (ValidMemTranslation_ValueInMem _ _ x _ HVMT) as [ir1 [HAIR1 HVIM1]];
      eauto.
    
    exists (CERead x ir1); repeat split; eauto.
    destruct (ValueInMem_respects_ApproxMem _ _ _ _ _ HAM HVIM1)
          as [ir2 [HAIR2 HVIM2]].
    
    unfold ApproxProc. intros t HOST.
    eapply traceInversion_InMemory_PPrefix in HOST; eauto.
    destruct HOST as [? | [ttail [mem' [evshead [? [? [? [? [? ?]]]]]]]]];
      subst; eauto.
    
    assert (ApproxIntRepr (bound_Z (st x)) (ir2)) as HAIR2'; eauto.
    assert (ApproxMem nfvs mem' m2) as HAM' by
      (eauto using ApproxMem_respects_EquivMem_left).
    unfold ApproxProc in HACont.
    apply (HACont _ _ _ _ HAIR2' HAM') in H4.
    destruct H4 as [ttail' [HAT' HOST']].
    
    exists (CERead x ir2 :: ttail'); split; eauto.
    apply OpSemTraces_InMemory_extChoiceInt with (i := ir2).
    apply OpSemTraces_InMemory_PPrefix_CERead; eauto.
  Qed.
    

  Theorem compile_cmd_respects_event_step : forall nfvs c st wev c' st' m1 m2 k1 k2,
       c / st ==>[ Some wev ] c' / st'
    -> (fvs_cmd c <= nfvs)%nat
    -> ValidMemTranslation st nfvs m1
    -> ApproxMem nfvs m1 m2
    -> (forall m1 m2, ApproxMem nfvs m1 m2 -> ApproxProc k1 m1 k2 m2)
    -> exists ev,
            ApproxEvent (whileToCSPEvent wev) ev
         /\ ConsistentMemEvent ev m1
         /\ ApproxProc (PPrefix ev (compile c' k1)) m1 
                       (compile c k2) m2.
  Proof.
    intros nfvs c st wev c' st' m1 m2 k1 k2 HStep; revert m1 m2 k1 k2.  
    remember (Some wev) as ev; generalize dependent wev.
    
    induction HStep;
    intros wev wev_eq m1 m2 k1 k2 HFvs HVMT HAMem HCont; subst;
    try (match goal with
    | [ HOpt : _ = Some _ |- _ ] => 
      inversion HOpt; subst; try (clear HOpt)
    end).

    - simpl in *. 
      apply compile_exp_respects_event_step with (nfvs := nfvs) (st := st); eauto.
      intros.
      apply (ApproxProc_Cong_PPrefix_CEWrite nfvs); eauto; intros.

    - simpl in *.
      exists (CEWrite x (bound_Z n)); repeat (split); eauto.
      apply (ApproxProc_Cong_PPrefix_CEWrite nfvs); eauto; intros.

    - simpl in *.  apply IHHStep; intros; eauto.
      + eauto using (compile_cmd_approx_refl nfvs).

    - simpl in *.
      apply compile_exp_respects_event_step with (nfvs := nfvs) (st := st); 
        intros; eauto.
      apply Max.max_lub_r in HFvs.
      inversion H0; subst; eauto.
      + destruct (n =? 0);
          eauto using (compile_cmd_approx_refl nfvs).
      + destruct i1.
        * destruct (k =? 0).
          -- apply ApproxProc_Tau_right with (p2' := compile c3 k2);
               eauto using (compile_cmd_approx_refl nfvs).
          -- apply ApproxProc_Tau_right with (p2' := compile c2 k2);
               eauto using (compile_cmd_approx_refl nfvs).
        * eauto using (compile_cmd_approx_refl nfvs),
                      (ApproxProc_Cong_PIntChoice nfvs).
  Qed.

  Theorem consistent_mem_updates_allowed : forall nfvs ev mem,
         ConsistentMemEvent ev mem
      -> ValidMemRep nfvs mem
      -> exists evs,
              observableEvents evs = (ev :: nil)
           /\ MStep WhileEnv mem evs (updateMem ev mem).
  Proof.
    intros nfvs ev mem HCME HVMR.
    inversion HCME; subst.
    - simpl in *.
      assert (HRead := ValueInMem_may_be_read _ _ _ H).
      destruct HRead as [evs [? ?]]; eauto 10.
    - destruct (mem_may_be_written n ir nfvs0 mem) as [evs [HMS HObs]]; eauto.
  Qed.

  Theorem translation_sound_generalized : forall wprog wprog' mem mem' wtrace memProc n,
       wprog / mem ==>*[wtrace] wprog' / mem'
    -> (n >= fvs_cmd wprog)%nat
    -> ValidMemTranslation mem n memProc
    -> exists ctrace,
            ApproxTrace (whileToCSPTrace wtrace) ctrace
         /\ OpSemTraces WhileEnv
              (PGenPar (compile wprog PStop)
                       allEvents
                       memProc)
              ctrace.
  Proof.
    intros wprog wprog' mem mem' wtrace memProc n HMS.
    revert memProc n.
    induction HMS; eauto; intros.

    (* There are three cases, one of which was solved by Auto: MCRefl (solved by
    auto), MCStepTau and MCStepEv *)

    (* MCStepTau: the program has stepped but the event wasn't observable.  The
       IH tells us that the stepped program translates to a process with a
       suitable trace.  Even though the original program does something
       unobservable, the translated program may not have the same trace.  The
       original program's trace should have the same length, but it may be more
       abstract when our model can't accurately capture the step of computation
       that took place in the original program and must approximate. *)
    - assert (ApproxProc (compile c2 PStop) memProc (compile c1 PStop) memProc)
        by (eapply compile_cmd_respects_nil_step; intros; eauto).

      unfold ApproxProc in H2.
      destruct (IHHMS memProc n) as [ctrace [Hctrace1 Hctrace2]]; eauto.

      + apply step_cmd_fvs in H.
        omega.
      + apply none_step_same_state in H; subst; eauto.
      + apply (H2 _) in Hctrace2; eauto.
        destruct Hctrace2 as [? [? ?]].
        eauto using ApproxTrace_trans.

    - assert ((fvs_cmd c1 <= n)%nat) by omega.
      edestruct (compile_cmd_respects_event_step _ _ _ _ _ _ _ memProc PStop PStop 
                   H H2 H1) as [ev' [HAE [HCME HAP]]]; eauto.
      assert (HVMT2 := Some_step_updates_mem_translation _ _ _ _ _ _ _ _ 
                                                         H H1 HAE).
      assert ((n >= fvs_cmd c2)%nat) by (apply step_cmd_fvs in H; omega).
      apply IHHMS in HVMT2; eauto.
      destruct HVMT2 as [ttail [HATtail HOSTtail]].
      unfold ApproxProc in HAP.
      
      clear IHHMS.
      destruct (HAP (ev' :: ttail)) as [ctrace [HAT HOST]]; eauto.
      + destruct (consistent_mem_updates_allowed n _ _ HCME)
              as [evsmem [? ?]]; eauto.
        destruct (allEvents_syncable (EvSigma ev' :: nil) evsmem)
              as [evsSynced ?]; simpl; eauto.
        replace (ev' :: ttail) with (observableEvents evsmem ++ ttail)
                                 by (rewrite H4; eauto).
        rewrite (SI_all_observable_right _ _ _ H6).
        apply OpSemTraces_trans
          with (q := PGenPar (compile c2 PStop) allEvents (updateMem ev' memProc)); eauto.
        apply (MStep_PGenPar_SI _ _ _ _ _ _ _ _ _ H6); eauto.
      + exists ctrace; simpl; eauto using ApproxTrace_trans.
  Qed.

  Theorem translation_sound : forall wprog wprog' st st' wtrace,
       wprog / st ==>*[wtrace] wprog' / st'
    -> exists ctrace,
            ApproxTrace (whileToCSPTrace wtrace) ctrace
         /\ OpSemTraces WhileEnv
              (PGenPar (compile wprog PStop)
                       allEvents
                       (MemProc (fvs_cmd wprog) st))
              ctrace.
  Proof.
    intros.
    apply (translation_sound_generalized _ _ _ _ _ _ (fvs_cmd wprog) H); 
      eauto using MemProc_ValidMemTranslation.
  Qed.
End CompilerProofs.

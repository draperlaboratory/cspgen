Require Import CSP_Syntax.
Require Import Coq.Structures.Equalities.
Require Import Coq.Sets.Ensembles.
Require Import List.

Module OpSem (Alphabet:Typ) (Names:Typ).

Module Export Syn := Syntax Alphabet Names.

Definition Env : Type := name -> Proc.

Notation allEvents := (fun _ => True).
Notation noEvents := (fun _ => False).

(* The operational semantics for CSP as given in CSPSyntax.  Roughly, 

      D |- p ~ev~> q

   Indicates that, in environment D, the process p can perform a step of
   computation labelled with the event ev and transform to q.

 *)
Inductive Step : Env -> Proc -> Event -> Proc -> Prop :=
  | SFVar       : forall D n, Step D (PFVar n) EvTau (D n)

  | SPrefix     : forall D c p, 
    Step D (PPrefix c p) (EvSigma c) p

  | SHideHidden : forall D c (cs : SigmaSet) p p',
        Step D p (EvSigma c) p'
     -> cs c
     -> Step D (PHide p cs) EvTau (PHide p' cs)
  | SHideShown  : forall D c cs p p',
        Step D p (EvSigma c) p'
     -> ~ (cs c)
     -> Step D (PHide p cs) (EvSigma c) (PHide p' cs)
  | SHideTau    : forall D cs p p',
        Step D p EvTau p'
     -> Step D (PHide p cs) EvTau (PHide p' cs)

  | SGenParSync : forall D p1 p1' p2 p2' c (cs : SigmaSet),
        Step D p1 (EvSigma c) p1'
     -> Step D p2 (EvSigma c) p2'
     -> cs c
     -> Step D (PGenPar p1 cs p2) (EvSigma c) (PGenPar p1' cs p2')
  | SGenParSigma1 : forall D p1 p1' p2 c cs,
        Step D p1 (EvSigma c) p1'
     -> ~ (cs c)
     -> Step D (PGenPar p1 cs p2) (EvSigma c) (PGenPar p1' cs p2)
  | SGenParSigma2 : forall D p1 p2 p2' c cs,
        Step D p2 (EvSigma c) p2'
     -> ~ (cs c)
     -> Step D (PGenPar p1 cs p2) (EvSigma c) (PGenPar p1 cs p2')
  | SGenParTau1 : forall D p1 p1' p2 cs,
        Step D p1 EvTau p1'
     -> Step D (PGenPar p1 cs p2) EvTau (PGenPar p1' cs p2)
  | SGenParTau2 : forall D p1 p2 p2' cs,
        Step D p2 EvTau p2'
     -> Step D (PGenPar p1 cs p2) EvTau (PGenPar p1 cs p2')

  | SExtChoice1 : forall D p1 p1' p2 e,
        Step D p1 e p1'
     -> ~ (e = EvTau)
     -> Step D (PExtChoice p1 p2) e p1'
  | SExtChoice2 : forall D p1 p2 p2' e,
        Step D p2 e p2'
     -> ~ (e = EvTau)
     -> Step D (PExtChoice p1 p2) e p2'
  | SExtChoiceTau1 : forall D p1 p1' p2,
        Step D p1 EvTau p1'
     -> Step D (PExtChoice p1 p2) EvTau (PExtChoice p1' p2)
  | SExtChoiceTau2 : forall D p1 p2 p2',
        Step D p2 EvTau p2'
     -> Step D (PExtChoice p1 p2) EvTau (PExtChoice p1 p2')

  | SIntChoice1 : forall p1 p2 D, Step D (PIntChoice p1 p2) EvTau p1
  | SIntChoice2 : forall p1 p2 D, Step D (PIntChoice p1 p2) EvTau p2

  | SMu : forall p D, Step D (PMu p) EvTau ({0 ~> PMu p}p)
.

Inductive MStep : Env -> Proc -> list Event -> Proc -> Prop :=  
  | MSRefl : forall D p, MStep D p nil p
  | MSStep : forall D p ev p' evs q,
         Step D p ev p'
      -> MStep D p' evs q
      -> MStep D p (ev :: evs) q
.



(* Many clauses of the operational semantics require proving an event isn't tau.
   We help auto resolve that when it's obvious from constructors. *)
Hint Extern 2 => match goal with
  | [ |- EvSigma _ <> EvTau ] => inversion 1
  | [ |- EvTau <> EvSigma _ ] => inversion 1
  end.

Fixpoint observableEvents (evs : list Event) : Trace :=
  match evs with
  | nil => nil
  | EvTau :: evs => observableEvents evs
  | EvSigma c :: evs => c :: observableEvents evs
  end.

Inductive OpSemTraces (D : Env) (p : Proc) : Trace -> Prop :=
  TStepsTo : forall evs q, MStep D p evs q -> OpSemTraces D p (observableEvents evs).

Hint Constructors MStep Step OpSemTraces.

Theorem OpSemTraces_nil_always : forall D p, OpSemTraces D p nil.
Proof.
  intros. replace (@nil Sigma) with (observableEvents (@nil Event)); eauto. 
Qed. 
Hint Immediate OpSemTraces_nil_always.

(**************************************************************
 **** Some useful facts about the operational semantics 
 **************************************************************)

Theorem MStep_GenPar_LeftSolo : forall G PSync t p1 p1' p2,
      Forall (fun c => ~ (PSync c)) (observableEvents t)
   -> MStep G p1 t p1'
   -> MStep G (PGenPar p1 PSync p2) t (PGenPar p1' PSync p2).
Proof.
  intros G PSync t p1 p1' p2 HForall HMS;
  induction HMS; eauto;
  match goal with
  | [ HStep : Step _ _ ?ev _,
      HForall : Forall _ _  |- _ ] => 
    destruct ev; eauto; inversion HForall; eauto
  end.
Qed.    

Theorem MStep_GenPar_RightSolo : forall G PSync t p1 p2 p2',
      Forall (fun c => ~ (PSync c)) (observableEvents t)
   -> MStep G p2 t p2'
   -> MStep G (PGenPar p1 PSync p2) t (PGenPar p1 PSync p2').
Proof.
  intros G PSync t p1 p1' p2 HForall HMS;
  induction HMS; eauto;
  match goal with
  | [ HStep : Step _ _ ?ev _,
      HForall : Forall _ _  |- _ ] => 
    destruct ev; eauto; inversion HForall; eauto
  end.
Qed.    

Theorem MStep_GenPar_LeftNil : forall G PSync p1 p1' p2,
      MStep G p1 nil p1'
   -> MStep G (PGenPar p1 PSync p2) nil (PGenPar p1' PSync p2).
Proof.
  intros; apply MStep_GenPar_LeftSolo; simpl; eauto.
Qed.

Theorem MStep_GenPar_RightNil : forall G PSync p1 p2 p2',
      MStep G p2 nil p2'
   -> MStep G (PGenPar p1 PSync p2) nil (PGenPar p1 PSync p2').
Proof.
  intros; apply MStep_GenPar_RightSolo; simpl; eauto.
Qed.

Hint Resolve MStep_GenPar_LeftNil MStep_GenPar_RightNil.

Theorem MStep_trans : forall G p1 p2 p3 t1 t2,
  MStep G p1 t1 p2 -> MStep G p2 t2 p3 -> MStep G p1 (t1 ++ t2) p3.
Proof.
  intros G p1 p2 p3 t1 t2 HMS1; revert p3 t2;
  induction HMS1; intros p3 t2 HMS2; simpl; eauto.
Qed.
(*
Theorem MStep_GenPar_Sync : forall G t1 t2 p1 p1' p2 p2',
     MStep G p1 t1 p1'
  -> MStep G p2 t2 p2'
  -> observableEvents t1 = observableEvents t2
  -> exists t3, 
          MStep G (PGenPar p1 allEvents p2) t3 (PGenPar p1' allEvents p2')
       /\ observableEvents t3 = observableEvents t1.
Proof.
  intros G t1 t2 p1 p1' p2 p2' HMS1; revert t2 p2 p2';
  induction HMS1; intros t2 p2 p2' HMS2 HAgree; eauto.

  - simpl in *. exists t2. split; eauto.
    apply MStep_GenPar_RightSolo; eauto.
    rewrite <- HAgree; eauto.

  - destruct ev. 
    + induction HMS2; subst.
      * simpl in HAgree. inversion HAgree.
      * destruct ev.  
          simpl in HAgree; inversion HAgree; subst; clear HAgree.
          destruct (IHHMS1 _ _ _ HMS2 H3) as [t3 [? ?]].
          exists (EvSigma t0 :: t3).  split.
          apply MSStep with (p' := PGenPar p' allEvents p'0); eauto.
          simpl. f_equal; eauto.
          
          simpl in HAgree.
          destruct (IHHMS2 H HMS1 IHHMS1) as [t3 [? ?]]; simpl; eauto.
          exists (EvTau :: t3); split; eauto.
          apply MSStep with (p' := PGenPar p allEvents p'0); eauto.

    + simpl in *.
      destruct (IHHMS1 _ _ _ HMS2 HAgree) as [t3 [? ?]].
      exists (EvTau :: t3); split; eauto.
      apply MSStep with (p' := PGenPar p' allEvents p2); eauto.
Qed.
*)
Inductive SyncedInterleavings (PSync : SigmaSet)
     : list Event -> list Event -> list Event -> Prop :=
| SIStopped : SyncedInterleavings PSync nil nil nil
| SILeftTau : forall ll lr li,
       SyncedInterleavings PSync ll lr li
    -> SyncedInterleavings PSync (EvTau :: ll) lr (EvTau :: li)
| SIRightTau : forall ll lr li,
       SyncedInterleavings PSync ll lr li
    -> SyncedInterleavings PSync ll (EvTau :: lr) (EvTau :: li)
| SILeftOnly : forall c ll lr li,
       ~ (PSync c)
    -> SyncedInterleavings PSync ll lr li
    -> SyncedInterleavings PSync (EvSigma c :: ll) lr (EvSigma c :: li)
| SIRightOnly : forall c ll lr li,
       ~ (PSync c)
    -> SyncedInterleavings PSync ll lr li
    -> SyncedInterleavings PSync ll (EvSigma c :: lr) (EvSigma c :: li)
| SITogether : forall c ll lr li,
       PSync c
    -> SyncedInterleavings PSync ll lr li
    -> SyncedInterleavings PSync (EvSigma c :: ll) (EvSigma c :: lr)
                                 (EvSigma c :: li).
Hint Constructors SyncedInterleavings.

Theorem SI_all_observable_left : forall evs1 evs2 evs3,
     SyncedInterleavings allEvents evs1 evs2 evs3
  -> observableEvents evs1 = observableEvents evs3.
Proof.
  induction 1; simpl; eauto.
  - destruct H; eauto.
  - destruct H; eauto.
  - f_equal; eauto.
Qed.

Theorem SI_all_observable_right : forall evs1 evs2 evs3,
     SyncedInterleavings allEvents evs1 evs2 evs3
  -> observableEvents evs2 = observableEvents evs3.
Proof.
  induction 1; simpl; eauto.
  - destruct H; eauto.
  - destruct H; eauto.
  - f_equal; eauto.
Qed.

Theorem allEvents_syncable : forall evs1 evs2,
     observableEvents evs1 = observableEvents evs2
  -> exists evs3, SyncedInterleavings allEvents evs1 evs2 evs3.
Proof.
  induction evs1; induction evs2; intros HEq; simpl; eauto.
  - destruct a; simpl in *.
    + inversion HEq.
    + destruct (IHevs2 HEq) as [evs3 ?]. eauto.
  - destruct a; simpl in *.
    + inversion HEq.
    + destruct (IHevs1 nil HEq) as [evs3 ?]; eauto.
  - destruct a; destruct a0.
    + inversion HEq; subst.
      destruct (IHevs1 _ H1); eauto.
    + destruct (IHevs2 HEq); eauto.
    + destruct (IHevs1 _ HEq); eauto.
    + destruct (IHevs1 _ HEq); eauto.
Qed.      

Theorem MStep_PGenPar_SI : forall G PSync evs1 evs2 evs3 p1 p1' p2 p2',
      SyncedInterleavings PSync evs1 evs2 evs3
   -> MStep G p1 evs1 p1'
   -> MStep G p2 evs2 p2'
   -> MStep G (PGenPar p1 PSync p2) evs3 (PGenPar p1' PSync p2').
Proof.
  intros G PSync ev1 ev2 ev3 p1 p1' p2 p2' HSI; revert G p1 p1' p2 p2';
  induction HSI; intros G p1 p1' p2 p2' HMS1 HMS2;
  subst;

  repeat (match goal with
  | [ HMS : MStep _ _ nil _ |- _ ] => inversion HMS; subst; clear HMS
  | [ HMS : MStep _ _ (_ :: _) _ |- _ ] => inversion HMS; subst; clear HMS
  end); eauto.
Qed.

Theorem MStep_Inversion_PGenPar : forall D p1 PSync p2 evs q,
     MStep D (PGenPar p1 PSync p2) evs q
  -> exists evs1 p1' evs2 p2',
          q = (PGenPar p1' PSync p2')
       /\ MStep D p1 evs1 p1'
       /\ MStep D p2 evs2 p2'
       /\ SyncedInterleavings PSync evs1 evs2 evs.
Proof.
  intros d p1 PSync p2 evs q HMS;
  remember (PGenPar p1 PSync p2) as p;
  generalize dependent p2; revert p1 PSync;
  induction HMS; intros p1 PSync p2 HEq; subst; eauto 8.

  inversion H; subst;

  match goal with
  | [ IH : forall _ _ _, _ = _ -> _ |- _ ] => 
    destruct (IH _ _ _ eq_refl) as [evs1 [q1 [evs2 [q2 [? [? [? ?]]]]]]];
      subst; clear IH; eauto 15
  end.
Qed.
  
Theorem MStep_PExtChoice_Left : forall D p1 p2 evs q,
      MStep D p1 evs q
   -> observableEvents evs <> nil
   -> MStep D (PExtChoice p1 p2) evs q.
Proof.
  induction 1; intros; subst; eauto.
  - destruct H; simpl; auto.
  - destruct ev; simpl in *; eauto.
Qed.

Theorem MStep_PExtChoice_Right : forall D p1 p2 evs q,
      MStep D p2 evs q
   -> observableEvents evs <> nil
   -> MStep D (PExtChoice p1 p2) evs q.
Proof.
  induction 1; intros; subst; eauto.
  - destruct H; simpl; auto.
  - destruct ev; simpl in *; eauto.
Qed.

End OpSem.

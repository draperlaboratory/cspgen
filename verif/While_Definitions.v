(* This file contains the definition and semantics of a dead-simple imperative
   programming language, as one might find in any introductory PL textbook.  The
   only novelty is that the small-step operational semantics are annotated with
   the memory events that occur during each step of evaluation.  The
   mechanization here was created in part based on the "Imp.v" from the Software
   Foundations textbook (which is available under a permissive MIT-style
   license).

   Integers are the only values in the program.  Variables are represented as
   natural numbers, and the state/memory is represented as a map from these
   variables to their values (i.e., nat -> int).  The language does not have a
   primitive notion of boolean.  When an int is used as a bool, 0 is false and
   any other value is true.
 *)

Require Import ZArith.

(* ltac magic to be moved elsewhere.  due to aaron bohannon *)
Tactic Notation
  "if" tactic(t)
  "then" tactic(t1)
  "else" tactic(t2) :=
  first [ t; first [ t1 | fail 2 ] | t2 ].

Tactic Notation "require_neq" constr(a) constr(b) :=
  if constr_eq a b then fail 2 else idtac.


(* Syntax *)
Notation var := nat.

Inductive exp : Set :=
  | EVar : var -> exp
  | ENum : Z -> exp

  | EPlus : exp -> exp -> exp
  | EMinus : exp -> exp -> exp
  | ETimes : exp -> exp -> exp

  | EEq : exp -> exp -> exp
  | ELTE : exp -> exp -> exp
  | ENot : exp -> exp
  | EOr : exp -> exp -> exp
  | EAnd : exp -> exp -> exp
.

Inductive cmd : Set :=
  | CSkip  : cmd
  | CAssn  : var -> exp -> cmd
  | CSeq   : cmd -> cmd -> cmd
  | CIf    : exp -> cmd -> cmd -> cmd
  | CWhile : exp -> cmd -> cmd
.

Notation "'SKIP'"    := 
  CSkip.
Notation "x '::=' a" := 
  (CAssn x a) (at level 60).
Notation "c1 ;; c2"  := 
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'IFC' a1 'THEN' c2 'ELSE' c3 'FI'" := 
  (CIf a1 c2 c3) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).


(* Semantics *)
Inductive wevent : Set :=
  | WEvRead  : var -> Z -> wevent
  | WEvWrite : var -> Z -> wevent
.

Notation state := (var -> Z).

Definition st_update (st : state) (x : var) (v : Z) : state :=
  fun x' => if beq_nat x x' then v else st x'.

Fixpoint fvs_exp (e : exp) : nat :=
  match e with
  | EVar n => S n
  | ENum _ => O
  | EPlus e1 e2  => max (fvs_exp e1) (fvs_exp e2)
  | EMinus e1 e2 => max (fvs_exp e1) (fvs_exp e2)
  | ETimes e1 e2 => max (fvs_exp e1) (fvs_exp e2)
  | EEq e1 e2    => max (fvs_exp e1) (fvs_exp e2)
  | ELTE e1 e2   => max (fvs_exp e1) (fvs_exp e2)
  | ENot e1      => fvs_exp e1
  | EOr e1 e2    => max (fvs_exp e1) (fvs_exp e2)
  | EAnd e1 e2   => max (fvs_exp e1) (fvs_exp e2)
  end.

Fixpoint fvs_cmd (c : cmd) : nat :=
  match c with
  | CSkip        => O
  | CAssn v e    => max (fvs_exp e) (S v) 
  | CSeq c1 c2   => max (fvs_cmd c1) (fvs_cmd c2)
  | CIf e1 c2 c3 => max (fvs_exp e1) (max (fvs_cmd c2) (fvs_cmd c3))
  | CWhile e1 c2 => max (fvs_exp e1) (fvs_cmd c2)
  end.

Reserved Notation " e '/' st '==a>[' ev ']' e' " (at level 40, st at level 39).

Local Open Scope Z_scope.

Inductive EStep : exp -> state -> option wevent -> exp -> Prop :=
  | ESVar : forall st x, (EVar x) / st ==a>[Some (WEvRead x (st x))] (ENum (st x))

  | ESPlus1 : forall st e1 e1' e2 ev,
        e1 / st ==a>[ev] e1'
     -> (EPlus e1 e2) / st ==a>[ev] (EPlus e1' e2)
  | ESPlus2 : forall st n e2 e2' ev,
        e2 / st ==a>[ev] e2'
     -> (EPlus (ENum n) e2) / st ==a>[ev] (EPlus (ENum n) e2')
  | ESPlus : forall st n m,
        (EPlus (ENum n) (ENum m)) / st ==a>[None] (ENum (n+m))
  | ESMinus1 : forall st e1 e1' e2 ev,
        e1 / st ==a>[ev] e1'
     -> (EMinus e1 e2) / st ==a>[ev] (EMinus e1' e2)
  | ESMinus2 : forall st n e2 e2' ev,
        e2 / st ==a>[ev] e2'
     -> (EMinus (ENum n) e2) / st ==a>[ev] (EMinus (ENum n) e2')
  | ESMinus : forall st n m, 
        (EMinus (ENum n) (ENum m)) / st ==a>[None] (ENum (n-m))
  | ESTimes1 : forall st e1 e1' e2 ev,
        e1 / st ==a>[ev] e1' 
     -> (ETimes e1 e2) / st ==a>[ev] (ETimes e1' e2)
  | ESTimes2 : forall st n e2 e2' ev,
        e2 / st ==a>[ev] e2' 
     -> (ETimes (ENum n) e2) / st ==a>[ev] (ETimes (ENum n) e2')
  | ESTimes : forall st n m, 
        (ETimes (ENum n) (ENum m)) /st ==a>[None] (ENum (n*m))

  | ESEq1 : forall st e1 e1' e2 ev,
        e1 / st ==a>[ev] e1' 
     -> (EEq e1 e2) / st ==a>[ev] (EEq e1' e2)
  | ESEq2 : forall st n e2 e2' ev,
        e2 / st ==a>[ev] e2' 
     -> (EEq (ENum n) e2) / st ==a>[ev] (EEq (ENum n) e2')
  | ESEqEq : forall st n, 
        (EEq (ENum n) (ENum n)) / st ==a>[None] (ENum 1)
  | ESEqNeq : forall st n m, 
        n <> m
     -> (EEq (ENum n) (ENum m)) / st ==a>[None] (ENum 0)

  | ESLTE1 : forall st e1 e1' e2 ev,
        e1 / st ==a>[ev] e1' 
     -> (ELTE e1 e2) / st ==a>[ev] (ELTE e1' e2)
  | ESLTE2 : forall st n e2 e2' ev,
        e2 /st ==a>[ev] e2' 
     -> (ELTE (ENum n) e2) / st ==a>[ev] (ELTE (ENum n) e2')
  | ESLTELTE : forall st n m, 
        (n ?= m) <> Gt
     -> (ELTE (ENum n) (ENum m)) / st ==a>[None] (ENum 1)
  | ESLTEGT : forall st n m, 
        (n ?= m) = Gt
     -> (ELTE (ENum n) (ENum m)) / st ==a>[None] (ENum 0)

  | ESNot1 : forall st e1 e1' ev,
        e1 / st ==a>[ev] e1'
     -> (ENot e1) / st ==a>[ev] (ENot e1')
  | ESNotFalse : forall st,
        (ENot (ENum 0)) / st ==a>[None] (ENum 1)
  | ESNotTrue : forall st n,
        n <> 0    
     -> (ENot (ENum n)) / st ==a>[None] (ENum 0)

  | ESOr1 : forall st e1 e1' e2 ev,
        e1 / st ==a>[ev] e1' 
     -> (EOr e1 e2) / st ==a>[ev] (EOr e1' e2)
  | ESOr2 : forall st n e2 e2' ev,
        e2 / st ==a>[ev] e2' 
     -> (EOr (ENum n) e2) / st ==a>[ev] (EOr (ENum n) e2')
  | EsOrFalse : forall st,
        (EOr (ENum 0) (ENum 0)) / st ==a>[None] (ENum 0)
  | EsOrTrue : forall st n m,
        ((n <> 0) \/ (m <> 0))
     -> (EOr (ENum n) (ENum m)) / st ==a>[None] (ENum 1)

  | ESAnd1 : forall st e1 e1' e2 ev,
        e1 / st ==a>[ev] e1' 
     -> (EAnd e1 e2) / st ==a>[ev] (EAnd e1' e2)
  | ESAnd2 : forall st n e2 e2' ev,
        e2 / st ==a>[ev] e2' 
     -> (EAnd (ENum n) e2) / st ==a>[ev] (EAnd (ENum n) e2')
  | EsAndFalse : forall st n m,
        ((n = 0) \/ (m = 0))
     -> (EAnd (ENum n) (ENum m)) / st ==a>[None] (ENum 0)
  | EsAndTrue : forall st n m,
        n <> 0
     -> m <> 0
     -> (EAnd (ENum n) (ENum m)) / st ==a>[None] (ENum 1)
  where " e '/' st '==a>[' ev ']' e' " := (EStep e st ev e')
.

Reserved Notation " c '/' st '==>[' ev ']' c1 / st1 " 
                  (at level 40, st at level 39, c1 at level 39).


Inductive CStep : cmd -> state -> option wevent -> cmd -> state -> Prop :=
  | CSAssn1 : forall st x e e' ev,
        e / st ==a>[ev] e'
     -> (x ::= e) / st ==>[ev] (x ::= e') / st
  | CSAssn : forall st x n,
        (x ::= ENum n) / st ==>[Some (WEvWrite x n)] SKIP / (st_update st x n)

  | CSSeq1 : forall st st' c1 c1' c2 ev,
        c1 / st ==>[ev] c1' / st'
     -> (c1 ;; c2) / st ==>[ev] (c1' ;; c2) / st'
  | CSSeq : forall st c2,
        (SKIP ;; c2) / st ==>[None] c2 / st

  | CSIf1 : forall st e1 e1' ev c2 c3,
        e1 / st ==a>[ev] e1'
     ->         (IFC e1 THEN c2 ELSE c3 FI) / st 
        ==>[ev] (IFC e1' THEN c2 ELSE c3 FI) / st
  | CSIfFalse : forall st c2 c3,
        (IFC (ENum 0) THEN c2 ELSE c3 FI) / st ==>[None] c3 / st
  | CSIfTrue : forall st n c2 c3,
        n <> 0
     -> (IFC (ENum n) THEN c2 ELSE c3 FI) / st ==>[None] c2 / st

  | CSWhile : forall st c1 c2,
                 (WHILE c1 DO c2 END) / st 
      ==>[None] (IFC c1 THEN (c2 ;; WHILE c1 DO c2 END) ELSE SKIP FI) / st
  where " c '/' st '==>[' ev ']' c1 / st1 " := (CStep c st ev c1 st1)
.


(* A few random properties of step. *)
Hint Extern 3 => match goal with
  | [ H : (ENum _) / _ ==a>[_] _ |- _ ] => inversion H
end. 

Theorem astep_deterministic : forall e st ev1 e1 ev2 e2,
     e / st ==a>[ev1] e1
  -> e / st ==a>[ev2] e2
  -> ev1 = ev2 /\ e1 = e2.
Proof.
  intros e st ev1 e1 ev2 e2 HAS1; revert ev2 e2.
  induction HAS1; intros ev_1 e_1 HAS_1;
  try solve [inversion HAS_1; subst; auto; match goal with
  | [ H : ?n <> ?n |- _ ] => destruct H; auto
  | [ HNo : ?x <> ?y,
      HYes : ?x = ?y |- _ ] => apply HNo in HYes; inversion HYes
  | [ H : (?x <> ?x) \/ (?y <> ?y) |- _ ] =>
    let H' := fresh H in 
    destruct H as [H' | H']; destruct H'; auto
  | [ HOr : ?a = ?b \/ ?c = ?d, 
      HNeq1 : ?a <> ?b,
      HNeq2 : ?c <> ?d |- _ ] => 
    let HEq := fresh "HEq" in 
    destruct HOr as [HEq | HEq]; [apply HNeq1 in HEq | apply HNeq2 in HEq];
    inversion HEq
  | [ IH : forall _ _, ?e / ?st ==a>[_] _ -> ?ev1 = _ /\ _,
      HInv : ?e / ?st ==a>[?ev2] _ |- _ ] =>
    require_neq ev1 ev2;
    apply IH in HInv; clear IH; destruct HInv; subst; auto
  end].
Qed.

Hint Extern 2 => match goal with
  | [ H : SKIP / _ ==>[_] _ / _ |- _ ] => inversion H
  end.

Theorem cstep_deterministic : forall c st c1 ev1 st1 c2 ev2 st2,
     c / st ==>[ev1] c1 / st1
  -> c / st ==>[ev2] c2 / st2
  -> ev1 = ev2 /\ c1 = c2 /\ st1 = st2.
Proof.
  intros c st c1 ev1 st1 c2 ev2 st2 HCS1 HCS2.
  revert c2 ev2 st2 HCS2.
  induction HCS1; intros c_1 ev_1 st_1 HCS_1;
  inversion HCS_1; subst; auto;
  match goal with
  | [ HNeq : ?x <> ?x |- _ ] => destruct HNeq; auto
  | [ HAS1 : ?e / ?st ==a>[?ev1] ?e1,
      HAS2 : ?e / ?st ==a>[?ev2] ?e2 |- _ ] =>
    require_neq ev1 ev2; let HEqs := fresh "HEqs" in
    assert (ev1 = ev2 /\ e1 = e2) as HEqs 
        by (eauto using astep_deterministic);
    clear HAS1 HAS2; destruct HEqs; subst; auto
  | [ IH : forall _ _ _, ?c / ?st ==>[_] _ / _ -> ?ev1 = _ /\ _ /\ _,
      HInv : ?c / ?st ==>[?ev2] _ / _ |- _ ] =>
    require_neq ev1 ev2;
    apply IH in HInv; clear IH; destruct HInv as [? [? ?]]; subst; auto
  end.
Qed.


Reserved Notation " c '/' st '==>*[' evs ']' c1 / st1 " 
                  (at level 40, st at level 39, c1 at level 39).

Inductive MCStep : cmd -> state -> list wevent -> cmd -> state -> Prop :=
  | MCRefl : forall st c, c / st ==>*[nil] c / st
  | MCStepTau : forall st1 c1 st2 c2 st3 c3 evs,
         c1 / st1 ==>[None] c2 / st2
      -> c2 / st2 ==>*[evs] c3 / st3
      -> c1 / st1 ==>*[evs] c3 / st3
  | MCStepEv : forall st1 c1 st2 c2 st3 c3 ev evs,
         c1 / st1 ==>[Some ev] c2 / st2
      -> c2 / st2 ==>*[evs] c3 / st3
      -> c1 / st1 ==>*[ev::evs] c3 / st3
  where " c '/' st '==>*[' evs ']' c1 '/' st1 " := (MCStep c st evs c1 st1)
.

Theorem step_exp_fvs : forall e1 st1 ev e2,
       e1 / st1 ==a>[ev] e2 
    -> (fvs_exp e2 <= fvs_exp e1)%nat.
Proof.
  induction 1; intros; simpl in *; 
    try omega;
    eauto using Nat.max_le_compat_r.
Qed.

Theorem step_cmd_fvs : forall c1 st1 ev c2 st2,
       c1 / st1 ==>[ev] c2 / st2
    -> (fvs_cmd c2 <= fvs_cmd c1)% nat.
Proof.
  induction 1; intros; simpl in *; 
    try omega;
    eauto using Nat.max_le_compat_r, step_exp_fvs,
                Nat.le_max_r, Nat.le_max_l.
  
  repeat (apply Nat.max_lub; try omega;
    eauto using Nat.max_le_compat_r, step_exp_fvs,
                Nat.le_max_r, Nat.le_max_l).
Qed.

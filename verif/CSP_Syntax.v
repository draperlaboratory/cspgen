Require Import Arith.
Require Import Max.
Require Import Coq.Structures.Equalities.
Require Import Coq.Sets.Ensembles.
Require Import Coq.omega.Omega.

(* The syntax is parameterized by the alphabet of events and the type for names
   in the environment. *)

Module Syntax (Alphabet:Typ) (Names:Typ).

Notation Sigma    := Alphabet.t.
Notation SigmaSet := (Ensemble Sigma).

Notation name     := Names.t.

(* Events and sets of events.

   Note that sets of events (here the type "channels") don't include tau.
   We use these sets as elements of the syntax, and you can't write the special
   event tau in CSPm.
*)

Inductive Event : Type :=
  | EvSigma : Sigma -> Event
  | EvTau   : Event
.


(* Now the type of Procs.

   This is a somewhat stripped down version of CSP.  For example, it's missing
   interrupt.  But it's what I need for now, I think.

   The only real subtlety is recursion and variables.

   For variables, we distinguish bound variables from free variables.  This is
   roughly in the "locally nameless" style made popular at Penn, though our
   binders are never "opened" with new free variables, always other procs.

   Recursion occurs in two ways.  First, the direct recursion of PMu.  Second,
   definitions associated with free variables are allowed to be (mutually)
   recursive.  The later enables the representation of variables.
  *)

Inductive Proc : Type :=
  | PBVar      : nat -> Proc
  | PFVar      : name -> Proc
  | PStop      : Proc
  | PPrefix    : Sigma -> Proc -> Proc
  | PHide      : Proc -> SigmaSet -> Proc
  | PGenPar    : Proc -> SigmaSet -> Proc -> Proc
  | PIntChoice : Proc -> Proc -> Proc
  | PExtChoice : Proc -> Proc -> Proc
  | PMu        : Proc -> Proc
.

Reserved Notation "{ n ~> a }" (at level 60, no associativity).

(* lift p m  -  adds 1 to every bound var in p which is at least as big as m.
 *)
Fixpoint lift (p : Proc) (m : nat) : Proc := 
  match p with
  | PBVar n => PBVar (match nat_compare n m with
                      | Lt => n
                      | _  => S n
                      end)
  | PFVar n          => PFVar n
  | PStop            => PStop
  | PPrefix c p'     => PPrefix c (lift p' m)
  | PHide p' cs      => PHide (lift p' m) cs
  | PGenPar p1 cs p2 => PGenPar (lift p1 m) cs (lift p2 m)
  | PIntChoice p1 p2 => PIntChoice (lift p1 m) (lift p2 m)
  | PExtChoice p1 p2 => PExtChoice (lift p1 m) (lift p2 m)
  | PMu p'           => PMu (lift p' (S m))
  end.

Fixpoint open (n:nat) (u:Proc) (p:Proc) {struct p} : Proc :=
  match p with
  | PBVar n'          => match nat_compare n' n with
                         | Lt => PBVar n'
                         | Eq => u
                         | Gt => PBVar (pred n')
                         end
  | PFVar n          => PFVar n
  | PStop            => PStop
  | PPrefix c p'     => PPrefix c ({n ~> u}p')
  | PHide p' cs      => PHide ({n ~> u}p') cs
  | PGenPar p1 cs p2 => PGenPar ({n ~> u} p1) cs ({n ~> u} p2)
  | PIntChoice p1 p2 => PIntChoice ({n ~> u} p1) ({n ~> u} p2)
  | PExtChoice p1 p2 => PExtChoice ({n ~> u} p1) ({n ~> u} p2)
  | PMu p'           => PMu ({S n ~> lift u 0}p')
  end
  where "{ n ~> a }" := (open n a).

(* Count the number of free variables *)
Fixpoint fbvs (p : Proc) : nat :=
  match p with
  | PBVar n          => S n
  | PFVar n          => 0
  | PStop            => 0
  | PPrefix c p'     => fbvs p'
  | PHide p' _       => fbvs p'
  | PGenPar p1 _ p2  => max (fbvs p1) (fbvs p2)
  | PIntChoice p1 p2 => max (fbvs p1) (fbvs p2)
  | PExtChoice p1 p2 => max (fbvs p1) (fbvs p2)
  | PMu p'           => pred (fbvs p')
  end.

Ltac crush_compare :=
  match goal with
    | [ |- context [nat_compare ?n ?m] ] =>
      is_var n; is_var m;
      let nc := fresh "nc" in
      remember (nat_compare n m) as nc;
      destruct nc; simpl; eauto
    | [ |- context [nat_compare ?n (S ?m)] ] =>
      is_var n; is_var m;
      let nc := fresh "nc" in
      remember (nat_compare n (S m)) as nc;
      destruct nc; simpl; eauto
    | [ |- context [nat_compare (S ?n) ?m] ] =>
      is_var n; is_var m;
      let nc := fresh "nc" in
      remember (nat_compare (S n) m) as nc;
      destruct nc; simpl; eauto 
    | [ |- context [nat_compare (pred ?n) ?m] ] =>
      is_var n; is_var m;
      let nc := fresh "nc" in
      remember (nat_compare (pred n) m) as nc;
      destruct nc; simpl; eauto 
    | [ |- context [match ?m with | _ => _ end ] ] =>
      is_var m; destruct m; simpl; eauto 
    | [ HContra : Eq = Lt |- _ ] => inversion HContra
    | [ HContra : Lt = Eq |- _ ] => inversion HContra
    | [ HContra : Lt = Gt |- _ ] => inversion HContra
    | [ HContra : Gt = Lt |- _ ] => inversion HContra
    | [ HEq : Eq = nat_compare _ _ |- _ ] => 
      apply eq_sym in HEq; apply nat_compare_eq in HEq; (try subst)
    | [ HGt : Gt = nat_compare _ _ |- _ ] => 
      apply eq_sym in HGt; apply nat_compare_Gt_gt in HGt; (try subst);
      try solve [ omega ]
    | [ HLt : Lt = nat_compare _ _ |- _ ] => 
      apply eq_sym in HLt; apply nat_compare_Lt_lt in HLt; (try subst);
      try solve [ omega ]
  end.


Theorem lift_lift_commute : forall p n m,
      n <= m
   -> lift (lift p m) n = lift (lift p n) (S m).
Proof.
  induction p; intros; simpl in *; eauto; 
  try solve [
     repeat (match goal with
     | [ IH : forall _ _, _ -> (lift (lift ?p _) _) = _
       |- context[(lift (lift ?p _) _)]] =>
      rewrite IH; simpl; eauto; try omega; clear IH
     end)];
  repeat crush_compare.
Qed.

Theorem open_lift_commute : forall p n m u,
      m <= n                           
   -> {S n ~> lift u m} (lift p m) = lift ({n ~> u} p) m.
Proof.
  induction p; intros; simpl in *; eauto; try solve
    [repeat (match goal with
     | [ IH : forall _ _ _, _ -> ({_ ~> _} (lift ?p _)) = _ 
       |- context[{_ ~> _} (lift ?p _)]] =>
      rewrite IH; simpl; eauto
     end)].

  - repeat (crush_compare).
    + destruct n; simpl; eauto.  inversion Heqnc.
    + destruct n; simpl; eauto.  inversion Heqnc.
  - f_equal.
    rewrite <- IHp; try omega.
    rewrite lift_lift_commute; eauto; try omega.
Qed.

Theorem open_under_lift : forall p n u,
  {n ~> u} (lift p n) = p.
Proof.
  induction p; intros; simpl in *; eauto; try solve
    [repeat (match goal with
     | [ IH : forall _ _, ({_ ~> _} (lift ?p _)) = _ 
       |- context[{_ ~> _} (lift ?p _)]] =>
      rewrite IH; simpl; eauto
     end)].

  repeat (crush_compare); try omega.
Qed.

Notation Trace := (list Sigma).


Notation Closed p := (fbvs p = 0).

Lemma closed_inv_genpar_1 : forall p1 cs p2, Closed (PGenPar p1 cs p2) -> Closed p1.
Proof.
  intros p1 cs p2 H; simpl in H. 
  assert (fbvs p1 <= 0) by (rewrite <- H; eauto using le_max_l).
  omega.
Qed.

Lemma closed_inv_genpar_2 : forall p1 cs p2, Closed (PGenPar p1 cs p2) -> Closed p2.
Proof.
  intros p1 cs p2 H; simpl in H. 
  assert (fbvs p2 <= 0) by (rewrite <- H; eauto using le_max_r).
  omega.
Qed.

Lemma closed_inv_intchoice_1 : forall p1 p2, Closed (PIntChoice p1 p2) -> Closed p1.
Proof.
  intros p1 p2 H; simpl in H. 
  assert (fbvs p1 <= 0) by (rewrite <- H; eauto using le_max_l).
  omega.
Qed.

Lemma closed_inv_intchoice_2 : forall p1 p2, Closed (PIntChoice p1 p2) -> Closed p2.
Proof.
  intros p1 p2 H; simpl in H. 
  assert (fbvs p2 <= 0) by (rewrite <- H; eauto using le_max_r).
  omega.
Qed.

Lemma closed_inv_extchoice_1 : forall p1 p2, Closed (PExtChoice p1 p2) -> Closed p1.
Proof.
  intros p1 p2 H; simpl in H. 
  assert (fbvs p1 <= 0) by (rewrite <- H; eauto using le_max_l).
  omega.
Qed.

Lemma closed_inv_extchoice_2 : forall p1 p2, Closed (PExtChoice p1 p2) -> Closed p2.
Proof.
  intros p1 p2 H; simpl in H. 
  assert (fbvs p2 <= 0) by (rewrite <- H; eauto using le_max_r).
  omega.
Qed.

Hint Extern 3 => 
  match goal with
  | [ H : Closed (PGenPar ?p1 _ _) |- Closed ?p1 ] =>
    apply closed_inv_genpar_1 in H; exact H
  | [ H : Closed (PGenPar _ _ ?p2) |- Closed ?p2 ] =>
    apply closed_inv_genpar_2 in H; exact H
  | [ H : Closed (PIntChoice ?p1 _) |- Closed ?p1 ] =>
    apply closed_inv_intchoice_1 in H; exact H
  | [ H : Closed (PIntChoice _ ?p2) |- Closed ?p2 ] =>
    apply closed_inv_intchoice_2 in H; exact H
  | [ H : Closed (PExtChoice ?p1 _) |- Closed ?p1 ] =>
    apply closed_inv_extchoice_1 in H; exact H
  | [ H : Closed (PExtChoice _ ?p2) |- Closed ?p2 ] =>
    apply closed_inv_extchoice_2 in H; exact H
  end.

Hint Extern 1 => 
  match goal with
  | [ H : Closed (PBVar _) |- _ ] => simpl in H; inversion H
  end.

End Syntax.

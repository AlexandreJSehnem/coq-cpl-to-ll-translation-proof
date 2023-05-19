From NanoYalla Require Import macrollcut.
Import LLNotations.
From CPL Require Export a_base.
Require Export Bool.
Export ListNotations.
Set Implicit Arguments.

(** * Definitions 

definition of Propositional Formulas*)
Inductive PropF : Set :=
 | Var : Atom -> PropF
 | Bot : PropF
 | Conj : PropF -> PropF -> PropF
 | Disj : PropF -> PropF -> PropF
 | Impl : PropF -> PropF -> PropF
 | Neg  : PropF -> PropF
.

Notation "# P" := (Var P) (at level 1) : My_scope.
Notation "A ∨ B" := (Disj A B) (at level 15, right associativity) : My_scope.
Notation "A ∧ B" := (Conj A B) (at level 15, right associativity) : My_scope.
Notation "A → B" := (Impl A B) (at level 16, right associativity) : My_scope.
Notation "⊥" := Bot (at level 0)  : My_scope.
(*Definition Neg A := A → ⊥.*)
Notation "¬ A" := (Neg A) (at level 5) : My_scope.
Definition Top := ¬⊥.
Notation "⊤" := Top (at level 0) : My_scope.
Definition BiImpl A B := (A→B)∧(B→A).
Notation "A ↔ B" := (BiImpl A B) (at level 17, right associativity) : My_scope.

(** Validness *)

(** Valuations are maps PropVars -> bool sending ⊥ to false*)
Fixpoint TrueQ v A : bool := match A with
 | # P   => v P
 | ⊥     => false
 | B ∨ C => (TrueQ v B) || (TrueQ v C)
 | B ∧ C => (TrueQ v B) && (TrueQ v C)
 | B → C => (negb (TrueQ v B)) || (TrueQ v C)
 | ¬ B   => negb (TrueQ v B)
end.
Definition Satisfies v Γ := forall A, In A Γ -> Is_true (TrueQ v A).
Definition Models Γ A := forall v,Satisfies v Γ->Is_true (TrueQ v A).
Notation "Γ ⊨ A" := (Models Γ A) (at level 80).
Definition Valid A := [] ⊨ A.

(** Provability *)

Reserved Notation "Γ \- A" (at level 80).
Inductive Nc : list PropF-> PropF->Prop :=
| Nax   : forall Γ A  ,    In A Γ                           -> Γ \- A
| ImpI  : forall Γ A B,  A::Γ \- B                           -> Γ \- A → B
| ImpE  : forall Γ A B,     Γ \- A → B -> Γ \- A              -> Γ \- B
| BotC  : forall Γ A  , ¬A::Γ \- ⊥                              -> Γ \- A
| AndI  : forall Γ A B,     Γ \- A     -> Γ \- B              -> Γ \- A∧B
| AndE1 : forall Γ A B,     Γ \- A∧B                        -> Γ \- A
| AndE2 : forall Γ A B,     Γ \- A∧B                        -> Γ \- B
| OrI1  : forall Γ A B,     Γ \- A                           -> Γ \- A∨B
| OrI2  : forall Γ A B,     Γ \- B                           -> Γ \- A∨B
| OrE   : forall Γ A B C,   Γ \- A∨B -> A::Γ \- C -> B::Γ \- C -> Γ \- C
where "Γ \- A" := (Nc Γ A) : My_scope.

Fixpoint cpl_to_ll (a: PropF) : formula :=
match a with
  | Var A => wn (oc (var A))
  | Disj A B => parr (cpl_to_ll A) (cpl_to_ll B)
  | Neg A => wn (dual (cpl_to_ll A))
  | Impl A B => parr (wn (dual (cpl_to_ll A))) (cpl_to_ll B)
  | Bot => bot
  | Conj A B => wn( dual ( parr (wn (dual(cpl_to_ll A))) (wn (dual(cpl_to_ll B)))))
end.

Definition Provable A := [] \- A.

Fixpoint dual_set_cpl_to_ll (a: list PropF) : list formula :=
match a with
  | [] => []
  | A::t => (wn (dual (cpl_to_ll A)))::(dual_set_cpl_to_ll t)
end.

Require Import Equality.


(*Lemma to remove dual_set_cpl_to_ll when there is an axiom*)
Lemma remove_wn_dual_set: forall Γ A, ll ((cpl_to_ll A)::[dual (cpl_to_ll A)]) -> ll ((cpl_to_ll A)::(dual_set_cpl_to_ll (A::Γ))).
Proof.
intros. induction Γ. 
  - simpl. apply (de_r_ext [cpl_to_ll A]). cbn_sequent. ax_expansion.
  - simpl. simpl in IHΓ. apply (wk_r_ext ((cpl_to_ll A)::[(wn(dual (cpl_to_ll A)))])); cbn_sequent. apply IHΓ.
Qed.

(*Lemma to remove dual_set_cpl_to_ll with only one element*)
Lemma remove_wn_dual_set': forall Γ A, ll ([wn(dual (cpl_to_ll A))]) -> ll (dual_set_cpl_to_ll (A::Γ)).
Proof.
intros. induction Γ. 
  - simpl. apply H.
  - simpl. simpl in IHΓ. apply (wk_r_ext ([(wn(dual (cpl_to_ll A)))])); cbn_sequent. apply IHΓ.
Qed.

(*Lemma to remove dual_set_cpl_to_ll when it is together with two distinct elements*)
Lemma remove_wn_dual_set'': forall A B p Γ, ll (A::[B]) -> ll (A::B::(dual_set_cpl_to_ll (p::Γ))).
Proof.
intros. induction Γ.
  - simpl. apply (wk_r_ext (A::[B])). cbn_sequent. apply H.
  - simpl. apply (wk_r_ext (A::(B)::[wn(dual(cpl_to_ll p))])). cbn_sequent. simpl in IHΓ. apply IHΓ. 
Qed.

Lemma remove_remove: forall Γ, ll [] -> ll (dual_set_cpl_to_ll Γ).
Proof.
intros. induction Γ.
  - simpl. apply H.
  - simpl. apply (wk_r_ext []). cbn_sequent. apply IHΓ.
Qed.

Theorem proof_cpl_to_ll: forall Γ A, Γ \- A -> (ll ((cpl_to_ll A)::(dual_set_cpl_to_ll Γ))).
Proof.
intros. dependent induction H.
  - induction Γ.
    + inversion H.
    + simpl. destruct H.
      * rewrite H. apply remove_wn_dual_set. ax_expansion.
      * apply IHΓ in H. apply (wk_r_ext [cpl_to_ll A]). cbn_sequent. apply H.
  - simpl. apply parr_r. simpl in IHNc. 
    replace ((wn (dual (cpl_to_ll A)))::(cpl_to_ll B)::(dual_set_cpl_to_ll Γ)) 
      with ([]++(wn (dual (cpl_to_ll A)))::[cpl_to_ll B]++(dual_set_cpl_to_ll Γ)).
    + apply ex_transp_middle2 . cbn_sequent. apply IHNc.
    + cbn_sequent. reflexivity.
  - apply (cut_r_ext [] (parr (wn(dual (cpl_to_ll B))) (cpl_to_ll B))).
    + cbn_sequent. apply parr_r. apply (de_r_ext []). cbn_sequent. ax_expansion.
    + cbn_sequent. simpl. apply (tens_r_ext (dual_set_cpl_to_ll Γ)).
      * simpl. apply (oc_r_ext [] (cpl_to_ll B) []); cbn_sequent.
induction Γ.
    + simpl. apply (cut_r_ext [cpl_to_ll B] (wn(dual (cpl_to_ll A)))).
      * simpl in IHNc1. simpl. apply (ex_perm_r [1; 0] [(wn (dual (cpl_to_ll A))); (cpl_to_ll B)]).
        replace ([(wn (dual (cpl_to_ll A))); (cpl_to_ll B)])
          with ([parr (wn (dual (cpl_to_ll A))) (cpl_to_ll B)]).
        { apply IHNc1. } { apply parr_r.


 induction Γ.
    + simpl. replace ([cpl_to_ll B]) with ([cpl_to_ll B]++[]).
        * apply (cut_r_ext [cpl_to_ll B] (dual (cpl_to_ll A))).
          { cbn_sequent. apply (ex_perm_r [1; 0] [(dual (cpl_to_ll A)); (cpl_to_ll B)]); cbn_sequent.


(**The Theorems we are going to prove*)
Definition Prop_Soundness := forall A,Provable A->Valid A.
Definition Prop_Completeness := forall A,Valid A->Provable A.

(** * Theorems *)

Ltac mp := eapply ImpE.
Ltac AddnilL := match goal with 
| |- _ ?Γ _ => change Γ with ([]++Γ)
end.
Ltac in_solve := intros;repeat 
 (eassumption
||match goal with 
   | H:In _ (_::_) |- _ => destruct H;[subst;try discriminate|]
   | H:In _ (_++_) |- _ => apply in_app_iff in H as [];subst
   | |- In _ (_++_) => apply in_app_iff;(left;in_solve;fail)||(right;in_solve;fail) 
  end
||(constructor;reflexivity)
||constructor 2).
Ltac is_ass := econstructor;in_solve.

Ltac case_bool v A := let HA := fresh "H" in
(case_eq (TrueQ v A);intro HA;try rewrite HA in *;simpl in *;try trivial;try contradiction).

Local Ltac prove_satisfaction :=
intros ? K;destruct K;[subst;simpl;
match goal with
| [ H : TrueQ _ _ = _  |-  _ ] => rewrite H
end;exact I|auto].

Lemma PropFeq_dec : forall (x y : PropF), {x = y}+{x <> y}.
induction x;destruct y;try (right;discriminate);
 try (destruct (IHx1 y1);[destruct (IHx2 y2);[left;f_equal;assumption|]|];
  right;injection;intros;contradiction).
 destruct (Varseq_dec p p0).
   left;f_equal;assumption.
   right;injection;intro;contradiction.
 left;reflexivity.
Qed.

Lemma Excluded_Middle : forall Γ A, Γ \- A∨¬A.
intros;apply BotC;mp;[is_ass|apply OrI2;apply ImpI;mp;[is_ass|apply OrI1;is_ass]].
Qed.

Lemma weakening2 : forall Γ A, Γ \- A -> forall Δ, (forall B, In B Γ -> In B Δ) -> Δ \- A.
induction 1;[constructor|constructor 2|econstructor 3|constructor 4|constructor 5|econstructor 6
|econstructor 7|constructor 8|constructor 9|econstructor 10];try eauto;
[apply IHNc..|apply IHNc2|try apply IHNc3];intros;in_solve;eauto.
Qed.

Lemma weakening : forall Γ Δ A, Γ \- A -> Γ++Δ \- A.
intros;eapply weakening2;[eassumption|in_solve].
Qed.

Lemma deduction : forall Γ A B, Γ \- A → B -> A::Γ \- B.
intros;eapply ImpE with A;[eapply weakening2;[eassumption|in_solve]|is_ass].
Qed.

Lemma prov_impl : forall A B, Provable (A → B)->forall Γ, Γ \- A -> Γ \- B.
intros. mp. 
  AddnilL;apply weakening. apply H.
  assumption. 
Qed.

(* This tactic applies prov_impl in IH (apply prov_impl in IH doesn't work, because I want to keep the Γ quantified)*)
Ltac prov_impl_in IH := let H := fresh "K" in
try (remember (prov_impl IH) as H eqn:HeqH;clear IH HeqH).

(** Soundness *)

Theorem Soundness_general : forall A Γ, Γ \- A -> Γ ⊨ A.
intros A Γ H0 v;induction H0;simpl;intros;auto;
 try simpl in IHNc;try simpl in IHNc1;try simpl in IHNc2;
  case_bool v A;try (case_bool v B;fail);
   try (apply IHNc||apply IHNc2;prove_satisfaction);
    case_bool v B;apply IHNc3;prove_satisfaction.
Qed.

Theorem Soundness : Prop_Soundness.
intros ? ? ? ?;eapply Soundness_general;eassumption.
Qed.


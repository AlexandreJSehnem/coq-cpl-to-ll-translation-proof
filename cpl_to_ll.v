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
| ImpE  : forall Γ Δ A B,     Γ \- A → B -> Δ \- A              -> Δ++Γ \- B
| BotC  : forall Γ A  , ¬A::Γ \- ⊥                              -> Γ \- A
| AndI  : forall Γ Δ A B,     Γ \- A     -> Δ \- B              -> Δ++Γ \- A∧B
| AndE1 : forall Γ A B,     Γ \- A∧B                        -> Γ \- A
| AndE2 : forall Γ A B,     Γ \- A∧B                        -> Γ \- B
| OrI1  : forall Γ A B,     Γ \- A                           -> Γ \- A∨B
| OrI2  : forall Γ A B,     Γ \- B                           -> Γ \- A∨B
| OrE   : forall Γ Δ Δ' A B C,   Γ \- A∨B -> A::Δ \- C -> B::(Δ') \- C -> Γ++Δ++(Δ') \- C
where "Γ \- A" := (Nc Γ A) : My_scope.

Definition Provable A := [] \- A.

(**The Theorems we are going to prove*)
Definition Prop_Soundness := forall A,Provable A->Valid A.
Definition Prop_Completeness := forall A,Valid A->Provable A.

Fixpoint cpl_to_ll (a: PropF) : formula :=
match a with
  | Var A => wn (oc (var A))
  | Disj A B => parr (cpl_to_ll A) (cpl_to_ll B)
  | Impl A B => parr (wn (dual (cpl_to_ll A))) (cpl_to_ll B)
  | Neg A => wn (dual (cpl_to_ll A))
  | Bot => zero
  | Conj A B => wn( dual ( parr (wn (dual(cpl_to_ll A))) (wn (dual(cpl_to_ll B)))))
end.

Axiom parr_oplus_eq a b: forall a b:formula, (parr a b) = (wn(aplus (oc a) (oc b))).

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

Lemma duplicate_set_element: forall A Γ, ll ((wn (dual (cpl_to_ll A)))::((wn (dual (cpl_to_ll A))))::(dual_set_cpl_to_ll (A::Γ))) -> ll (dual_set_cpl_to_ll (A::Γ)).
Proof.
intros. simpl. apply co_r. apply co_r. apply H.
Qed.

Lemma split_tr_set: forall Δ Γ, dual_set_cpl_to_ll (Δ ++ Γ) = (dual_set_cpl_to_ll (Δ)++dual_set_cpl_to_ll (Γ)).
Proof.
intros. induction Δ.
- simpl. reflexivity.
- simpl. rewrite IHΔ. reflexivity.
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
(*Começo da prova de eliminação da implicação*)
  - rewrite split_tr_set.
    apply (cut_r_ext ((cpl_to_)) (parr (wn(dual (cpl_to_ll A))) (cpl_to_ll B)) [cpl_to_ll B]).
      * simpl in IHNc1. simpl. apply IHNc1.
      * cbn_sequent. apply (tens_r_ext []). 
        { cbn_sequent. apply (oc_r_ext [] (cpl_to_ll A) []); cbn_sequent. simpl in IHNc2. apply IHNc2. }
        { ax_expansion. }
    + simpl.
  admit. (*-> elim*)
(*Começo da prova de eliminação da negação*)
  - apply (cut_r_ext [] (dual(zero))).
    + cbn_sequent. apply (top_r_ext []).
    + simpl. simpl in IHNc. rewrite <-(bidual (cpl_to_ll A)).
  admit. (*dual elim*)


(*Começo da prova de eliminação da negação*)
  - apply (cut_r_ext [] (dual(zero))).
    + cbn_sequent. apply (top_r_ext []).
    + simpl. simpl in IHNc. rewrite <-(bidual (cpl_to_ll A)).

(* Prova da eliminação do ^ 1*)
  - simpl in IHNc. apply (cut_r_ext [cpl_to_ll A] (?(!(cpl_to_ll A^)^ ⊗ !(cpl_to_ll B^)^))).
    + simpl. apply (de_r_ext [cpl_to_ll A]). apply (parr_r_ext [cpl_to_ll A]). 
      simpl. apply (de_r_ext [cpl_to_ll A]). cbn_sequent. apply (wk_r_ext ((cpl_to_ll A)::[dual(cpl_to_ll A)])).  
      cbn_sequent. ax_expansion.
    + 

Lemma duplicate_set: forall Γ, ll ((dual_set_cpl_to_ll (Γ))++(dual_set_cpl_to_ll (Γ))) -> ll (dual_set_cpl_to_ll (Γ)).
intros. induction Γ.
  - apply H.
  -  

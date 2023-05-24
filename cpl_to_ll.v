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

(** Provability *)

Reserved Notation "Γ \- A" (at level 80).
Inductive Nc : list PropF-> PropF->Prop :=
| Nax   : forall Γ A  ,    In A Γ                           -> Γ \- A
| ImpI  : forall Γ A B,  A::Γ \- B                           -> Γ \- A → B
| ImpE  : forall Γ Δ A B,     Γ \- A → B -> Δ \- A              -> Γ++Δ \- B
(*| BotC  : forall Γ A  , ¬A::Γ \- ⊥                              -> Γ \- A*)
| BotE  : forall Γ A,     Γ \- ⊥                            -> Γ \- A
| AndI  : forall Γ Δ A B,     Γ \- A     -> Δ \- B              -> Δ++Γ \- A∧B
| AndE1 : forall Γ A B,     Γ \- A∧B                        -> Γ \- A
| AndE2 : forall Γ A B,     Γ \- A∧B                        -> Γ \- B
| OrI1  : forall Γ A B,     Γ \- A                           -> Γ \- A∨B
| OrI2  : forall Γ A B,     Γ \- B                           -> Γ \- A∨B
| OrE   : forall Γ Δ Δ' A B C,   Γ \- A∨B -> A::Δ \- C -> B::(Δ') \- C -> Γ++Δ++(Δ') \- C
where "Γ \- A" := (Nc Γ A) : My_scope.

Definition Provable A := [] \- A.

(**The Theorems we are going to prove*)
(*Definition Prop_Soundness := forall A,Provable A->Valid A.*)

Fixpoint cpl_to_ll (a: PropF) : formula :=
match a with
  | Var A => var A
  | Disj A B => aplus (oc (cpl_to_ll A)) (oc(cpl_to_ll B))
  | Impl A B => parr (wn (dual (cpl_to_ll A))) (cpl_to_ll B)
  | Neg A => parr (wn (dual (cpl_to_ll A))) zero
  | Bot => zero
  | Conj A B => awith(cpl_to_ll A) (cpl_to_ll B)
end.


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

Lemma split_tr_set: forall Δ Γ, dual_set_cpl_to_ll (Δ ++ Γ) = (dual_set_cpl_to_ll (Δ)++dual_set_cpl_to_ll (Γ)).
Proof.
intros. induction Δ.
- simpl. reflexivity.
- simpl. rewrite IHΔ. reflexivity.
Qed.

Lemma remove_tr_set: forall Δ A, ll (A) -> ll (A++(dual_set_cpl_to_ll Δ)).
Proof.
intros. induction Δ.
  - simpl. rewrite app_nil_r. apply H.
  - simpl. apply (wk_r_ext A ). apply IHΔ.
Qed.

(* Gambiarra!  Deveria fazer para um conjunto A de formulas em vez de para uma unica*)
Lemma remove_and_intros': forall Δ Γ A, ll ((cpl_to_ll A)::(dual_set_cpl_to_ll Δ)) -> ll ((cpl_to_ll A)::(dual_set_cpl_to_ll Γ)++(dual_set_cpl_to_ll Δ)).
Proof.
intros. induction Γ.
  - simpl. apply H.
  - simpl. apply (wk_r_ext [(cpl_to_ll A)]). apply IHΓ.
Qed.

Lemma remove_and_intros'': forall Δ Γ A, ll ((cpl_to_ll A)::(dual_set_cpl_to_ll Γ)) -> ll ((cpl_to_ll A)::(dual_set_cpl_to_ll Γ)++(dual_set_cpl_to_ll Δ)).
Proof.
intros. induction Δ.
  - simpl. rewrite app_nil_r. apply H.
  - simpl. apply (wk_r_ext ((cpl_to_ll A ):: dual_set_cpl_to_ll Γ)). apply IHΔ.
Qed.

(* Gambiarra!  Deveria fazer para um conjunto A de formulas em vez de para duas*)
Lemma remove_or_elim': forall Δ Γ A C, ll ((?(cpl_to_ll A)^)::(cpl_to_ll C)::(dual_set_cpl_to_ll Δ)) -> ll ((?(cpl_to_ll A)^)::(cpl_to_ll C)::(dual_set_cpl_to_ll Γ)++(dual_set_cpl_to_ll Δ)).
Proof.
intros. induction Γ.
  - simpl. apply H.
  - simpl. apply (wk_r_ext [(?(cpl_to_ll A)^); (cpl_to_ll C)]). apply IHΓ.
Qed.

Lemma remove_or_elim'': forall Δ Γ A C, ll ((?(cpl_to_ll A)^)::(cpl_to_ll C)::(dual_set_cpl_to_ll Γ)) -> ll ((?(cpl_to_ll A)^)::(cpl_to_ll C)::(dual_set_cpl_to_ll Γ)++(dual_set_cpl_to_ll Δ)).
Proof.
intros. induction Δ.
  - simpl. rewrite app_nil_r. apply H.
  - simpl. apply (wk_r_ext ((?(cpl_to_ll A)^)::(cpl_to_ll C)::dual_set_cpl_to_ll Γ)). apply IHΔ.
Qed.

Lemma remove_oc_set: forall A Δ, ll ((cpl_to_ll A) :: (dual_set_cpl_to_ll Δ)) -> ll ((!(cpl_to_ll A)) :: (dual_set_cpl_to_ll Δ)).
Proof.
intros.
Admitted.

Theorem proof_cpl_to_ll: forall Γ A, Γ \- A -> (ll ((cpl_to_ll A)::(dual_set_cpl_to_ll Γ))).
Proof.
intros. dependent induction H.

(*Axioma*)
  - induction Γ.
    + inversion H.
    + simpl. destruct H.
      * rewrite H. apply remove_wn_dual_set. ax_expansion.
      * apply IHΓ in H. apply (wk_r_ext [cpl_to_ll A]). cbn_sequent. apply H.

(*Introdução da Implicação*)
  - simpl. apply parr_r. simpl in IHNc. 
    replace ((wn (dual (cpl_to_ll A)))::(cpl_to_ll B)::(dual_set_cpl_to_ll Γ)) 
      with ([]++(wn (dual (cpl_to_ll A)))::[cpl_to_ll B]++(dual_set_cpl_to_ll Γ)).
    + apply ex_transp_middle2 . cbn_sequent. apply IHNc.
    + cbn_sequent. reflexivity.

(*Eliminação da implicação*)
  - rewrite split_tr_set.
    replace ((cpl_to_ll B) :: (dual_set_cpl_to_ll Γ) ++ (dual_set_cpl_to_ll Δ))
      with ([]++(cpl_to_ll B) :: (dual_set_cpl_to_ll Γ) ++ (dual_set_cpl_to_ll Δ)).
    + apply ex_transp_middle2. cbn_sequent.
    apply (cut_r_ext (dual_set_cpl_to_ll Γ) (parr (wn(dual (cpl_to_ll A))) (cpl_to_ll B)) ((cpl_to_ll B)::(dual_set_cpl_to_ll Δ))).
      * simpl in IHNc1. 
        replace ((?(cpl_to_ll A)^ ⅋ (cpl_to_ll B)) :: (dual_set_cpl_to_ll Γ))
          with ([]++(?(cpl_to_ll A)^ ⅋ (cpl_to_ll B)) :: (dual_set_cpl_to_ll Γ)++[]) in IHNc1.
        { apply ex_transp_middle1 in IHNc1. apply IHNc1. }
        { simpl. rewrite app_nil_r. reflexivity. }
      * replace ((?(cpl_to_ll A)^ ⅋ (cpl_to_ll B))^ :: (cpl_to_ll B) :: (dual_set_cpl_to_ll Δ))
          with ([(?(cpl_to_ll A)^ ⅋ (cpl_to_ll B))^] ++ (cpl_to_ll B) :: (dual_set_cpl_to_ll Δ)++[]).
        { apply ex_transp_middle2. 
          replace ([(?(cpl_to_ll A)^ ⅋ (cpl_to_ll B))^] ++ (dual_set_cpl_to_ll Δ)++ [(cpl_to_ll B)])
            with ([]++((?(cpl_to_ll A)^ ⅋ (cpl_to_ll B))^) :: (dual_set_cpl_to_ll Δ)++ [(cpl_to_ll B)]).
            { apply ex_transp_middle2. simpl. apply (tens_r_ext (dual_set_cpl_to_ll Δ)).
              { simpl. cbn_sequent. 
                replace ((dual_set_cpl_to_ll Δ) ++ [!cpl_to_ll A])
                   with ([]++(dual_set_cpl_to_ll Δ)++(!cpl_to_ll A)::[]).
                { apply ex_transp_middle1. cbn_sequent. rewrite app_nil_r. admit. }
                { reflexivity. } }
              { ax_expansion. } }
            { reflexivity. } }
        { rewrite app_nil_r. reflexivity. }
     + reflexivity.

(* Prova da eliminação da Negação*)
  - simpl. simpl in IHNc. apply (cut_r_ext [(cpl_to_ll A)] (dual 0 )).
    + simpl. apply (top_r_ext [(cpl_to_ll A)]).
    + simpl. apply  IHNc.

(* Prova da introdução do E*)
  - simpl. rewrite split_tr_set. apply (with_r_ext []).
    + simpl. apply remove_and_intros'. apply IHNc1.
    + simpl. apply remove_and_intros''. apply IHNc2.

(* Prova 1 da eliminação do E*)
  - simpl in IHNc. apply (cut_r_ext [cpl_to_ll A] (dual (awith (cpl_to_ll A) (cpl_to_ll B))) (dual_set_cpl_to_ll Γ)).
    + simpl. apply (plus_r1_ext [cpl_to_ll A]). cbn_sequent. ax_expansion.
    + rewrite bidual. apply IHNc.

(* Prova 2 da eliminação do E*)
  - simpl in IHNc. apply (cut_r_ext [cpl_to_ll B] (dual (awith (cpl_to_ll A) (cpl_to_ll B))) (dual_set_cpl_to_ll Γ)).
    + simpl. apply (plus_r2_ext [cpl_to_ll B]). cbn_sequent. ax_expansion.
    + rewrite bidual. apply IHNc.

(* Prova 1 da introdução do OU*)
  - simpl. apply (plus_r1_ext []). cbn_sequent. admit.

(* Prova 2 da introdução do OU*)
  - simpl. apply (plus_r2_ext []). cbn_sequent. admit.

(* Prova da eliminação do OU*)
  - rewrite split_tr_set.
    replace (cpl_to_ll C :: dual_set_cpl_to_ll Γ ++ dual_set_cpl_to_ll (Δ ++ Δ'))
    with ([]++cpl_to_ll C :: dual_set_cpl_to_ll Γ ++ dual_set_cpl_to_ll (Δ ++ Δ')).
    + apply ex_transp_middle2. simpl. simpl in IHNc1. 
      apply (cut_r_ext (dual_set_cpl_to_ll Γ) (aplus (oc (cpl_to_ll A)) (oc (cpl_to_ll B))) ((cpl_to_ll C) :: dual_set_cpl_to_ll (Δ ++ Δ'))).
      * replace (dual_set_cpl_to_ll Γ ++ [!cpl_to_ll A ⊕ !cpl_to_ll B])
        with ([]++dual_set_cpl_to_ll Γ ++ (!cpl_to_ll A ⊕ !cpl_to_ll B)::[]).
        { apply ex_transp_middle1. simpl. rewrite app_nil_r. apply IHNc1. }
        { reflexivity. }
      * simpl. apply (with_r_ext []).
        { simpl. rewrite split_tr_set. apply remove_or_elim''. simpl in IHNc2.
          replace ((?(cpl_to_ll A)^ :: cpl_to_ll C :: dual_set_cpl_to_ll Δ))
          with ([]++[(?(cpl_to_ll A)^)] ++ cpl_to_ll C :: dual_set_cpl_to_ll Δ).
          { apply ex_transp_middle1. simpl. apply IHNc2. } reflexivity. }
        { simpl. rewrite split_tr_set. apply remove_or_elim'. simpl in IHNc3.
          replace ((?(cpl_to_ll B)^ :: cpl_to_ll C :: dual_set_cpl_to_ll Δ'))
          with ([]++[(?(cpl_to_ll B)^)] ++ cpl_to_ll C :: dual_set_cpl_to_ll Δ').
          { apply ex_transp_middle1. simpl. apply IHNc3. } reflexivity. }
    + reflexivity.
Admitted.


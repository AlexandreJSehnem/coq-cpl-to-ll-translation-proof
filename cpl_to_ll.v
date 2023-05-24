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
Inductive Ni : list PropF-> PropF->Prop :=
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
where "Γ \- A" := (Ni Γ A) : My_scope.

Definition Provable A := [] \- A.

(**The Theorems we are going to prove*)
(*Definition Prop_Soundness := forall A,Provable A->Valid A.*)

Fixpoint cbv (a: PropF) : formula :=
match a with
  | Var A => var A
  | Disj A B => aplus (oc (cbv A)) (oc(cbv B))
  | Impl A B => parr (wn (dual (cbv A))) (cbv B)
  | Neg A => parr (wn (dual (cbv A))) zero
  | Bot => zero
  | Conj A B => awith(cbv A) (cbv B)
end.


Fixpoint dual_set_cbv (a: list PropF) : list formula :=
match a with
  | [] => []
  | A::t => (wn (dual (cbv A)))::(dual_set_cbv t)
end.

Require Import Equality.


(*Lemma to remove dual_set_cbv when there is an axiom*)
Lemma remove_wn_dual_set: forall Γ A, ll ((cbv A)::[dual (cbv A)]) -> ll ((cbv A)::(dual_set_cbv (A::Γ))).
Proof.
intros. induction Γ. 
  - simpl. apply (de_r_ext [cbv A]). cbn_sequent. ax_expansion.
  - simpl. simpl in IHΓ. apply (wk_r_ext ((cbv A)::[(wn(dual (cbv A)))])); cbn_sequent. apply IHΓ.
Qed.

Lemma split_tr_set: forall Δ Γ, dual_set_cbv (Δ ++ Γ) = (dual_set_cbv (Δ)++dual_set_cbv (Γ)).
Proof.
intros. induction Δ.
- simpl. reflexivity.
- simpl. rewrite IHΔ. reflexivity.
Qed.

Lemma remove_tr_set: forall Δ A, ll (A) -> ll ((A)++(dual_set_cbv Δ)).
Proof.
intros. induction Δ.
  - simpl. rewrite app_nil_r. apply H.
  - simpl. apply (wk_r_ext A ). apply IHΔ.
Qed.

(* Gambiarra!  Deveria fazer para um conjunto A de formulas em vez de para uma unica*)
Lemma remove_and_intros': forall Δ Γ A, ll ((cbv A)::(dual_set_cbv Δ)) -> ll ((cbv A)::(dual_set_cbv Γ)++(dual_set_cbv Δ)).
Proof.
intros. induction Γ.
  - simpl. apply H.
  - simpl. apply (wk_r_ext [(cbv A)]). apply IHΓ.
Qed.

Lemma remove_and_intros'': forall Δ Γ A, ll ((cbv A)::(dual_set_cbv Γ)) -> ll ((cbv A)::(dual_set_cbv Γ)++(dual_set_cbv Δ)).
Proof.
intros. induction Δ.
  - simpl. rewrite app_nil_r. apply H.
  - simpl. apply (wk_r_ext ((cbv A ):: dual_set_cbv Γ)). apply IHΔ.
Qed.

(* Gambiarra!  Deveria fazer para um conjunto A de formulas em vez de para duas*)
Lemma remove_or_elim': forall Δ Γ A C, ll ((?(cbv A)^)::(cbv C)::(dual_set_cbv Δ)) -> ll ((?(cbv A)^)::(cbv C)::(dual_set_cbv Γ)++(dual_set_cbv Δ)).
Proof.
intros. induction Γ.
  - simpl. apply H.
  - simpl. apply (wk_r_ext [(?(cbv A)^); (cbv C)]). apply IHΓ.
Qed.

Lemma remove_or_elim'': forall Δ Γ A C, ll ((?(cbv A)^)::(cbv C)::(dual_set_cbv Γ)) -> ll ((?(cbv A)^)::(cbv C)::(dual_set_cbv Γ)++(dual_set_cbv Δ)).
Proof.
intros. induction Δ.
  - simpl. rewrite app_nil_r. apply H.
  - simpl. apply (wk_r_ext ((?(cbv A)^)::(cbv C)::dual_set_cbv Γ)). apply IHΔ.
Qed.


Lemma remove_oc_set: forall A Δ, ll ((cbv A) :: (dual_set_cbv Δ)) -> ll ((!(cbv A)) :: (dual_set_cbv Δ)).
Proof.
intros. destruct Δ.
  - simpl. simpl in H. apply (oc_r_ext [] (cbv A) []). apply H.
  - simpl. simpl in H. destruct dual_set_cbv.
      + apply (oc_r_ext [] (cbv A) [((cbv p)^)]). apply H.
      + admit.
Admitted.

Theorem proof_cbv: forall Γ A, Γ \- A -> (ll ((cbv A)::(dual_set_cbv Γ))).
Proof.
intros. dependent induction H.

(*Axioma*)
  - induction Γ.
    + inversion H.
    + simpl. destruct H.
      * rewrite H. apply remove_wn_dual_set. ax_expansion.
      * apply IHΓ in H. apply (wk_r_ext [cbv A]). cbn_sequent. apply H.

(*Introdução da Implicação*)
  - simpl. apply parr_r. simpl in IHNi. 
    replace ((wn (dual (cbv A)))::(cbv B)::(dual_set_cbv Γ)) 
      with ([]++(wn (dual (cbv A)))::[cbv B]++(dual_set_cbv Γ)).
    + apply ex_transp_middle2 . cbn_sequent. apply IHNi.
    + cbn_sequent. reflexivity.

(*Eliminação da implicação*)
  - rewrite split_tr_set.
    replace ((cbv B) :: (dual_set_cbv Γ) ++ (dual_set_cbv Δ))
      with ([]++(cbv B) :: (dual_set_cbv Γ) ++ (dual_set_cbv Δ)).
    + apply ex_transp_middle2. cbn_sequent.
    apply (cut_r_ext (dual_set_cbv Γ) (parr (wn(dual (cbv A))) (cbv B)) ((cbv B)::(dual_set_cbv Δ))).
      * simpl in IHNi1. 
        replace ((?(cbv A)^ ⅋ (cbv B)) :: (dual_set_cbv Γ))
          with ([]++(?(cbv A)^ ⅋ (cbv B)) :: (dual_set_cbv Γ)++[]) in IHNi1.
        { apply ex_transp_middle1 in IHNi1. apply IHNi1. }
        { simpl. rewrite app_nil_r. reflexivity. }
      * replace ((?(cbv A)^ ⅋ (cbv B))^ :: (cbv B) :: (dual_set_cbv Δ))
          with ([(?(cbv A)^ ⅋ (cbv B))^] ++ (cbv B) :: (dual_set_cbv Δ)++[]).
        { apply ex_transp_middle2. 
          replace ([(?(cbv A)^ ⅋ (cbv B))^] ++ (dual_set_cbv Δ)++ [(cbv B)])
            with ([]++((?(cbv A)^ ⅋ (cbv B))^) :: (dual_set_cbv Δ)++ [(cbv B)]).
            { apply ex_transp_middle2. simpl. apply (tens_r_ext (dual_set_cbv Δ)).
              { simpl. cbn_sequent. 
                replace ((dual_set_cbv Δ) ++ [!cbv A])
                   with ([]++(dual_set_cbv Δ)++(!cbv A)::[]).
                { apply ex_transp_middle1. cbn_sequent. rewrite app_nil_r. admit. }
                { reflexivity. } }
              { ax_expansion. } }
            { reflexivity. } }
        { rewrite app_nil_r. reflexivity. }
     + reflexivity.

(* Prova da eliminação da Negação*)
  - simpl. simpl in IHNi. apply (cut_r_ext [(cbv A)] (dual 0 )).
    + simpl. apply (top_r_ext [(cbv A)]).
    + simpl. apply  IHNi.

(* Prova da introdução do E*)
  - simpl. rewrite split_tr_set. apply (with_r_ext []).
    + simpl. apply remove_and_intros'. apply IHNi1.
    + simpl. apply remove_and_intros''. apply IHNi2.

(* Prova 1 da eliminação do E*)
  - simpl in IHNi. apply (cut_r_ext [cbv A] (dual (awith (cbv A) (cbv B))) (dual_set_cbv Γ)).
    + simpl. apply (plus_r1_ext [cbv A]). cbn_sequent. ax_expansion.
    + rewrite bidual. apply IHNi.

(* Prova 2 da eliminação do E*)
  - simpl in IHNi. apply (cut_r_ext [cbv B] (dual (awith (cbv A) (cbv B))) (dual_set_cbv Γ)).
    + simpl. apply (plus_r2_ext [cbv B]). cbn_sequent. ax_expansion.
    + rewrite bidual. apply IHNi.

(* Prova 1 da introdução do OU*)
  - simpl. apply (plus_r1_ext []). cbn_sequent. admit.

(* Prova 2 da introdução do OU*)
  - simpl. apply (plus_r2_ext []). cbn_sequent. admit.

(* Prova da eliminação do OU*)
  - rewrite split_tr_set.
    replace (cbv C :: dual_set_cbv Γ ++ dual_set_cbv (Δ ++ Δ'))
    with ([]++cbv C :: dual_set_cbv Γ ++ dual_set_cbv (Δ ++ Δ')).
    + apply ex_transp_middle2. simpl. simpl in IHNi1. 
      apply (cut_r_ext (dual_set_cbv Γ) (aplus (oc (cbv A)) (oc (cbv B))) ((cbv C) :: dual_set_cbv (Δ ++ Δ'))).
      * replace (dual_set_cbv Γ ++ [!cbv A ⊕ !cbv B])
        with ([]++dual_set_cbv Γ ++ (!cbv A ⊕ !cbv B)::[]).
        { apply ex_transp_middle1. simpl. rewrite app_nil_r. apply IHNi1. }
        { reflexivity. }
      * simpl. apply (with_r_ext []).
        { simpl. rewrite split_tr_set. apply remove_or_elim''. simpl in IHNi2.
          replace ((?(cbv A)^ :: cbv C :: dual_set_cbv Δ))
          with ([]++[(?(cbv A)^)] ++ cbv C :: dual_set_cbv Δ).
          { apply ex_transp_middle1. simpl. apply IHNi2. } reflexivity. }
        { simpl. rewrite split_tr_set. apply remove_or_elim'. simpl in IHNi3.
          replace ((?(cbv B)^ :: cbv C :: dual_set_cbv Δ'))
          with ([]++[(?(cbv B)^)] ++ cbv C :: dual_set_cbv Δ').
          { apply ex_transp_middle1. simpl. apply IHNi3. } reflexivity. }
    + reflexivity.
Admitted.

Theorem proof_cbv': forall Γ A, (ll ((cbv A)::(dual_set_cbv Γ))) -> Γ \- A.
Proof.
intros.
Admitted.


(* Começo tradução call-by-name *)
Fixpoint cbn (a: PropF) : formula :=
match a with
  | Var A => oc (var A)
  | Disj A B => aplus (cbv A) (cbv B)
  | Impl A B => oc (parr (dual (cbv A)) (cbv B))
  | Neg A => parr (wn (dual (cbv A))) zero
  | Bot => zero
  | Conj A B => tens (cbv A) (cbv B)
end.


Fixpoint dual_set_cbn (a: list PropF) : list formula :=
match a with
  | [] => []
  | A::t => (wn (dual (cbn A)))::(dual_set_cbn t)
end.

Lemma remove_cbn_set: forall Δ A, ll (A) -> ll (A++(dual_set_cbn Δ)).
Proof.
intros. induction Δ.
  - simpl. rewrite app_nil_r. apply H.
  - simpl. apply (wk_r_ext A ). apply IHΔ.
Qed.

(*Lemma to remove dual_set_cbv when there is an axiom*)
Lemma remove_wn_set_cbn: forall Γ A, ll ((cbn A)::[dual (cbn A)]) -> ll ((cbn A)::(dual_set_cbn (A::Γ))).
Proof.
intros. induction Γ. 
  - simpl. apply (de_r_ext [cbn A]). cbn_sequent. ax_expansion.
  - simpl. simpl in IHΓ. apply (wk_r_ext ((cbn A)::[(wn(dual (cbn A)))])); cbn_sequent. apply IHΓ.
Qed.

Lemma split_cbn_set: forall Δ Γ, dual_set_cbn (Δ ++ Γ) = (dual_set_cbn (Δ)++dual_set_cbn (Γ)).
Proof.
intros. induction Δ.
- simpl. reflexivity.
- simpl. rewrite IHΔ. reflexivity.
Qed.

Theorem proof_cbn: forall Γ A, Γ \- A -> (ll ((cbn A)::(dual_set_cbn Γ))).
Proof.
intros. induction H.
(* Axiom *)
  - induction Γ.
    + inversion H.
    + simpl. simpl in H. destruct H.
      * rewrite H. apply remove_wn_set_cbn. ax_expansion.
      * apply (wk_r_ext [(cbn A)]). apply IHΓ. apply H.
(* Introdução da implicação *)
  - simpl. admit.
(* Eliminação da implicação *)
  - simpl in IHNi1. rewrite split_cbn_set.
    replace ((cbn B) :: dual_set_cbn Γ ++ dual_set_cbn Δ)
    with (cbn B :: dual_set_cbn Γ ++ dual_set_cbn Δ)
    apply (cut_r_ext ((cbn B) :: dual_set_cbn Γ) (!(cbv A^ ⅋ cbv B)) (dual_set_cbn Δ)).
    + admit.
    + simpl. admit.
Admitted.



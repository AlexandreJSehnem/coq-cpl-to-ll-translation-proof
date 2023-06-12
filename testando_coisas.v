From NanoYalla Require Import macrollcut.
Import LLNotations.
From CPL Require Export a_base.
Require Export Bool.
Export ListNotations.
Set Implicit Arguments.

(** * Definitions 

definition of Intuitionistic Formulas*)
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
| Magic  : forall Γ A  , Γ \- A∨¬A
| Botc  : forall Γ A  , ¬A::Γ \- ⊥                              -> Γ \- A
(*| BotE  : forall Γ A,     Γ \- ⊥                            -> Γ \- A*)
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

Fixpoint cbv (a: PropF) : formula :=
match a with
  | Var A => var A
  | Disj A B => parr (wn (cbv A)) (wn (cbv B))
  | Impl A B => parr (wn (oc (dual (cbv A)))) (wn (cbv B))
  | Neg A => wn (oc (dual (cbv A)))
  | Bot => bot
  | Conj A B => awith (wn (cbv A)) (wn (cbv B))
end.

Fixpoint dual_set_cbv (a: list PropF) : list formula :=
match a with
  | [] => []
  | A::t => (wn (oc (dual (cbv A))))::(dual_set_cbv t)
end.

Require Import Equality.

(*Lemma to remove dual_set_cbv when there is an axiom*)
Lemma remove_wn_dual_set: forall Γ A, ll ((wn (cbv A))::[dual (cbv A)]) -> ll ((wn (cbv A))::(dual_set_cbv (A::Γ))).
Proof.
intros. simpl. induction Γ. 
  - simpl. apply (de_r_ext [? (cbv A)]). cbn_sequent. ax_expansion.
  - simpl. simpl in IHΓ. apply (wk_r_ext ((? (cbv A))::[(wn(! (dual (cbv A))))])); cbn_sequent. apply IHΓ.
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
Lemma remove_and_intros': forall Δ Γ A, ll ((A)::(dual_set_cbv Δ)) -> ll ((A)::(dual_set_cbv Γ)++(dual_set_cbv Δ)).
Proof.
intros. induction Γ.
  - simpl. apply H.
  - simpl. apply (wk_r_ext [(A)]). apply IHΓ.
Qed.

Lemma remove_and_intros'': forall Δ Γ A, ll ((A)::(dual_set_cbv Γ)) -> ll ((A)::(dual_set_cbv Γ)++(dual_set_cbv Δ)).
Proof.
intros. induction Δ.
  - simpl. rewrite app_nil_r. apply H.
  - simpl. apply (wk_r_ext ((A ):: dual_set_cbv Γ)). apply IHΔ.
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

Fixpoint oc_set_cbv (a: list PropF) : list formula :=
match a with
  | [] => []
  | A::t => (oc (dual (cbv A)))::(oc_set_cbv t)
end.

Lemma map_equals_set: forall Δ, dual_set_cbv Δ = nanoll.map wn (oc_set_cbv Δ).
Proof.
intros. induction Δ.
  - reflexivity.
  - simpl. rewrite IHΔ. reflexivity.
Qed.

Lemma remove_oc_set: forall A Δ, ll ((A) :: (dual_set_cbv Δ)) -> ll ((!A) :: (dual_set_cbv Δ)).
Proof.
intros. rewrite map_equals_set. apply (oc_r_ext [] (A) (oc_set_cbv Δ)). simpl.
 rewrite <- map_equals_set. apply H.
Qed.


Theorem proof_cbv_cl: forall Γ A, Γ \- A -> (ll ((? (cbv A))::(dual_set_cbv Γ))).
Proof.
intros. dependent induction H.

(*Axioma*)
  - induction Γ.
    + inversion H.
    + simpl. destruct H.
      * rewrite H. apply remove_wn_dual_set. apply (de_r_ext []). ax_expansion.
      * apply IHΓ in H. apply (wk_r_ext [? (cbv A)]). cbn_sequent. apply H.

(*Introdução da Implicação*)
  - simpl. simpl in IHNc. apply (de_r_ext []). apply parr_r.
    replace (?!cbv A^ :: ?(cbv B) :: dual_set_cbv Γ)
      with ([]++(?!cbv A^)::[?(cbv B)]++(dual_set_cbv Γ)).
    + apply ex_transp_middle2 . cbn_sequent. apply IHNc.
    + cbn_sequent. reflexivity.

(*Eliminação da implicação*)
  - rewrite split_tr_set.
    replace (?(cbv B) :: (dual_set_cbv Γ) ++ (dual_set_cbv Δ))
      with ([]++?(cbv B) :: (dual_set_cbv Γ) ++ (dual_set_cbv Δ)).
    + apply ex_transp_middle2. cbn_sequent.
    apply (cut_r_ext (dual_set_cbv Γ) (?(cbv (A → B))) (?(cbv B)::(dual_set_cbv Δ))).
      * apply (ex_transp_middle1 []). rewrite app_nil_r. apply IHNc1.
      * simpl. rewrite map_equals_set. replace (!(!?(cbv A^)^ ⊗ !cbv B^) :: ?(cbv B) :: nanoll.map wn (oc_set_cbv Δ))
        with (!(!?(cbv A^)^ ⊗ !cbv B^) :: nanoll.map wn ((cbv B)::oc_set_cbv Δ)).
        { apply (oc_r_ext []). simpl. rewrite <- map_equals_set.
          replace ((!?(cbv A^)^ ⊗ !cbv B^) :: ?(cbv B) :: dual_set_cbv Δ)
          with ([(!?(cbv A^)^ ⊗ !cbv B^)] ++ ?(cbv B) :: dual_set_cbv Δ++[]).
        { apply ex_transp_middle2. simpl. apply (ex_transp_middle2 []). simpl. apply tens_r_ext.
          { apply (ex_transp_middle1 []). simpl. rewrite bidual. rewrite app_nil_r. apply remove_oc_set. apply IHNc2. }
          { ax_expansion. } }
        { rewrite app_nil_r. reflexivity. } } reflexivity.
    + reflexivity.

(* Prova da regra do terceiro excluido*)
  - simpl. apply (de_r_ext []). apply (parr_r_ext []). apply (de_r_ext [?(cbv A)]). simpl.
    replace ([?(cbv A)] ++ (?!cbv A^) :: dual_set_cbv Γ) with ([?(cbv A)] ++ (dual_set_cbv (A::Γ))).
    + apply remove_wn_dual_set. apply (de_r_ext []). ax_expansion.
    + simpl. reflexivity.

(* Prova da introdução da dupla negação*)
  - simpl. simpl in IHNc. apply (cut_r_ext [?(cbv A)] (dual(parr (?⟂) (?(!(!(?(cbv A^)^))))))).
    + simpl. rewrite bidual. replace [?(cbv A); !1 ⊗ !??!cbv A^] with ([]++?(cbv A)::[!1 ⊗ !??!cbv A^]++[]).
      * apply ex_transp_middle2. apply tens_r_ext. apply (oc_r_ext [] (1) []). simpl. apply one_r.
        apply (oc_r_ext [] (??!cbv A^) [cbv A]). apply (de_r_ext []). apply (de_r_ext []). ax_expansion.
      * reflexivity.
    + rewrite bidual. apply (parr_r_ext []). simpl. apply IHNc.

(* Prova da introdução do E*)
  - simpl. rewrite split_tr_set. apply (de_r_ext []). apply (with_r_ext []).
    + simpl. apply remove_and_intros'. apply IHNc1.
    + simpl. apply remove_and_intros''. apply IHNc2.

(* Prova 1 da eliminação do E*)
  - simpl in IHNc. apply (cut_r_ext [?(cbv A)] (dual (?(?(cbv A) ＆ ?(cbv B)))) (dual_set_cbv Γ)).
    + simpl. apply (oc_r_ext [cbv A] ((!cbv A^ ⊕ !cbv B^)) []). simpl. apply (plus_r1_ext [?(cbv A)]). ax_expansion.
    + rewrite bidual. apply IHNc.

(* Prova 2 da eliminação do E*)
  - simpl in IHNc. apply (cut_r_ext [?(cbv B)] (dual (?(?(cbv A) ＆ ?(cbv B)))) (dual_set_cbv Γ)).
    + simpl. apply (oc_r_ext [cbv B] ((!cbv A^ ⊕ !cbv B^)) []). simpl. apply (plus_r2_ext [?(cbv B)]). ax_expansion.
    + rewrite bidual. apply IHNc.

(* Prova 1 da introdução do OU*)
  - simpl. apply (de_r_ext []). simpl. apply (parr_r_ext []). apply (wk_r_ext [?(cbv A)]). apply IHNc.

(* Prova 2 da introdução do OU*)
  - simpl. apply (de_r_ext []). simpl. apply (parr_r_ext []). apply (wk_r_ext []). apply IHNc.

(* Prova da eliminação do OU*)
  - rewrite split_tr_set. apply (ex_transp_middle2 []). simpl.
      apply (cut_r_ext (dual_set_cbv Γ) (?(cbv (A ∨ B))) (?(cbv C) :: dual_set_cbv (Δ ++ Δ'))).
    + replace (dual_set_cbv Γ ++ [?(cbv (A ∨ B))])
        with ([]++dual_set_cbv Γ ++ (?(cbv (A ∨ B)))::[]).
      * apply ex_transp_middle1. simpl. rewrite app_nil_r. apply IHNc1.
      * reflexivity.
    + simpl. simpl in IHNc2. rewrite map_equals_set.
      replace (!(!cbv A^ ⊗ !cbv B^) :: ?(cbv C) :: nanoll.map wn (oc_set_cbv (Δ ++ Δ')))
      with (!(!cbv A^ ⊗ !cbv B^) :: nanoll.map wn ((cbv C):: oc_set_cbv (Δ ++ Δ'))).
      * apply (oc_r_ext []). simpl. rewrite <- map_equals_set.
        replace (!cbv A^ ⊗ !cbv B^ :: ?(cbv C) :: dual_set_cbv (Δ ++ Δ'))
        with ([]++[!cbv A^ ⊗ !cbv B^] ++ ?(cbv C) :: dual_set_cbv (Δ ++ Δ')).
        { apply ex_transp_middle1. rewrite split_tr_set. simpl.
          replace (?(cbv C) :: !cbv A^ ⊗ !cbv B^ :: dual_set_cbv Δ ++ dual_set_cbv Δ')
          with ([?(cbv C)] ++ !cbv A^ ⊗ !cbv B^ :: dual_set_cbv Δ ++ dual_set_cbv Δ').
          { apply ex_transp_middle2. apply (tens_r_ext ([?(cbv C)] ++ dual_set_cbv Δ )).
            {
Admitted.
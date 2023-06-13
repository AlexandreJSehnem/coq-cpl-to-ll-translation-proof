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
  | Var A => (wn (var A))
  | Disj A B => wn (aplus (oc(cbv A)) (oc(cbv B)))
  | Impl A B => wn (parr (wn (dual (cbv A))) (cbv B))
  | Neg A => wn (wn (dual (cbv A)))
  | Bot => wn bot
  | Conj A B => wn (awith (cbv A) (cbv B))
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
intros. simpl. induction Γ. 
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

Lemma remove_tr_set': forall Δ A B, ll ((A)::[B]) -> ll ((A)::(B)::(dual_set_cbv Δ)).
Proof.
intros. induction Δ.
  - simpl. apply H.
  - simpl. apply (wk_r_ext [A; B]). apply IHΔ.
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

Fixpoint oc_set_cbv (a: list PropF) : list formula :=
match a with
  | [] => []
  | A::t => (dual (cbv A))::(oc_set_cbv t)
end.

Lemma map_equals_set: forall Δ, dual_set_cbv Δ = nanoll.map wn (oc_set_cbv Δ).
Proof.
intros. induction Δ.
  - reflexivity.
  - simpl. rewrite IHΔ. reflexivity.
Qed.

Lemma remove_oc_set: forall A Δ, ll ((cbv A) :: (dual_set_cbv Δ)) -> ll ((!(cbv A)) :: (dual_set_cbv Δ)).
Proof.
intros. rewrite map_equals_set. apply (oc_r_ext [] (cbv A) (oc_set_cbv Δ)). simpl.
 rewrite <- map_equals_set. apply H.
Qed.

Lemma remove_oc_f: forall  Γ A B, ll ((B)::(cbv A)::(dual_set_cbv (Γ))) -> ll ((!B)::(cbv A)::(dual_set_cbv (Γ))).
Proof.
intros. induction A.
  - simpl. rewrite map_equals_set.
    replace ((!B) :: (?(var a)) :: nanoll.map wn (oc_set_cbv Γ))
    with ((!B) :: nanoll.map wn (var a::(oc_set_cbv Γ))).
    + apply (oc_r_ext [] (B)). simpl. simpl in H. rewrite <- map_equals_set. apply H.
    + reflexivity.
  - simpl. rewrite map_equals_set.
    replace ((!B) :: (?(⟂)) :: nanoll.map wn (oc_set_cbv Γ))
    with ((!B) :: nanoll.map wn ((⟂)::(oc_set_cbv Γ))).
    + apply (oc_r_ext [] (B)). simpl. simpl in H. rewrite <- map_equals_set. apply H.
    + reflexivity.
  - simpl. rewrite map_equals_set.
    replace ((!B) :: (?(cbv A1 ＆ cbv A2)) :: nanoll.map wn (oc_set_cbv Γ))
    with ((!B) :: nanoll.map wn ((cbv A1 ＆ cbv A2)::(oc_set_cbv Γ))).
    + apply (oc_r_ext [] (B)). simpl. simpl in H. rewrite <- map_equals_set. apply H.
    + reflexivity.
  - simpl. rewrite map_equals_set.
    replace ((!B) :: (?(!cbv A1 ⊕ !cbv A2)) :: nanoll.map wn (oc_set_cbv Γ))
    with ((!B) :: nanoll.map wn ((!cbv A1 ⊕ !cbv A2) ::(oc_set_cbv Γ))).
    + apply (oc_r_ext [] (B)). simpl. simpl in H. rewrite <- map_equals_set. apply H.
    + reflexivity.
  - simpl. rewrite map_equals_set.
    replace ((!B) :: (?(?(cbv A1)^ ⅋ cbv A2)) :: nanoll.map wn (oc_set_cbv Γ))
    with ((!B) :: nanoll.map wn ((?(cbv A1)^ ⅋ cbv A2) ::(oc_set_cbv Γ))).
    + apply (oc_r_ext [] (B)). simpl. simpl in H. rewrite <- map_equals_set. apply H.
    + reflexivity.
  - simpl. rewrite map_equals_set.
    replace ((!B) :: (?(?(cbv A)^)) :: nanoll.map wn (oc_set_cbv Γ))
    with ((!B) :: nanoll.map wn ((?(cbv A)^) ::(oc_set_cbv Γ))).
    + apply (oc_r_ext [] (B)). simpl. simpl in H. rewrite <- map_equals_set. apply H.
    + reflexivity.
Qed.

Lemma duplicate_cbv_cl: forall A B Γ, ll (B::(cbv A)::(cbv A)::(dual_set_cbv Γ)) -> ll (B::(cbv A)::(dual_set_cbv Γ)).
Proof.
intros. induction A.
  - simpl. apply (co_r_ext [B]). apply H.
  - simpl. apply (co_r_ext [B]). apply H.
  - simpl. apply (co_r_ext [B]). apply H.
  - simpl. apply (co_r_ext [B]). apply H.
  - simpl. apply (co_r_ext [B]). apply H.
  - simpl. apply (co_r_ext [B]). apply H.
Qed.


Theorem proof_cbv_cl: forall Γ A, Γ \- A -> (ll ((cbv A)::(dual_set_cbv Γ))).
Proof.
intros. dependent induction H.

(*Axioma*)
  - induction Γ.
    + inversion H.
    + simpl. destruct H.
      * rewrite H. apply remove_wn_dual_set. ax_expansion.
      * apply IHΓ in H. apply (wk_r_ext [cbv A]). cbn_sequent. apply H.

(*Introdução da Implicação*)
  - simpl. simpl in IHNc. apply (de_r_ext []). apply parr_r.
    replace ((wn (dual (cbv A)))::(cbv B)::(dual_set_cbv Γ)) 
      with ([]++(wn (dual (cbv A)))::[cbv B]++(dual_set_cbv Γ)).
    + apply ex_transp_middle2 . cbn_sequent. apply IHNc.
    + cbn_sequent. reflexivity.

(*Eliminação da implicação*)
  - rewrite split_tr_set.
    replace ((cbv B) :: (dual_set_cbv Γ) ++ (dual_set_cbv Δ))
      with ([]++(cbv B) :: (dual_set_cbv Γ) ++ (dual_set_cbv Δ)).
    + apply ex_transp_middle2. cbn_sequent.
    apply (cut_r_ext (dual_set_cbv Γ) (wn (parr (wn(dual (cbv A))) (cbv B))) ((cbv B)::(dual_set_cbv Δ))).
      * simpl in IHNc1. 
        replace ((wn (parr (wn(dual (cbv A))) (cbv B)))::(dual_set_cbv Γ))
          with ([]++(wn (parr (wn(dual (cbv A))) (cbv B))) :: (dual_set_cbv Γ)++[]) in IHNc1.
        { apply ex_transp_middle1 in IHNc1. apply IHNc1. }
        { simpl. rewrite app_nil_r. reflexivity. }
      * simpl. apply remove_oc_f.
        { replace ((!(cbv A^)^ ⊗ cbv B^) :: (cbv B) :: (dual_set_cbv Δ))
          with ([!(cbv A^)^ ⊗ cbv B^] ++ (cbv B) :: (dual_set_cbv Δ)++[]).
        { apply ex_transp_middle2. 
          replace ([!(cbv A^)^ ⊗ cbv B^] ++ (dual_set_cbv Δ)++ [(cbv B)])
            with ([]++(!(cbv A^)^ ⊗ cbv B^) :: (dual_set_cbv Δ)++ [(cbv B)]).
            { apply ex_transp_middle2. simpl. apply (tens_r_ext (dual_set_cbv Δ)).
              { simpl. cbn_sequent. 
                replace ((dual_set_cbv Δ) ++ [!cbv A])
                   with ([]++(dual_set_cbv Δ)++(!cbv A)::[]).
                { apply ex_transp_middle1. cbn_sequent. rewrite app_nil_r. apply remove_oc_set. apply IHNc2. }
                { reflexivity. } }
              { ax_expansion. } }
            { reflexivity. } }
        { rewrite app_nil_r. reflexivity. } }
     + reflexivity.

(* Prova da regra do terceiro excluido*)
  - simpl. apply (co_r_ext []). simpl. apply (de_r_ext []). simpl. apply remove_tr_set'.
    apply (plus_r2_ext []). simpl. apply (oc_r_ext [] (??(cbv A)^) [(!cbv A ⊕ !??(cbv A)^)]).
    simpl. apply (de_r_ext [??(cbv A)^]). apply (plus_r1_ext [??(cbv A)^]).
    apply (oc_r_ext [?(cbv A)^] (cbv A) []). simpl. apply (de_r_ext []). apply (de_r_ext []).
    ax_expansion.
(* Prova da introdução da dupla negação*)
  - simpl. simpl in IHNc. apply (cut_r_ext [cbv A] (dual ((parr (?⟂) (?(!(!(cbv A^)^))))))).
    + simpl. rewrite bidual. replace [cbv A; !1 ⊗ !??(cbv A)^] with ([]++(cbv A)::[!1 ⊗ !??(cbv A)^]++[]).
      * apply ex_transp_middle2. apply tens_r_ext. apply (oc_r_ext [] (1) []). simpl. apply one_r.
        apply (remove_oc_f []). apply (de_r_ext []). apply (de_r_ext []). ax_expansion.
      * reflexivity.
    + rewrite bidual. apply (parr_r_ext []). simpl. apply IHNc.

(* Prova da introdução do E*)
  - simpl. rewrite split_tr_set. apply (de_r_ext []). apply (with_r_ext []).
    + simpl. apply remove_and_intros'. apply IHNc1.
    + simpl. apply remove_and_intros''. apply IHNc2.

(* Prova 1 da eliminação do E*)
  - simpl in IHNc. apply (cut_r_ext [cbv A] (dual (? (awith (cbv A) (cbv B)))) (dual_set_cbv Γ)).
    + simpl. replace ((cbv A)::[(!(cbv A^ ⊕ cbv B^))]) with ([]++[cbv A]++(!((cbv A^) ⊕ (cbv B^)))::[]).
      * apply ex_transp_middle1. simpl. apply (remove_oc_f []). simpl. apply (plus_r1_ext []). cbn_sequent. ax_expansion.
      * simpl. reflexivity.
    + rewrite bidual. apply IHNc.

(* Prova 2 da eliminação do E*)
  - simpl in IHNc. apply (cut_r_ext [cbv B] (dual (? (awith (cbv A) (cbv B)))) (dual_set_cbv Γ)).
    + simpl. replace ((cbv B)::[(!(cbv A^ ⊕ cbv B^))]) with ([]++[cbv B]++(!((cbv A^) ⊕ (cbv B^)))::[]).
      * apply ex_transp_middle1. simpl. apply (remove_oc_f []). simpl. apply (plus_r2_ext []). cbn_sequent. ax_expansion.
      * simpl. reflexivity.
    + rewrite bidual. apply IHNc.

(* Prova 1 da introdução do OU*)
  - simpl. apply (de_r_ext []). apply (plus_r1_ext []). rewrite map_equals_set.
    apply (oc_r_ext []). rewrite <- map_equals_set. simpl. apply IHNc.

(* Prova 2 da introdução do OU*)
  - simpl. apply (de_r_ext []). apply (plus_r2_ext []). rewrite map_equals_set.
    apply (oc_r_ext []). rewrite <- map_equals_set. simpl. apply IHNc.

(* Prova da eliminação do OU*)
  - rewrite split_tr_set.
    replace (cbv C :: dual_set_cbv Γ ++ dual_set_cbv (Δ ++ Δ'))
    with ([]++cbv C :: dual_set_cbv Γ ++ dual_set_cbv (Δ ++ Δ')).
    + apply ex_transp_middle2. simpl. simpl in IHNc1. 
      apply (cut_r_ext (dual_set_cbv Γ) (?(!cbv A ⊕ !cbv B)) ((cbv C) :: dual_set_cbv (Δ ++ Δ'))).
      * replace (dual_set_cbv Γ ++ [?(!cbv A ⊕ !cbv B)])
        with ([]++dual_set_cbv Γ ++ (?(!cbv A ⊕ !cbv B))::[]).
        { apply ex_transp_middle1. simpl. rewrite app_nil_r. apply IHNc1. }
        { reflexivity. }
      * simpl. apply remove_oc_f. apply (with_r_ext []).
        { simpl. simpl in IHNc2. rewrite split_tr_set. apply remove_or_elim''.
          replace (?(cbv A)^ :: cbv C :: dual_set_cbv Δ)
          with ([]++[?(cbv A)^] ++ cbv C :: dual_set_cbv Δ).
          { apply (ex_transp_middle1 []). apply IHNc2. }
          { reflexivity. } } }
        { simpl. simpl in IHNc3. rewrite split_tr_set. apply remove_or_elim'.
          replace (?(cbv B)^ :: cbv C :: dual_set_cbv Δ')
          with ([]++[?(cbv B)^] ++ cbv C :: dual_set_cbv Δ').
          { apply (ex_transp_middle1 []). apply IHNc3. }
          { reflexivity. } }
    + reflexivity.
Qed.

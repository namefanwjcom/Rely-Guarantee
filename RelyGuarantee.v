(** * Smallstep: 小步操作语义 *)

Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.Init.Nat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.
From RG Require Import Maps.
From RG Require Import Imp.

Definition relation (X: Type) := X -> X -> Prop.

Definition deterministic {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Inductive multi {X:Type} (R: relation X) : relation X :=
  | multi_refl  : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Theorem multi_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> (multi R) x y.
Proof.
  intros X R x y H.
  apply multi_step with y. apply H. apply multi_refl.   Qed.

Theorem multi_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      multi R x y  ->
      multi R y z ->
      multi R x z.
Proof.
  intros X R x y z G H.
  induction G.
    - (* multi_refl *) assumption.
    - (* multi_step *)
      apply multi_step with y. assumption.
      apply IHG. assumption.  Qed.

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
  ~ exists t', R t t'.

Definition normalizing {X:Type} (R:relation X) :=
  forall t, exists t',
    (multi R) t t' /\ normal_form R t'.

(* ################################################################# *)
(** * Imp 的小步语义 *)
Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                (* <----- 新增 *)
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval st a1) =? (aeval st a2)
  | BLe a1 a2   => (aeval st a1) <=? (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  (* New: *)
  | CPar : com -> com -> com
  | CAwait: bexp -> com -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' b 'THEN' c1 'ELSE' c2 'FI'" :=
  (CIf b c1 c2) (at level 80, right associativity).
Notation "'PAR' c1 'WITH' c2 'END'" :=
  (CPar c1 c2) (at level 80, right associativity).
Notation "'AWAIT' b 'THEN' c 'END'" :=
  (CAwait b c) (at level 80, right associativity).

Reserved Notation " t '/' st '==>' t' '/' st' "
                  (at level 40, st at level 39, t' at level 39).

Inductive cstep : (com * state)  -> (com * state) -> Prop :=
  | CS_Ass : forall st i a,
      (i ::= a) / st ==> SKIP / st & { i --> aeval st a }
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st ==> c1' / st' ->
      (c1 ;; c2) / st ==> (c1' ;; c2) / st'
  | CS_SeqFinish : forall st c2,
      (SKIP ;; c2) / st ==> c2 / st
  | CS_IfTrue : forall st b c1 c2,
      beval st b = true ->
      (IFB b THEN c1 ELSE c2 FI) / st ==> c1 / st
  | CS_IfFalse : forall st b c1 c2,
      beval st b = false ->
      (IFB b THEN c1 ELSE c2 FI) / st ==> c2 / st
  | CS_While : forall st b c1,
          (WHILE b DO c1 END) / st
      ==> (IFB b THEN (c1;; (WHILE b DO c1 END)) ELSE SKIP FI) / st
  | CS_Par1 : forall st c1 c1' c2 st',
      c1 / st ==> c1' / st' ->
      (PAR c1 WITH c2 END) / st ==> (PAR c1' WITH c2 END) / st'
  | CS_Par2 : forall st c1 c2 c2' st',
      c2 / st ==> c2' / st' ->
      (PAR c1 WITH c2 END) / st ==> (PAR c1 WITH c2' END) / st'
  | CS_ParDone : forall st,
      (PAR SKIP WITH SKIP END) / st ==> SKIP / st
  | CS_Await : forall b c st st',
      beval st b = true ->
      multi cstep (c, st) (SKIP, st') ->
      (AWAIT b THEN c END) / st ==> SKIP / st'
  where " t '/' st '==>' t' '/' st' " := (cstep (t,st) (t',st')).

Definition cmultistep := multi cstep.

Notation " t '/' st '==>*' t' '/' st' " :=
   (multi cstep  (t,st) (t',st'))
   (at level 40, st at level 39, t' at level 39).

Inductive trans :=
  | notrans
  | ctrans
  | etrans.

Record config :=
  mkconfig
  {
    c : com;
    st : state;
    tr: trans;
  }.

Definition trace := list config.

Definition Assertion := state -> Prop.

Definition RG_Assertion := state -> state -> Prop.

Inductive valid_trace: trace ->  Prop :=
  | begin_valid c st :
      valid_trace [mkconfig c st notrans]
  | ctrans_valid c st c' st' tr l :
      c' / st' ==> c / st ->
      valid_trace (mkconfig c' st' tr :: l) ->
      valid_trace (mkconfig c st ctrans :: mkconfig c' st' tr :: l)
  | etrans_valid' c st st' tr l :
      valid_trace (mkconfig c st' tr :: l) ->
      valid_trace (mkconfig c st etrans :: mkconfig c st' tr :: l).

Inductive rely_hold: trace -> RG_Assertion -> Assertion ->  Prop :=
  | begin_rely c st rely (pre: Assertion) :
      pre st ->
      rely_hold [mkconfig c st notrans] rely pre
  | ctrans_rely c st c' st' tr l rely pre :
      c / st ==> c' / st' ->
      rely_hold (mkconfig c st tr :: l) rely pre ->
      rely_hold (mkconfig c' st' ctrans :: mkconfig c st tr :: l) rely pre
  | etrans_rely c st st' tr l (rely: RG_Assertion) pre :
      rely st st' ->
      rely_hold (mkconfig c st tr :: l) rely pre ->
      rely_hold (mkconfig c st' etrans :: mkconfig c st tr :: l) rely pre.

Lemma rely_hold_implies_valid_trace: forall l rely pre,
  rely_hold l rely pre -> valid_trace l.
Proof.
  intros. induction H; constructor; auto.
Qed.

Inductive guar_hold: trace -> RG_Assertion ->  Prop :=
  | begin_guar c st rely :
      guar_hold [mkconfig c st notrans] rely
  | ctrans_guar c st c' st' tr l (guar: RG_Assertion) :
      c / st ==> c' / st' ->
      guar st st' ->
      guar_hold (mkconfig c st tr :: l) guar ->
      guar_hold (mkconfig c' st' ctrans :: mkconfig c st tr :: l) guar
  | etrans_guar' c st l (guar: RG_Assertion) :
      guar_hold l guar ->
      guar_hold (mkconfig c st etrans :: l) guar.

Definition post_hold l post :=
  match l with
  | nil => False
  | h :: t => post h.(st)
  end.

Definition begin_with l co :Prop :=
  match l with
  | nil => False
  | h :: t=> h.(c) = co
  end.

Inductive end_with: trace -> com -> Prop :=
  | end_with_base c st tr: end_with [mkconfig c st tr] c
  | end_with_cons s h t: end_with t s -> end_with (h :: t) s.

Definition begin_with_config l (s: config) :Prop :=
  match l with
  | nil => False
  | h :: t => h = s
  end.

Inductive end_with_config: trace -> config -> Prop :=
  | end_with_base' s: end_with_config [s] s
  | end_with_cons' s h t: end_with_config t s -> end_with_config (h :: t) s.

Lemma end_with_config_implies_end_with: forall l c st,
  end_with_config l (mkconfig c st notrans) -> end_with l c.
Proof.
  intros. remember (mkconfig c0 st0 notrans) as s. induction H; subst; constructor; auto.
Qed.

Lemma separate_rely_pre: forall l c st rely (pre: Assertion),
  rely_hold l rely (fun st => True) -> end_with_config l (mkconfig c st notrans) ->
  pre st -> rely_hold l rely pre.
Proof.
  intros. induction H; inversion H0; simpl in *; subst; auto.
  - constructor; auto.
  - inversion H5.
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma separate_rely_pre': forall l c st rely (pre: Assertion),
  rely_hold l rely pre -> end_with_config l (mkconfig c st notrans) ->
  pre st /\ rely_hold l rely (fun st => True).
Proof.
  intros. induction H; inversion H0; simpl in *; subst.
  - split; auto. constructor; auto.
  - inversion H4.
  - destruct (IHrely_hold H5). split; auto. constructor; auto.
  - destruct (IHrely_hold H5). split; auto. constructor; auto.
Qed.

Definition rely_guarantee (pre post :Assertion) (c: com) (rely guar:RG_Assertion) : Prop :=
  forall l,
    end_with l c ->
    rely_hold l rely pre ->
    guar_hold l guar /\ (begin_with l SKIP -> post_hold l post).

(*Definition strongest_postcondition (pre: Assertion) c c': Assertion :=
  fun st' => forall st, c / st ==> c' / st' -> pre st.

Definition weakest_precondition (post: Assertion) c c' st': Assertion :=
  fun st => c / st ==> c' / st' -> post st'.

Inductive rely_guarantee': Assertion -> Assertion -> com -> RG_Assertion -> RG_Assertion -> Prop :=
  | rg_base pre post c rely guar:
      rely_guarantee pre post c rely guar ->
      rely_guarantee' pre post c rely guar
  | rg_com (pre post: Assertion) c c' (rely guar: RG_Assertion):
      (forall st st', c / st ==> c' / st' -> guar st st') ->
      rely_guarantee' (strongest_postcondition pre c c') post c' rely guar ->
      rely_guarantee' pre post c rely guar
  | rg_env (pre post: Assertion) c st st' (rely guar: RG_Assertion):
      rely st st' ->
      rely_guarantee' (fun st0 => pre st) post c rely guar ->
      rely_guarantee' pre post c rely guar.

Lemma rely_guarantee_equals_rely_guarantee': forall pre post c rely guar,
  rely_guarantee pre post c rely guar <-> rely_guarantee' pre post c rely guar.
Proof.
  split; intros.
  - constructor; auto.
  - induction H; auto; unfold rely_guarantee in *; intros.
    + assert (guar_hold (l ++ [mkconfig c0 st0 notrans]) guar /\
        (begin_with (l ++ [mkconfig c0 st0 notrans]) SKIP -> post_hold (l ++ [mkconfig c0 st0 notrans]) post)).
      apply IHrely_guarantee'. apply end_with_last.
*)
Definition assn_sub X a P : Assertion :=
  fun (st : state) =>
    P (st & { X  --> aeval st a }).

Definition stable_when (pre: Assertion) (rely: RG_Assertion) :Prop :=
  forall st st', pre st -> rely st st' -> pre st'.

Inductive rely_guarantee_proof: Assertion -> Assertion -> com -> RG_Assertion -> RG_Assertion -> Prop :=
  | RG_Skip: forall (pre post: Assertion) (rely guar: RG_Assertion),
      (forall st, pre st -> post st) ->
      stable_when pre rely ->
      stable_when post rely ->
      rely_guarantee_proof pre post SKIP rely guar
  | RG_Ass: forall (pre post: Assertion) x e (rely guar: RG_Assertion),
      (forall st, pre st -> assn_sub x e post st) ->
      (forall st st', pre st /\ (st' = st & { x --> aeval st e } \/ st' = st) -> guar st st') ->
      stable_when pre rely ->
      stable_when post rely ->
      rely_guarantee_proof pre post (x ::= e) rely guar
  | RG_Seq: forall (pre mid post: Assertion) c1 c2 (rely guar: RG_Assertion),
      (forall st, (SKIP;; c2) / st ==> c2 / st -> guar st st) ->
      rely_guarantee_proof pre mid c1 rely guar ->
      rely_guarantee_proof mid post c2 rely guar ->
      rely_guarantee_proof pre post (c1;; c2) rely guar
  | RG_If: forall (pre mid post: Assertion) b c1 c2 (rely guar: RG_Assertion),
      stable_when pre rely ->
      (forall c st st', (IFB b THEN c1 ELSE c2 FI) / st ==> c / st' -> guar st st') ->
      rely_guarantee_proof (fun st => pre st /\ beval st b = true) post c1 rely guar ->
      rely_guarantee_proof (fun st => pre st /\ beval st b = false) post c2 rely guar ->
      rely_guarantee_proof pre post (IFB b THEN c1 ELSE c2 FI) rely guar
  | RG_While: forall (pre post: Assertion) b c (rely guar: RG_Assertion),
      stable_when pre rely ->
      stable_when (fun st => beval st b = true) rely ->
      stable_when post rely ->
      (forall st, guar st st) ->
      (forall st, pre st /\ beval st b = false -> post st) ->
      rely_guarantee_proof (fun st => pre st /\ beval st b = true) pre c rely guar ->
      rely_guarantee_proof pre post (WHILE b DO c END) rely guar
  | RG_Await: forall (pre post: Assertion) b c (rely guar: RG_Assertion),
      stable_when pre rely ->
      stable_when post rely ->
      (forall st0, rely_guarantee_proof (fun st => pre st /\ beval st b = true /\ forall x, st x = st0 x)
        (fun st => post st /\ guar st0 st) c (fun st st' => st = st') (fun st st' => True)) ->
      rely_guarantee_proof pre post (AWAIT b THEN c END) rely guar
  | RG_Consequence: forall (pre pre1 post post1: Assertion) c (rely rely1 guar guar1: RG_Assertion),
      (forall st, pre st -> pre1 st) ->
      (forall st st', rely st st' -> rely1 st st') ->
      (forall st st', guar1 st st' -> guar st st') ->
      (forall st, post1 st -> post st) ->
      rely_guarantee_proof pre1 post1 c rely1 guar1 ->
      rely_guarantee_proof pre post c rely guar
  | RG_Par: forall (pre post1 post2: Assertion) c1 c2 (rely1 rely2 rely guar1 guar2 guar: RG_Assertion),
      (forall st, guar st st) ->
      (forall st, rely1 st st) ->
      (forall st, rely2 st st) ->
      (forall st st', rely st st' \/ guar1 st st' -> rely2 st st') ->
      (forall st st', rely st st' \/ guar2 st st' -> rely1 st st') ->
      (forall st st', guar1 st st' \/ guar2 st st' -> guar st st') ->
      rely_guarantee_proof pre post1 c1 rely1 guar1 ->
      rely_guarantee_proof pre post2 c2 rely2 guar2 ->
      rely_guarantee_proof pre (fun st => post1 st /\ post2 st) (PAR c1 WITH c2 END) rely guar.

Module Seq.

Inductive merge: com -> trace -> trace -> trace -> bool -> Prop :=
  | merge_begin c co st :
      merge co [mkconfig c st notrans] nil [mkconfig (c;; co) st notrans] true
  | merge_ctrans_before co c st c' st' tr l1 l :
      c / st ==> c' / st' ->
      merge co (mkconfig c st tr :: l1) nil (mkconfig (c;; co) st tr :: l) true ->
      merge co (mkconfig c' st' ctrans :: mkconfig c st tr :: l1) nil (mkconfig (c';; co) st' ctrans :: mkconfig (c;; co) st tr :: l) true
  | merge_etrans_before co c st st' tr l1 l :
      merge co (mkconfig c st tr :: l1) nil (mkconfig (c;; co) st tr :: l) true ->
      merge co (mkconfig c st' etrans :: mkconfig c st tr :: l1) nil (mkconfig (c;; co) st' etrans :: mkconfig (c;; co) st tr :: l) true
  | merge_join co st tr l1 l :
      merge co (mkconfig SKIP st tr :: l1) nil (mkconfig (SKIP;; co) st tr :: l) true ->
      merge co (mkconfig SKIP st tr :: l1) [mkconfig co st notrans] (mkconfig co st ctrans :: mkconfig (SKIP;; co) st tr :: l) false
  | merge_ctrans_after co c st c' st' tr tr' l1 l2 l :
      c / st ==> c' / st' ->
      merge co l1 (mkconfig c st tr :: l2) (mkconfig c st tr' :: l) false ->
      merge co l1 (mkconfig c' st' ctrans :: mkconfig c st tr :: l2) (mkconfig c' st' ctrans :: mkconfig c st tr' :: l) false
  | merge_etrans_after co c st st' tr tr' l1 l2 l :
      merge co l1 (mkconfig c st tr :: l2) (mkconfig c st tr' :: l) false ->
      merge co l1 (mkconfig c st' etrans :: mkconfig c st tr :: l2) (mkconfig c st' etrans :: mkconfig c st tr' :: l) false.

Lemma merge_property_post: forall c l1 l2 l post,
  merge c l1 l2 l false -> post_hold l2 post -> post_hold l post.
Proof.
  intros. inversion H; subst; simpl in *; auto.
Qed.

Lemma merge_property_rely: forall c l1 l2 l rely pre b,
  merge c l1 l2 l b -> rely_hold l rely pre -> rely_hold l1 rely pre.
Proof.
  intros. induction H; inversion H0; subst; auto.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma merge_property_rely': forall c l1 l2 l rely pre mid,
  merge c l1 l2 l false -> post_hold l1 mid -> rely_hold l rely pre -> rely_hold l2 rely mid.
Proof.
  intros. remember false as b. induction H; inversion H1; subst; simpl in *; try congruence.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma merge_property_guar: forall c l1 l2 l (guar: RG_Assertion),
  merge c l1 l2 l true -> guar_hold l1 guar -> guar_hold l guar.
Proof.
  intros. remember true as b. induction H; inversion H0; subst; try congruence.
  - constructor; auto.
  - constructor; auto. constructor; auto.
  - constructor; auto.
Qed.

Lemma merge_property_guar': forall c l1 l2 l (guar: RG_Assertion),
  (forall st, (SKIP;; c) / st ==> c / st -> guar st st) ->
  merge c l1 l2 l false -> guar_hold l1 guar -> guar_hold l2 guar -> guar_hold l guar.
Proof.
  intros. remember false as b. induction H0; try congruence.
  - constructor; auto. constructor; auto. eapply H; econstructor; eauto.
    eapply merge_property_guar; eauto.
  - inversion H2; subst. constructor; auto.
  - inversion H2; subst. constructor; auto.
Qed.

Lemma merge_property_end: forall l1 l2 l c1 c2 b,
  merge c2 l1 l2 l b -> end_with l (c1;; c2) -> end_with l1 c1.
Proof.
  intros. induction H; inversion H0; subst; auto; try (constructor; auto).
  inversion H3.
Qed.

Lemma merge_property_end': forall l1 l2 l c1 c2,
  merge c2 l1 l2 l false -> end_with l (c1;; c2) -> end_with l2 c2.
Proof.
  intros. remember false as b.
  induction H; inversion H0; subst; auto; try (constructor; auto).
  congruence. inversion H3.
Qed.

Lemma merge_property_begin: forall l1 l2 l c1 c2,
  merge c2 l1 l2 l true -> begin_with l (c1;; c2) -> begin_with l1 c1.
Proof.
  intros. inversion H; subst; simpl in *; inversion H0; subst; auto.
Qed.

Lemma merge_property_begin': forall l1 l2 l co c,
  merge co l1 l2 l false -> begin_with l c -> begin_with l2 c.
Proof.
  intros. inversion H; subst; simpl in *; inversion H0; subst; split; auto.
Qed.

Lemma merge_property_begin'': forall l1 l2 l co,
  merge co l1 l2 l false -> begin_with l1 SKIP.
Proof.
  intros. remember false as b. induction H; simpl in *; auto; try congruence.
Qed.

Lemma merge_property_begin''': forall l1 l2 l co,
  merge co l1 l2 l true -> exists c, begin_with l (c;; co).
Proof.
  intros. inversion H; eexists; simpl in *; eauto.
Qed.

Lemma merge_property_decompose: forall l c1 c2,
  end_with l (c1;; c2) -> valid_trace l ->
  exists l1 l2 b, merge c2 l1 l2 l b.
Proof.
  intros. induction H0; inversion H; subst.
  - do 3 eexists; constructor; auto.
  - inversion H3.
  - destruct (IHvalid_trace H5) as [l1 [l2 [b H_merge]]]. inversion H_merge; subst;
      inversion H0; subst; do 2 eexists; econstructor; eauto; econstructor; eauto.
  - destruct (IHvalid_trace H4) as [l1 [l2 [b H_merge]]]. inversion H_merge; subst;
      inversion H0; subst; do 2 eexists; econstructor; eauto; econstructor; eauto.
Qed.

Theorem seq_soundness: forall pre mid post c1 c2 rely (guar: RG_Assertion),
  (forall st, (SKIP;; c2) / st ==> c2 / st -> guar st st) ->
  rely_guarantee pre mid c1 rely guar -> rely_guarantee mid post c2 rely guar ->
  rely_guarantee pre post (c1;; c2) rely guar.
Proof.
  unfold rely_guarantee; intros.
  assert (exists l1 l2 b, merge c2 l1 l2 l b).
  eapply merge_property_decompose; eauto.
  eapply rely_hold_implies_valid_trace; eauto.
  destruct H4 as [l1 [l2 [b H_merge]]].
  assert (end_with l1 c1). eapply merge_property_end; eauto. apply H0 in H4.
  destruct H4 as [H_guar1 H_post1]. destruct b.
  - split.
    + eapply merge_property_guar; eauto.
    + intros. destruct (merge_property_begin''' _ _ _ _ H_merge). destruct l.
      inversion H5. simpl in *; subst; congruence.
  - assert (end_with l2 c2). eapply merge_property_end'; eauto. apply H1 in H4.
    destruct H4 as [H_guar2 H_post2]. split.
    + eapply merge_property_guar'; eauto.
    + intros. eapply merge_property_post; eauto. apply H_post2.
      eapply merge_property_begin'; eauto.
    + eapply merge_property_rely'; eauto. apply H_post1.
      eapply merge_property_begin''; eauto.
  - eapply merge_property_rely; eauto.
Qed.

End Seq.

Module Skip.

Lemma skip_property: forall l,
  end_with l SKIP -> valid_trace l -> begin_with l SKIP.
Proof.
  intros. induction H0; inversion H; subst; simpl; auto.
  - inversion H3.
  - apply IHvalid_trace in H5. simpl in H5; subst. inversion H0.
  - apply IHvalid_trace in H4. simpl in H4; subst. auto.
Qed.

Theorem skip_soundness: forall (pre post: Assertion) rely guar,
  (forall st, pre st -> post st) ->
  stable_when pre rely ->
  stable_when post rely ->
  rely_guarantee pre post SKIP rely guar.
Proof.
  unfold rely_guarantee; intros. induction H3; simpl in *; subst.
  + split. constructor; auto. intros; auto.
  + inversion H2; subst. assert (begin_with (mkconfig c0 st0 tr0 :: l) SKIP).
    apply skip_property; auto. eapply rely_hold_implies_valid_trace; eauto.
    simpl in *; subst. inversion H3; subst.
  + inversion H2; subst. destruct (IHrely_hold H H0 H1 H8). split.
    constructor; auto. intros. eapply H1; eauto.
Qed.

End Skip.

Module Ass.

Lemma ass_property: forall l x e (pre post: Assertion) rely,
  stable_when pre rely ->
  stable_when post rely ->
  (forall st, pre st -> assn_sub x e post st) ->
  end_with l (x ::= e) -> rely_hold l rely pre ->
  begin_with l (x ::= e) /\ post_hold l pre \/ begin_with l SKIP /\ post_hold l post.
Proof.
  intros. induction H3; inversion H2; subst; simpl; auto.
  - inversion H7.
  - destruct (IHrely_hold H H0 H1 H8) as [[? ?] | [? ?]]; simpl in *; subst.
    + inversion H3; subst. right; split; auto. apply H1; auto.
    + inversion H3.
  - destruct (IHrely_hold H H0 H1 H8) as [[? ?] | [? ?]]; simpl in *; subst.
    + left; split; auto. eapply H; eauto.
    + right; split; auto. eapply H0; eauto.
Qed.

Theorem ass_soundness: forall (pre post: Assertion) x e (rely guar: RG_Assertion),
  (forall st, pre st -> assn_sub x e post st) ->
  (forall st st', pre st /\ (st' = st & { x --> aeval st e } \/ st' = st) -> guar st st') ->
  stable_when pre rely ->
  stable_when post rely ->
  rely_guarantee pre post (x ::= e) rely guar.
Proof.
  unfold rely_guarantee; intros.
  induction H4; simpl in *; subst.
  - assert (rely_hold [mkconfig c0 st0 notrans] rely pre). constructor; auto.
    destruct (ass_property _ _ _ _ _ _ H1 H2 H H3 H5) as [[? H_pre] | [? H_post]]; simpl in *; subst.
    + split. constructor; auto. intros. inversion H6.
    + inversion H3; subst. inversion H9.
  - inversion H3; subst.
    destruct (ass_property _ _ _ _ _ _ H1 H2 H H9 H5) as [[? H_pre] | [? H_post]]; simpl in *; subst.
    + inversion H4; subst. split. constructor; auto. apply IHrely_hold; auto. intros. apply H; auto.
    + inversion H4.
  - inversion H3; subst. destruct (IHrely_hold H H0 H1 H2 H9) as [H_guar H_post].
    split. constructor; auto. intros. eapply H2; eauto.
Qed.

End Ass.

Module If.

Inductive only_env: trace -> Prop :=
  | only_env_base c st: only_env [mkconfig c st notrans]
  | only_env_cons c st st' tr l: only_env (mkconfig c st tr :: l) ->
      only_env (mkconfig c st' etrans :: mkconfig c st tr :: l).

Lemma only_env_and_end_with_implies_begin_with: forall l c,
  only_env l -> end_with l c -> begin_with l c.
Proof.
  intros. induction H; inversion H0; subst; simpl in *; auto. inversion H3.
Qed.

Lemma only_env_implies_guar: forall l guar,
  only_env l -> guar_hold l guar.
Proof.
  intros. induction H; constructor; auto.
Qed.

Lemma only_env_and_pre_stable_when_rely_implies_post: forall l pre rely,
  only_env l -> stable_when pre rely -> rely_hold l rely pre -> post_hold l pre.
Proof.
  intros. induction H1; inversion H; subst; simpl in *; auto. eapply H0; eauto.
Qed.

Inductive subtrace: trace -> trace -> Prop :=
  | subtrace_begin c c' st st' tr l:
      c / st ==> c' / st' -> only_env (mkconfig c st tr :: l) ->
      subtrace [mkconfig c' st' notrans] (mkconfig c' st' ctrans :: mkconfig c st tr :: l)
  | subtrace_ctrans c c' st st' tr tr' l l':
      c / st ==> c' / st' ->
      subtrace (mkconfig c st tr :: l) (mkconfig c st tr' :: l') ->
      subtrace (mkconfig c' st' ctrans :: mkconfig c st tr :: l) (mkconfig c' st' ctrans :: mkconfig c st tr' :: l')
  | subtrace_etrans c st st' tr tr' l l':
      subtrace (mkconfig c st tr :: l) (mkconfig c st tr' :: l') ->
      subtrace (mkconfig c st' etrans :: mkconfig c st tr :: l) (mkconfig c st' etrans :: mkconfig c st tr' :: l').

Lemma subtrace_property_begin: forall c l l',
  subtrace l l' -> begin_with l' c -> begin_with l c.
Proof.
  intros. induction H; inversion H0; subst; simpl in *; auto.
Qed.

Lemma subtrace_property_begin': forall c l l',
  subtrace l l' -> begin_with l c -> begin_with l' c.
Proof.
  intros. induction H; inversion H0; subst; simpl in *; auto.
Qed.

Lemma subtrace_property_post: forall c l l',
  subtrace l l' -> post_hold l c -> post_hold l' c.
Proof.
  intros. induction H; subst; simpl in *; auto.
Qed.

Lemma subtrace_property_decompose': forall b c1 c2 l',
  end_with l' (IFB b THEN c1 ELSE c2 FI) -> valid_trace l' ->
  only_env l' \/
    exists l, (end_with l c1 \/ end_with l c2) /\ subtrace l l'.
Proof.
  intros. induction H0; inversion H; subst; simpl in *; auto.
  - left; constructor.
  - inversion H3.
  - destruct (IHvalid_trace H5) as [H_env | [l0 [[H_end1 | H_end2] H_subtrace]]]; subst.
    + apply only_env_and_end_with_implies_begin_with in H5; auto. simpl in *; subst.
      inversion H0; subst.
      * right. exists [mkconfig c0 st0 notrans]. split. left; constructor; auto. constructor; auto.
      * right. exists [mkconfig c0 st0 notrans]. split. right; constructor; auto. constructor; auto.
    + right. exists (mkconfig c0 st0 ctrans :: l0). split. left; constructor; auto.
      inversion H_subtrace; subst; constructor; auto.
    + right. exists (mkconfig c0 st0 ctrans :: l0). split. right; constructor; auto.
      inversion H_subtrace; subst; constructor; auto.
  - destruct (IHvalid_trace H4) as [H_env | [l0 [[H_end1 | H_end2] H_subtrace]]]; subst.
    + left. constructor; auto.
    + right. exists (mkconfig c0 st0 etrans :: l0). split. left; constructor; auto.
      inversion H_subtrace; subst; constructor; auto.
    + right. exists (mkconfig c0 st0 etrans :: l0). split. right; constructor; auto.
      inversion H_subtrace; subst; constructor; auto.
Qed.

Lemma subtrace_property_decompose: forall b c1 c2 l' rely pre,
  end_with l' (IFB b THEN c1 ELSE c2 FI) -> rely_hold l' rely pre ->
  stable_when pre rely ->
  only_env l' \/
    exists l, (end_with l c1 /\ rely_hold l rely (fun st => pre st /\ beval st b = true) \/
      end_with l c2 /\ rely_hold l rely (fun st => pre st /\ beval st b = false)) /\ subtrace l l'.
Proof.
  intros. induction H0; inversion H; subst; simpl in *; auto.
  - left; constructor.
  - inversion H5.
  - destruct (IHrely_hold H6 H1) as [H_env | [l0 [[[H_end1 H_rely1] | [H_end2 H_rely2]] H_subtrace]]]; subst.
    + apply only_env_and_end_with_implies_begin_with in H6; auto. simpl in *; subst.
      inversion H0; subst.
      * right. exists [mkconfig c' st' notrans]. split. left; split; constructor; auto.
        split; auto. eapply only_env_and_pre_stable_when_rely_implies_post in H_env; eauto.
        constructor; auto.
      * right. exists [mkconfig c' st' notrans]. split. right; split; constructor; auto.
        split; auto. eapply only_env_and_pre_stable_when_rely_implies_post in H_env; eauto.
        constructor; auto.
    + right. exists (mkconfig c' st' ctrans :: l0). split. left. split. constructor; auto.
      inversion H_rely1; subst; inversion H_subtrace; subst; constructor; auto.
      inversion H_subtrace; subst; constructor; auto.
    + right. exists (mkconfig c' st' ctrans :: l0). split. right. split. constructor; auto.
      inversion H_rely2; subst; inversion H_subtrace; subst; constructor; auto.
      inversion H_subtrace; subst; constructor; auto.
  - destruct (IHrely_hold H6 H1) as [H_env | [l0 [[[H_end1 H_rely1] | [H_end2 H_rely2]] H_subtrace]]]; subst.
    + left. constructor; auto.
    + right. exists (mkconfig c0 st' etrans :: l0). split. left. split. constructor; auto.
      inversion H_rely1; subst; inversion H_subtrace; subst; constructor; auto.
      inversion H_subtrace; subst; constructor; auto.
    + right. exists (mkconfig c0 st' etrans :: l0). split. right. split. constructor; auto.
      inversion H_rely2; subst; inversion H_subtrace; subst; constructor; auto.
      inversion H_subtrace; subst; constructor; auto.
Qed.

Lemma subtrace_property_guar: forall b c1 c2 l l' (guar: RG_Assertion),
  (forall c' st st', (IFB b THEN c1 ELSE c2 FI) / st ==> c' / st' -> guar st st') ->
  end_with l' (IFB b THEN c1 ELSE c2 FI) ->
  subtrace l l' -> end_with l c1 -> guar_hold l guar -> guar_hold l' guar.
Proof.
  intros. induction H1; inversion H0; subst; inversion H2; subst; inversion H3; subst.
  - eapply only_env_and_end_with_implies_begin_with in H4 as H_begin; eauto.
    simpl in *; subst. inversion H2; subst. constructor; auto. eapply H; eauto.
    apply only_env_implies_guar; auto. inversion H9.
  - inversion H9.
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma subtrace_property_guar': forall b c1 c2 l l' (guar: RG_Assertion),
  (forall c' st st', (IFB b THEN c1 ELSE c2 FI) / st ==> c' / st' -> guar st st') ->
  end_with l' (IFB b THEN c1 ELSE c2 FI) ->
  subtrace l l' -> end_with l c2 -> guar_hold l guar -> guar_hold l' guar.
Proof.
  intros. induction H1; inversion H0; subst; inversion H2; subst; inversion H3; subst.
  - eapply only_env_and_end_with_implies_begin_with in H4 as H_begin; eauto.
    simpl in *; subst. inversion H2; subst. constructor; auto. eapply H; eauto.
    apply only_env_implies_guar; auto. inversion H9.
  - inversion H9.
  - constructor; auto.
  - constructor; auto.
Qed.

Theorem if_soundness: forall pre post b c1 c2 (rely guar: RG_Assertion),
  stable_when pre rely ->
  (forall c' st st', (IFB b THEN c1 ELSE c2 FI) / st ==> c' / st' -> guar st st') ->
  rely_guarantee (fun st => pre st /\ beval st b = true) post c1 rely guar ->
  rely_guarantee (fun st => pre st /\ beval st b = false) post c2 rely guar ->
  rely_guarantee pre post (IFB b THEN c1 ELSE c2 FI) rely guar.
Proof.
  unfold rely_guarantee; intros.
  destruct (subtrace_property_decompose _ _ _ _ _ _ H3 H4 H) as [H_begin | [l' [[[H_end1 H_rely1] | [H_end2 H_rely2]] H_subtrace]]].
  - split. apply only_env_implies_guar; auto. intros.
    apply only_env_and_end_with_implies_begin_with in H3; auto.
    destruct l. inversion H5. simpl in *; subst; congruence.
  - destruct (H1 l' H_end1 H_rely1) as [H_guar1 H_post1]. split.
    eapply subtrace_property_guar; eauto. intros. eapply subtrace_property_post; eauto.
    apply H_post1. eapply subtrace_property_begin; eauto.
  - destruct (H2 l' H_end2 H_rely2) as [H_guar2 H_post2]. split.
    eapply subtrace_property_guar'; eauto. intros. eapply subtrace_property_post; eauto.
    apply H_post2. eapply subtrace_property_begin; eauto.
Qed.

End If.

Module Consequence.

Lemma consequence_pre_rely: forall (pre pre': Assertion) (rely rely': RG_Assertion),
  (forall st, pre st -> pre' st) ->
  (forall st st', rely st st' -> rely' st st') ->
  forall l, rely_hold l rely pre -> rely_hold l rely' pre'.
Proof.
  intros. induction H1; constructor; auto.
Qed.

Lemma consequence_guar: forall (guar guar': RG_Assertion),
  (forall st st', guar st st' -> guar' st st') ->
  forall l, guar_hold l guar -> guar_hold l guar'.
Proof.
  intros. induction H0; constructor; auto.
Qed.

Lemma consequence_post: forall (post post': Assertion),
  (forall st, post st -> post' st) ->
  forall l, post_hold l post -> post_hold l post'.
Proof.
  intros. destruct l. inversion H0. simpl in *; auto.
Qed.

Theorem consequence_soundness:
  forall (pre pre1 post post1: Assertion) c (rely rely1 guar guar1: RG_Assertion),
  (forall st, pre st -> pre1 st) ->
  (forall st st', rely st st' -> rely1 st st') ->
  (forall st st', guar1 st st' -> guar st st') ->
  (forall st, post1 st -> post st) ->
  rely_guarantee pre1 post1 c rely1 guar1 ->
  rely_guarantee pre post c rely guar.
Proof.
  unfold rely_guarantee; intros. eapply consequence_pre_rely in H5; eauto.
  destruct (H3 l H4 H5) as [H_guar H_post]. split. eapply consequence_guar; eauto.
  intros. eapply consequence_post; eauto.
Qed.

End Consequence.

Module While.

Inductive merge': com -> trace -> trace -> trace -> bool -> Prop :=
  | merge_begin' c co st tr l :
      merge' co [mkconfig c st notrans] nil (mkconfig (c;; co) st tr :: l) true
  | merge_ctrans_before' co c st c' st' tr tr' l1 l :
      c / st ==> c' / st' ->
      merge' co (mkconfig c st tr :: l1) nil (mkconfig (c;; co) st tr' :: l) true ->
      merge' co (mkconfig c' st' ctrans :: mkconfig c st tr :: l1) nil (mkconfig (c';; co) st' ctrans :: mkconfig (c;; co) st tr' :: l) true
  | merge_etrans_before' co c st st' tr tr' l1 l :
      merge' co (mkconfig c st tr :: l1) nil (mkconfig (c;; co) st tr' :: l) true ->
      merge' co (mkconfig c st' etrans :: mkconfig c st tr :: l1) nil (mkconfig (c;; co) st' etrans :: mkconfig (c;; co) st tr' :: l) true
  | merge_join' co st tr tr' l1 l :
      merge' co (mkconfig SKIP st tr :: l1) nil (mkconfig (SKIP;; co) st tr' :: l) true ->
      merge' co (mkconfig SKIP st tr :: l1) [mkconfig co st notrans] (mkconfig co st ctrans :: mkconfig (SKIP;; co) st tr' :: l) false
  | merge_ctrans_after' co c st c' st' tr tr' l1 l2 l :
      c / st ==> c' / st' ->
      merge' co l1 (mkconfig c st tr :: l2) (mkconfig c st tr' :: l) false ->
      merge' co l1 (mkconfig c' st' ctrans :: mkconfig c st tr :: l2) (mkconfig c' st' ctrans :: mkconfig c st tr' :: l) false
  | merge_etrans_after' co c st st' tr tr' l1 l2 l :
      merge' co l1 (mkconfig c st tr :: l2) (mkconfig c st tr' :: l) false ->
      merge' co l1 (mkconfig c st' etrans :: mkconfig c st tr :: l2) (mkconfig c st' etrans :: mkconfig c st tr' :: l) false.

Lemma merge'_property_post: forall c l1 l2 l post,
  merge' c l1 l2 l false -> post_hold l2 post -> post_hold l post.
Proof.
  intros. inversion H; subst; simpl in *; auto.
Qed.

Lemma merge'_property_rely: forall c l1 l2 l rely pre b,
  merge' c l1 l2 l b -> rely_hold l rely pre -> rely_hold l1 rely (fun st => True).
Proof.
  intros. induction H; inversion H0; subst; auto.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma merge'_property_rely': forall c l1 l2 l rely pre mid,
  merge' c l1 l2 l false -> post_hold l1 mid -> rely_hold l rely pre -> rely_hold l2 rely mid.
Proof.
  intros. remember false as b. induction H; inversion H1; subst; simpl in *; try congruence.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma merge'_property_begin: forall l1 l2 l c1 c2,
  merge' c2 l1 l2 l true -> begin_with l (c1;; c2) -> begin_with l1 c1.
Proof.
  intros. inversion H; subst; simpl in *; inversion H0; subst; auto.
Qed.

Lemma merge'_property_begin': forall l1 l2 l co c,
  merge' co l1 l2 l false -> begin_with l c -> begin_with l2 c.
Proof.
  intros. inversion H; subst; simpl in *; inversion H0; subst; split; auto.
Qed.

Lemma merge'_property_begin'': forall l1 l2 l co,
  merge' co l1 l2 l false -> begin_with l1 SKIP.
Proof.
  intros. remember false as b. induction H; simpl in *; auto; try congruence.
Qed.

Lemma merge'_property_begin''': forall l1 l2 l co,
  merge' co l1 l2 l true -> exists c, begin_with l (c;; co).
Proof.
  intros. inversion H; eexists; simpl in *; eauto.
Qed.

Lemma while_property: forall (pre post: Assertion) b c (rely guar: RG_Assertion) l,
  stable_when pre rely ->
  stable_when (fun st => beval st b = true) rely ->
  stable_when post rely ->
  (forall st, pre st /\ beval st b = false -> post st) ->
  (forall st, guar st st) ->
  rely_guarantee (fun st => pre st /\ beval st b = true) pre c rely guar ->
  end_with l (WHILE b DO c END) ->
  rely_hold l rely pre ->
    begin_with l (WHILE b DO c END) /\ post_hold l pre \/
    begin_with l (IFB b THEN c;; WHILE b DO c END ELSE SKIP FI) /\ post_hold l pre \/
    (exists c', begin_with l (c';; WHILE b DO c END) /\
      exists l1, merge' (WHILE b DO c END) l1 nil l true /\
      end_with l1 c /\
      rely_hold l1 rely (fun st => pre st /\ beval st b = true)) \/
    begin_with l SKIP /\ post_hold l post.
Proof.
  intros. induction H6; inversion H5; subst; simpl in *; auto.
  - inversion H10.
  - eapply IHrely_hold in H11; eauto.
    destruct H11 as [[? H_pre] | [[? H_pre] | [[c2 [? [l1 [H_merge [H_end H_rely]]]]] | [? H_pre]]]];
      simpl in *; subst.
    + inversion H6; subst; auto.
    + inversion H6; subst.
      * right. right. left. eexists; split; eauto. eexists; split; econstructor; eauto.
        constructor. constructor; auto.
      * right. right. right. auto.
    + inversion H6; subst.
      * right. right. left. eexists; split; eauto.
        exists (mkconfig c1' st' ctrans :: l1). split.
        inversion H_merge; subst; constructor; auto.
        split. constructor; auto.
        inversion H_merge; subst; constructor; eauto.
      * left; split; auto.
        eapply merge'_property_begin in H_merge as H_begin; simpl; eauto.
        apply H4 in H_rely; auto. destruct H_rely. apply H9 in H_begin.
        inversion H_merge; subst; simpl in *; auto.
    + inversion H6.
  - eapply IHrely_hold in H11; eauto.
    destruct H11 as [[? H_pre] | [[? H_pre] | [[c2 [? [l1 [H_merge [H_end H_rely]]]]] | [? H_pre]]]];
      simpl in *; subst.
    + left. split; auto. eapply H; eauto.
    + right. left. split; auto. eapply H; eauto.
    + right. right. left. eexists; split; eauto.
      exists (mkconfig c2 st' etrans :: l1). split.
      inversion H_merge; subst; constructor; auto.
      split. constructor; auto.
      inversion H_merge; subst; constructor; eauto.
    + right. right. right. split; auto. eapply H1; eauto.
Qed.

Theorem while_soundness: forall (pre post: Assertion) b c (rely guar: RG_Assertion),
  stable_when pre rely ->
  stable_when (fun st => beval st b = true) rely ->
  stable_when post rely ->
  (forall st, pre st /\ beval st b = false -> post st) ->
  (forall st, guar st st) ->
  rely_guarantee (fun st => pre st /\ beval st b = true) pre c rely guar ->
  rely_guarantee pre post (WHILE b DO c END) rely guar.
Proof.
  intros. unfold rely_guarantee. intros. rename c0 into c.
  induction H6; inversion H5; subst; simpl in *.
  - split. constructor; auto. intros. congruence.
  - inversion H10.
  - destruct (while_property _ _ _ _ _ _ _ H H0 H1 H2 H3 H4 H11 H7) as
      [[? H_post] | [[? H_post] | [[c1 [H_begin [l1 [H_merge [H_end H_rely]]]]] | [? H_post]]]];
      simpl in *; subst.
    + inversion H6; subst. destruct (IHrely_hold H H0 H1 H2 H4 H11). split.
      constructor; auto. intros; congruence.
    + destruct (IHrely_hold H H0 H1 H2 H4 H11). inversion H6; subst.
      * split. constructor; auto. intros. congruence.
      * split. constructor; auto. intros. eapply H2; eauto.
    + inversion H6; subst.
      * assert (rely_hold (mkconfig c1' st' ctrans :: l1)
          rely (fun st => pre st /\ beval st b = true)).
        inversion H_merge; subst; constructor; auto. apply H4 in H8; auto.
        destruct H8 as [H8 _]. split. constructor; auto.
        inversion H_merge; subst; inversion H8; subst; auto.
        eapply IHrely_hold; eauto. intros. congruence. constructor; auto.
      * split. constructor; auto. eapply IHrely_hold; eauto.
        intros. congruence.
    + inversion H6.
  - destruct (IHrely_hold H H0 H1 H2 H4 H11). split.
    constructor; auto. intros. eapply H1; eauto.
Qed.

End While.

Module Await.

Inductive subtrace': trace -> trace -> Prop :=
  | subtrace'_begin c c' st st':
      c / st ==> c' / st' ->
      subtrace' [mkconfig c' st' notrans] (mkconfig c' st' ctrans :: [mkconfig c st notrans])
  | subtrace'_ctrans c c' st st' tr tr' l l':
      c / st ==>c' / st' ->
      subtrace' (mkconfig c st tr :: l) (mkconfig c st tr' :: l') ->
      subtrace' (mkconfig c' st' ctrans :: mkconfig c st tr :: l) (mkconfig c' st' ctrans :: mkconfig c st tr' :: l')
  | subtrace'_etrans c st st' tr tr' l l':
      subtrace' (mkconfig c st tr :: l) (mkconfig c st tr' :: l') ->
      subtrace' (mkconfig c st' etrans :: mkconfig c st tr :: l) (mkconfig c st' etrans :: mkconfig c st tr' :: l').

Lemma subtrace'_create: forall l c st c' st',
  valid_trace l -> end_with_config l (mkconfig c' st' notrans) -> c / st ==> c' / st' ->
  exists l', subtrace' l l' /\ end_with_config l' (mkconfig c st notrans).
Proof.
  intros. induction H; inversion H0; simpl in *; subst.
  - exists (mkconfig c' st' ctrans :: [mkconfig c0 st0 notrans]). split; constructor; auto.
    constructor.
  - inversion H4.
  - destruct (IHvalid_trace H6) as [l' [H_sub H_end]].
    exists (mkconfig c1 st1 ctrans :: l'); split. inversion H_sub; subst; constructor; auto.
    constructor; auto.
  - destruct (IHvalid_trace H5) as [l' [H_sub H_end]].
    exists (mkconfig c1 st1 etrans :: l'); split. inversion H_sub; subst; constructor; auto.
    constructor; auto.
Qed.

Lemma subtrace'_property_begin: forall l l' c st,
  subtrace' l l' -> begin_with_config l (mkconfig c st ctrans) -> begin_with_config l' (mkconfig c st ctrans).
Proof.
  intros. inversion H; subst; inversion H0; subst; simpl in *; auto.
Qed.

Lemma subtrace'_property_rely: forall l l' rely,
  subtrace' l l' -> rely_hold l rely (fun st => True) ->
  rely_hold l' rely (fun st' => True).
Proof.
  intros. induction H; inversion H0; subst; auto.
  - constructor; auto. constructor; auto.
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma await_property_subtrace': forall b c rely pre st0 st1,
  stable_when pre rely ->
  (AWAIT b THEN c END) / st0 ==> SKIP / st1 -> pre st0 ->
    c = SKIP /\ st0 = st1 \/
      exists l, end_with_config l (mkconfig c st0 notrans) /\
      begin_with_config l (mkconfig SKIP st1 ctrans) /\
      rely_hold l (fun st st' => st = st') (fun st=> pre st /\ beval st b = true /\ forall x, st x = st0 x).
Proof.
  intros. inversion H0; subst. remember (c0, st0) as config.
  remember (SKIP, st1) as config'. replace c0 with (fst config) by (subst; auto).
  replace st0 with (snd config) by (subst; auto).
  assert (fst config = SKIP /\ snd config = st1 \/ (exists l : trace,
   end_with_config l {| c := fst config; st := snd config; tr := notrans |} /\
   begin_with_config l {| c := SKIP; st := st1; tr := ctrans |} /\
   rely_hold l (fun st2 st' : state => st2 = st')
     (fun st2 : state => pre st0 /\ beval st0 b = true /\ (forall x : string, st2 x = snd config x)))).
  - assert (exists st', cmultistep config (SKIP, st')). subst; eexists; eauto.
    clear Heqconfig. induction H7; subst; simpl.
    + left; split; auto.
    + destruct x; destruct y; simpl in *. right. destruct H2.
      assert ((SKIP, st1) = (SKIP, st1)) by auto.
      apply IHmulti in H5; auto.
      destruct H5 as [[? ?] | [l' [H_end [H_begin H_rely]]]]; subst.
      * exists (mkconfig SKIP st1 ctrans :: [mkconfig c1 s notrans]); split; simpl; auto.
        constructor; constructor. split; auto. constructor; auto.
        constructor; auto.
      * assert (valid_trace l') by (eapply rely_hold_implies_valid_trace; eauto).
        destruct (subtrace'_create _ _ _ _ _ H5 H_end H3) as [l [H_sub H_end']].
        exists l; split; auto. split. eapply subtrace'_property_begin; eauto.
        eapply separate_rely_pre; eauto. eapply subtrace'_property_rely; eauto.
        eapply separate_rely_pre'; eauto.
      * eexists; eauto.
  - subst. destruct H2 as [[? ?] | [l [H_end [H_begin H_rely]]]]; subst; simpl in *; auto.
    right. eexists; split; eauto. split; auto.
    eapply Consequence.consequence_pre_rely; eauto.
    simpl; intros. destruct H2 as [H_pre [H_true H_state]].
    assert (st2 = st0) by (apply functional_extensionality; auto). subst. auto.
Qed.

Lemma await_property: forall b c l rely pre,
  stable_when pre rely ->
  end_with l (AWAIT b THEN c END) -> rely_hold l rely pre ->
    begin_with l (AWAIT b THEN c END) /\ post_hold l pre \/ begin_with l SKIP.
Proof.
  intros. induction H1; inversion H0; subst; simpl in *; auto.
  - inversion H5.
  - destruct (IHrely_hold H H6) as [[? H_pre] | ?]; subst; inversion H1; subst; auto.
  - destruct (IHrely_hold H H6) as [[? H_pre] | ?]; subst; auto. left; split; auto.
    eapply H; eauto.
Qed.

Theorem await_soundness: forall (pre post: Assertion) b c (rely guar: RG_Assertion),
  stable_when pre rely ->
  stable_when post rely ->
  (forall st0, rely_guarantee
    (fun st => pre st /\ beval st b = true /\ forall x, st x = st0 x)
    (fun st => post st /\ guar st0 st) c (fun st st' => st = st')
    (fun st st' => True)) ->
  rely_guarantee pre post (AWAIT b THEN c END) rely guar.
Proof.
  unfold rely_guarantee. intros. induction H3; inversion H2; subst; simpl in *.
  - inversion H2; subst. split. constructor. intros. inversion H4. inversion H7.
  - inversion H7.
  - destruct (await_property _ _ _ _ _ H H8 H4) as [[H_begin H_post] | H_begin];
      simpl in *; subst.
    + inversion H3; subst. destruct (await_property_subtrace' _ _ _ _ _ _ H H3 H_post) as [[? ?] | [l' [H_end [H_begin H_rely]]]];
        simpl in *; subst.
      * assert (end_with [mkconfig SKIP st' notrans] SKIP) by constructor.
        apply (H1 st') in H5. destruct H5. simpl in *; subst. split. constructor; auto.
        apply H6; auto. apply IHrely_hold; auto. intros; apply H6; auto. constructor; auto.
      * assert (end_with l' c0). eapply end_with_config_implies_end_with; eauto.
        apply (H1 st0) in H5; auto. destruct H5 as [_ H5].
        destruct l'. inversion H_begin. destruct c1; simpl in *; inversion H_begin; subst.
        split. constructor; auto. apply H5; auto. apply IHrely_hold; auto.
        intros; apply H5; auto.
    + inversion H3.
  - destruct (await_property _ _ _ _ _ H H8 H4) as [[H_begin H_post] | H_begin];
      simpl in *; subst.
    + split. constructor; auto. apply IHrely_hold; auto. intros. inversion H5.
    + assert (guar_hold ({| c := SKIP; st := st0; tr := tr0 |} :: l) guar /\
        (SKIP = SKIP -> post st0)) by (apply IHrely_hold; auto). destruct H5.
      split. constructor; auto. intros. eapply H0; eauto.
Qed.

End Await.

Module Parallel.

Inductive conjoin: trace -> trace -> trace -> Prop :=
  | conjoin_begin c1 c2 st:
      conjoin [mkconfig c1 st notrans] [mkconfig c2 st notrans] [mkconfig (PAR c1 WITH c2 END) st notrans]
  | conjoin_ctrans_left c1 st c1' c2 st' tr1 tr2 tr l1 l2 l:
      c1' / st' ==> c1 / st ->
      conjoin (mkconfig c1' st' tr1 :: l1) (mkconfig c2 st' tr2 :: l2) (mkconfig (PAR c1' WITH c2 END) st' tr :: l) ->
      conjoin (mkconfig c1 st ctrans :: mkconfig c1' st' tr1 :: l1) (mkconfig c2 st etrans :: mkconfig c2 st' tr2 :: l2) (mkconfig (PAR c1 WITH c2 END) st ctrans :: mkconfig (PAR c1' WITH c2 END) st' tr :: l)
  | conjoin_ctrans_right c1 c2 st c2' st' tr1 tr2 tr l1 l2 l:
      c2' / st' ==> c2 /st ->
      conjoin (mkconfig c1 st' tr1 :: l1) (mkconfig c2' st' tr2 :: l2) (mkconfig (PAR c1 WITH c2' END) st' tr :: l) ->
      conjoin (mkconfig c1 st etrans :: mkconfig c1 st' tr1 :: l1) (mkconfig c2 st ctrans :: mkconfig c2' st' tr2 :: l2) (mkconfig (PAR c1 WITH c2 END) st ctrans :: mkconfig (PAR c1 WITH c2' END) st' tr :: l)
  | conjoin_etrans c1 c2 st st' tr1 tr2 tr l1 l2 l:
      conjoin (mkconfig c1 st' tr1 :: l1) (mkconfig c2 st' tr2 :: l2) (mkconfig (PAR c1 WITH c2 END) st' tr :: l) ->
      conjoin (mkconfig c1 st etrans :: mkconfig c1 st' tr1 :: l1) (mkconfig c2 st etrans :: mkconfig c2 st' tr2 :: l2) (mkconfig (PAR c1 WITH c2 END) st etrans :: mkconfig (PAR c1 WITH c2 END) st' tr :: l)
  | conjoin_join st tr1 tr2 tr l1 l2 l:
      conjoin (mkconfig SKIP st tr1 :: l1) (mkconfig SKIP st tr2 :: l2) (mkconfig (PAR SKIP WITH SKIP END) st tr :: l) ->
      conjoin (mkconfig SKIP st etrans :: mkconfig SKIP st tr1 :: l1) (mkconfig SKIP st etrans :: mkconfig SKIP st tr2 :: l2) (mkconfig SKIP st ctrans :: mkconfig (PAR SKIP WITH SKIP END) st tr :: l)
  | conjoin_after_join st st' tr1 tr2 tr l1 l2 l:
      conjoin (mkconfig SKIP st tr1 :: l1) (mkconfig SKIP st tr2 :: l2) (mkconfig SKIP st tr :: l) ->
      conjoin (mkconfig SKIP st' etrans :: mkconfig SKIP st tr1 :: l1) (mkconfig SKIP st' etrans :: mkconfig SKIP st tr2 :: l2) (mkconfig SKIP st' etrans :: mkconfig SKIP st tr :: l).

Lemma par_property: forall c1 c2 l,
  end_with l (PAR c1 WITH c2 END) -> valid_trace l ->
  begin_with l SKIP \/ exists c1' c2', begin_with l (PAR c1' WITH c2' END).
Proof.
  intros. induction H0; inversion H; subst; simpl in *.
  - right. eexists; eexists; eauto.
  - inversion H3.
  - destruct (IHvalid_trace H5) as [? | [c1' [c2' ?]]]; subst; inversion H0; subst.
    + right. do 2 eexists; eauto.
    + right. do 2 eexists; eauto.
    + left; auto.
  - destruct (IHvalid_trace H4) as [? | [c1' [c2' ?]]]; subst.
    + left; auto.
    + right. do 2 eexists; eauto.
Qed.

Lemma conjoin_create: forall l c1 c2,
  end_with l (PAR c1 WITH c2 END) -> valid_trace l ->
  exists l1 l2, conjoin l1 l2 l.
Proof.
  intros. induction H0; simpl in *; subst.
  - inversion H; subst. exists [mkconfig c1 st0 notrans], [mkconfig c2 st0 notrans].
    constructor; auto. inversion H3.
  - inversion H; subst.
    destruct (IHvalid_trace H5) as [l1 [l2 H_conjoin]].
    destruct (par_property _ _ _ H5 H1) as [? | [c1' [c2' ?]]]; simpl in *; subst; inversion H0; subst.
    + exists (mkconfig c1'0 st0 ctrans :: l1); exists (mkconfig c2' st0 etrans :: l2).
      inversion H_conjoin; subst; constructor; auto.
    + exists (mkconfig c1' st0 etrans :: l1); exists (mkconfig c2'0 st0 ctrans :: l2).
      inversion H_conjoin; subst; constructor; auto.
    + exists (mkconfig SKIP st0 etrans :: l1); exists (mkconfig SKIP st0 etrans :: l2).
      inversion H_conjoin; subst; constructor; auto.
  - inversion H; subst.
    destruct (IHvalid_trace H4) as [l1 [l2 H_conjoin]].
    destruct (par_property _ _ _ H4 H0) as [? | [c1' [c2' ?]]]; simpl in *; subst.
    + exists (mkconfig SKIP st0 etrans :: l1); exists (mkconfig SKIP st0 etrans :: l2).
      inversion H_conjoin; subst; constructor; auto.
    + exists (mkconfig c1' st0 etrans :: l1); exists (mkconfig c2' st0 etrans :: l2).
      inversion H_conjoin; subst; constructor; auto.
Qed.

Lemma conjoin_property_end: forall c1 c2 l1 l2 l, conjoin l1 l2 l ->
  end_with l (PAR c1 WITH c2 END) -> end_with l1 c1.
Proof.
  intros. induction H; subst; simpl in *; inversion H0; subst; constructor; auto. inversion H3.
Qed.

Lemma conjoin_property_end': forall c1 c2 l1 l2 l, conjoin l1 l2 l ->
  end_with l (PAR c1 WITH c2 END) -> end_with l2 c2.
Proof.
  intros. induction H; subst; simpl in *; inversion H0; subst; constructor; auto. inversion H3.
Qed.

Lemma conjoin_property_begin: forall l1 l2 l, conjoin l1 l2 l ->
  begin_with l SKIP -> begin_with l1 SKIP.
Proof.
  intros. induction H; subst; simpl in *; inversion H0; subst; constructor; auto.
Qed.

Lemma conjoin_property_begin': forall l1 l2 l, conjoin l1 l2 l ->
  begin_with l SKIP -> begin_with l2 SKIP.
Proof.
  intros. induction H; subst; simpl in *; inversion H0; subst; constructor; auto.
Qed.

Lemma conjoin_property_post: forall l1 l2 l post1 post2,
  conjoin l1 l2 l -> post_hold l1 post1 -> post_hold l2 post2 ->
  post_hold l (fun st => post1 st /\ post2 st).
Proof.
  intros. induction H; simpl in *; auto.
Qed.

Lemma conjoin_property_rely: forall l1 l2 l (rely guar rely': RG_Assertion) (pre post: Assertion),
  conjoin l1 l2 l -> rely_hold l rely pre -> guar_hold l2 guar ->
  (forall st st', rely st st' \/ guar st st' -> rely' st st') ->
  (forall st, rely' st st) ->
  rely_hold l1 (fun st st' => rely' st st') pre.
Proof.
  intros. induction H.
  - inversion H0; subst. inversion H1; subst. constructor; auto.
  - inversion H0; subst; inversion H1; subst. constructor; auto.
  - inversion H0; subst; inversion H1; subst. constructor; auto.
  - inversion H0; subst. inversion H1; subst. constructor; auto.
  - inversion H0; subst. inversion H1; subst. constructor; auto.
  - inversion H0; subst. inversion H1; subst. constructor; auto.
Qed.

Lemma conjoin_property_rely': forall l1 l2 l (rely guar rely': RG_Assertion) (pre post: Assertion),
  conjoin l1 l2 l -> rely_hold l rely pre -> guar_hold l1 guar ->
  (forall st st', rely st st' \/ guar st st' -> rely' st st') ->
  (forall st, rely' st st) ->
  rely_hold l2 (fun st st' => rely' st st') pre.
Proof.
  intros. induction H.
  - inversion H0; subst. inversion H1; subst. constructor; auto.
  - inversion H0; subst; inversion H1; subst. constructor; auto.
  - inversion H0; subst; inversion H1; subst. constructor; auto.
  - inversion H0; subst. inversion H1; subst. constructor; auto.
  - inversion H0; subst. inversion H1; subst. constructor; auto.
  - inversion H0; subst. inversion H1; subst. constructor; auto.
Qed.

Lemma conjoin_property_rely_guar:
  forall c1 c2 l1 l2 l (rely rely1 rely2 guar guar1 guar2: RG_Assertion) pre,
    conjoin l1 l2 l -> rely_hold l rely pre -> end_with l (PAR c1 WITH c2 END) ->
    (forall l, end_with l c1 -> rely_hold l rely1 pre -> guar_hold l guar1) ->
    (forall l, end_with l c2 -> rely_hold l rely2 pre -> guar_hold l guar2) ->
    (forall st st', rely st st' \/ guar1 st st' -> rely2 st st') ->
    (forall st st', rely st st' \/ guar2 st st' -> rely1 st st') ->
    (forall st st', guar1 st st' \/ guar2 st st' -> guar st st') ->
    (forall st, rely1 st st) -> (forall st, rely2 st st) ->
    guar_hold l1 guar1 /\ guar_hold l2 guar2.
Proof.
  intros. induction H.
  - split; constructor.
  - inversion H0; subst; clear H0. inversion H1; subst; clear H1.
    assert (guar_hold ({| c := c1'; st := st'; tr := tr1 |} :: l1) guar1 /\
            guar_hold ({| c := c3; st := st'; tr := tr2 |} :: l2) guar2).
    apply IHconjoin; auto.
    destruct H0 as [H_guar1 H_guar2].
    split; constructor; auto. clear H3. clear IHconjoin.
    assert (guar_hold (mkconfig c0 st0 ctrans :: mkconfig c1' st' tr1 :: l1) guar1).
    apply H2. constructor; auto. eapply conjoin_property_end; eauto. constructor; auto.
    eapply conjoin_property_rely; eauto. inversion H0; auto.
  - inversion H0; subst; clear H0. inversion H1; subst; clear H1.
    assert (guar_hold ({| c := c0; st := st'; tr := tr1 |} :: l1) guar1 /\
            guar_hold ({| c := c2'; st := st'; tr := tr2 |} :: l2) guar2).
    apply IHconjoin; auto.
    destruct H0 as [H_guar1 H_guar2].
    split; constructor; auto. clear H2. clear IHconjoin.
    assert (guar_hold (mkconfig c3 st0 ctrans :: mkconfig c2' st' tr2 :: l2) guar2).
    apply H3. constructor; auto. eapply conjoin_property_end'; eauto. constructor; auto.
    eapply conjoin_property_rely'; eauto. inversion H0; auto.
  - inversion H0; subst; clear H0. inversion H1; subst; clear H1.
    assert (guar_hold ({| c := c0; st := st'; tr := tr1 |} :: l1) guar1 /\
            guar_hold ({| c := c3; st := st'; tr := tr2 |} :: l2) guar2).
    apply IHconjoin; auto.
    destruct H0 as [H_guar1 H_guar2].
    split; constructor; auto.
  - inversion H0; subst; clear H0. inversion H1; subst; clear H1.
    assert (guar_hold ({| c := SKIP; st := st0; tr := tr1 |} :: l1) guar1 /\
            guar_hold ({| c := SKIP; st := st0; tr := tr2 |} :: l2) guar2).
    apply IHconjoin; auto.
    destruct H0 as [H_guar1 H_guar2].
    split; constructor; auto.
  - inversion H0; subst; clear H0. inversion H1; subst; clear H1.
    assert (guar_hold ({| c := SKIP; st := st0; tr := tr1 |} :: l1) guar1 /\
            guar_hold ({| c := SKIP; st := st0; tr := tr2 |} :: l2) guar2).
    apply IHconjoin; auto.
    destruct H0 as [H_guar1 H_guar2].
    split; constructor; auto.
Qed.

Lemma conjoin_property_guar: forall l1 l2 l (guar1 guar2 guar: RG_Assertion),
  conjoin l1 l2 l -> guar_hold l1 guar1 -> guar_hold l2 guar2 ->
  (forall st st', guar1 st st' \/ guar2 st st' -> guar st st') ->
  (forall st, guar st st) ->
  guar_hold l guar.
Proof.
  intros. induction H.
  - inversion H0; subst. inversion H1; subst. constructor; auto.
  - inversion H0; subst. inversion H1; subst. constructor; auto. constructor; auto.
  - inversion H0; subst. inversion H1; subst. constructor; auto. constructor; auto.
  - inversion H0; subst. inversion H1; subst. constructor; auto.
  - inversion H0; subst. inversion H1; subst. constructor; auto. constructor; auto.
  - inversion H0; subst. inversion H1; subst. constructor; auto.
Qed.

Theorem par_soundness:
  forall (pre post1 post2: Assertion) c1 c2 (rely1 rely2 rely guar1 guar2 guar: RG_Assertion),
    (forall st, guar st st) ->
    (forall st, rely1 st st) ->
    (forall st, rely2 st st) ->
    (forall st st', rely st st' \/ guar1 st st' -> rely2 st st') ->
    (forall st st', rely st st' \/ guar2 st st' -> rely1 st st') ->
    (forall st st', guar1 st st' \/ guar2 st st' -> guar st st') ->
    rely_guarantee pre post1 c1 rely1 guar1 ->
    rely_guarantee pre post2 c2 rely2 guar2 ->
    rely_guarantee pre (fun st => post1 st /\ post2 st) (PAR c1 WITH c2 END) rely guar.
Proof.
  unfold rely_guarantee; intros.
  assert (exists l1 l2, conjoin l1 l2 l). eapply conjoin_create; eauto.
  eapply rely_hold_implies_valid_trace; eauto.
  destruct H9 as [l1 [l2 H_conjoin]].
  assert (guar_hold l1 guar1 /\ guar_hold l2 guar2).
  eapply conjoin_property_rely_guar; eauto; intros. apply H5; auto. apply H6; auto.
  destruct H9 as [H_guar1 Hguar2]. split.
  - eapply conjoin_property_guar; eauto.
  - intros. eapply conjoin_property_post; eauto.
    + apply H5. eapply conjoin_property_end; eauto. eapply conjoin_property_rely; eauto.
      eapply conjoin_property_begin; eauto.
    + apply H6. eapply conjoin_property_end'; eauto. eapply conjoin_property_rely'; eauto.
      eapply conjoin_property_begin'; eauto.
Qed.

End Parallel.

Theorem rely_guarantee_proof_soundness: forall pre post c rely guar,
  rely_guarantee_proof pre post c rely guar -> rely_guarantee pre post c rely guar.
Proof.
  intros. induction H.
  - eapply Skip.skip_soundness; eauto.
  - eapply Ass.ass_soundness; eauto.
  - eapply Seq.seq_soundness; eauto.
  - eapply If.if_soundness; eauto.
  - eapply While.while_soundness; eauto.
  - eapply Await.await_soundness; eauto.
  - eapply Consequence.consequence_soundness; eauto.
  - apply (Parallel.par_soundness pre post1 post2 c1 c2 rely1 rely2 rely guar1 guar2 guar); auto.
Qed.




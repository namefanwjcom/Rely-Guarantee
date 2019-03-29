(** * Imp: �򵥵�ָ��ʽ���� *)

(** �ڱ����У����ǻ��������ؿ�������� Coq ���о������������Ȥ�Ķ�����
    ���ǵİ����о���һ����Ϊ Imp ��_'�򵥵�ָ��ʽ�������'_��
    �������˴�ͳ�������ԣ��� C �� Java����һС���ֺ���Ƭ�Ρ�������һ����
    Imp ��д�ĳ�����ѧ������

       Z ::= X;;
       Y ::= 1;;
       WHILE ! (Z = 0) DO
         Y ::= Y * Z;;
         Z ::= Z - 1
       END
*)

(** ���¹�ע����ζ��� Imp ��_'�﷨'_��_'����'_��_'��������Ի�����
    ��Programming Language Foundations��'_��_'�����������'_�ڶ���
    �е��½���չ��_'����ȼ۹�ϵ��Program Equivalence��'_��������
    _'�����߼���Hoare Logic��'_������һ�ֹ㷺��������ָ��ʽ������߼��� *)

Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.

From RG Require Import Maps.

(* ################################################################# *)
(** * �����Ͳ������ʽ *)

(** ���ǻ����������չʾ Imp��������_'�����Ͳ������ʽ'_�ĺ������ԣ�
    ֮������_'����'_�Ա��ʽ����չ�������һ��������ֵ��������������ѭ����
    _'ָ��'_���ԡ� *)

(* ================================================================= *)
(** ** �﷨ *)

Module AExp.

(** ������������ָ���������Ͳ������ʽ��_'�����﷨��Abstract Syntax��'_�� *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

(** �ڱ����У�����ʡ���˴󲿷ִӳ���Աʵ�ʱ�д�ľ����﷨��������﷨���ķ���
    -- ���磬���Ὣ�ַ��� ["1+2*3"] ��������� AST��

      APlus (ANum 1) (AMult (ANum 2) (ANum 3)).

    ��ѡ���½� [ImpParser] �п�����һ���򵥵Ĵʷ��������ͽ�������ʵ�֣�
    �����Խ������ַ��롣��_'����'_ͨ������������Ȿ�£�
    �������û���Ϲ�������Щ�����Ŀγ̣�����������γ̣���������Ҫ�Զ�һ�¸��½ڡ� *)

(** ��Ϊ�Աȣ���������Լ���� BNF���Ϳ�˹-ŵ����ʽ���ķ������ͬ���ĳ����﷨��

    a ::= nat
        | a + a
        | a - a
        | a * a

    b ::= true
        | false
        | a = a
        | a <= a
        | not b
        | b and b
*)

(** ��ǰ��� Coq �汾��Ա�...

       - BNF �Ƿ���ʽ���� -- ���磬�������˱��ʽ�����ϵ��﷨�Ľ���
         ������ӷ�����д�� [+] ������һ����׺��������û��ָ���ʷ������ͽ�������������
         ���� [+]��[-] �� [*] ��������ȼ�������������ȷ�ӱ��ʽ�ķ���ȣ���
         ��ʵ�ֱ�����ʱ����ҪһЩ���ӵ���Ϣ���Լ�������ǻۣ�
         ���ܽ�������ת������ʽ���Ķ��塣

         Coq �汾��ʼ�պ�����������Щ��Ϣ��ֻרע�ڳ����﷨��

       - ��һ���� BNF �汾����������׶������ķ���ʽ��ʹ�������
         �����ۺ��ںڰ�����дʱ�����кܴ�����ƣ�
         ��ʱ����һ��ĸ���Ҫ�Ⱦ�ȷ��������ϸ�ڸ�����Ҫ��

         ȷʵ�����ںܶ������� BNF �ļǷ������ǿ�������ʹ�����ǣ�
         ��������ľ���ʹ�������� BNF ����ʽ����Ϊû�б�Ҫ��
         ���µ�����Ƿǳ���Ҫ�ġ�

    ��Ӧ�����ּǷ������б�Ҫ������ʽ������������֮��Ľ�����
    ����ʽ����������ʵ�ֺ�֤���� *)

(* ================================================================= *)
(** ** ��ֵ *)

(** ���������ʽ����_'��ֵ��Evaluation��'_��õ���ֵ�� *)

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2  => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

(** ͬ�����Բ������ʽ��ֵ��õ�����ֵ�� *)

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval a1) =? (aeval a2)
  | BLe a1 a2   => (aeval a1) <=? (aeval a2)
  | BNot b1     => negb (beval b1)
  | BAnd b1 b2  => andb (beval b1) (beval b2)
  end.

(* ================================================================= *)
(** ** �Ż� *)

(** ������δ����̫�ණ������������Щ����������Ѿ���ǰ�������ˡ�
    �������Ƕ�����һ�������������ʽ��������΢���л���ĺ������������е�
    [0+e]���� [(APlus (ANum 0) e]������Ϊ [e]�� *)

Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n =>
      ANum n
  | APlus (ANum 0) e2 =>
      optimize_0plus e2
  | APlus e1 e2 =>
      APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 =>
      AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 =>
      AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

(** Ҫ��֤���ǵ��Ż�����ȷ�ģ�������ĳЩʾ���в��������۲������������ȷ�� *)

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

(** �����Ҫȷ�����Ż�����ȷ�ԣ����Ż���ı��ʽ��ԭ���ʽ����ֵ�����ͬ��
    ��ô����Ӧ��֤������ *)

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  - (* ANum *) reflexivity.
  - (* APlus *) destruct a1 eqn:Ea1.
    + (* a1 = ANum n *) destruct n eqn:En.
      * (* n = 0 *)  simpl. apply IHa2.
      * (* n <> 0 *) simpl. rewrite IHa2. reflexivity.
    + (* a1 = APlus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMinus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMult a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  - (* AMinus *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - (* AMult *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.  Qed.

(* ################################################################# *)
(** * Coq �Զ��� *)

(** ��һ��֤���еĴ����ظ������˷��ꡣ�����������ʽ�����ԣ�
    ����֤���Ż��Ŀɿ������Զ����Ӹ��ӣ���������Ϊһ�����������⡣

    ĿǰΪֹ���������е�֤����ֻʹ����һ����ֵ� Coq �Ĳ��ԣ�
    �����Զ����첿��֤����ǿ��������ȫ�������ˡ�����������������һЩ���ܣ�
    ������һ�������ǻῴ�����ࡣҪʹ��������Ҫ�ķѵ㾫�� --
    Coq ���Զ����Ǹ�ǿ��Ĺ��� -- �������������Ǵ����ġ��ظ���
    �ײ��ϸ���н�ų�����רע�ڸ��Ӹ��ӵĶ���͸�����Ȥ�����ʡ� *)

(* ================================================================= *)
(** ** ������ *)

(** _'�����ԣ�Tacticals��'_�� Coq �е��������ʾһ����������������Ϊ�����Ĳ��ԣ�
    ��Ȼ����Ը��Ļ�Ҳ���԰�����Ϊ���߽ײ��ԡ��� *)

(* ----------------------------------------------------------------- *)
(** *** [try] ������ *)

(** ��� [T] ��һ�����ԣ���ô [try T] ��һ���� [T] һ���Ĳ��ԣ�ֻ�����
    [T] ʧ�ܵĻ���[try T] �ͻ�_'�ɹ���'_ʲôҲ����������ʧ�ܣ��� *)

Theorem silly1 : forall ae, aeval ae = aeval ae.
Proof. try reflexivity. (* ���� [reflexivity] ����һ�� *) Qed.

Theorem silly2 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  try reflexivity. (* �� [reflexivity] ʧ��ʱһ�� *)
  apply HP. (* ������Ȼ���Ի��ַ�ʽ��������֤�� *)
Qed.

(** ���ǲ�û�����������������������ֶ�֤����ʹ�� [try]����������ͬ
    [;] ������һ������Զ���֤��ʱ����ǳ����ã�������������չʾ���� *)

(* ----------------------------------------------------------------- *)
(** *** [;] �����ԣ�����ʽ�� *)

(** ����õ���ʽ�У�[;] �����Ի��������������Ϊ���������ϲ��� [T;T']
    ���� [T] ���ɵ�_'ÿ����Ŀ��'_����ִ�� [T] ��ִ�� [T']�� *)

(** ���磬��������ƽ�������� *)

Lemma foo : forall n, 0 <=? n = true.
Proof.
  intros.
  destruct n eqn:E.
    (* ���������ִ�й�����ͬ����Ŀ��...  *)
    - (* n=0 *) simpl. reflexivity.
    - (* n=Sn' *) simpl. reflexivity.
Qed.

(** ���ǿ����� [;] ���������������� *)

Lemma foo' : forall n, 0 <=? n = true.
Proof.
  intros.
  (* [destruct] �⹹��ǰ��Ŀ�� *)
  destruct n;
  (* Ȼ���� [simpl] ����ÿ����������Ŀ�� *)
  simpl;
  (* ֮���ٶ�ÿ����������Ŀ��ִ�� [reflexivity] *)
  reflexivity.
Qed.

(** [try] ��� [;] һͬʹ�ã����ǿ��Դ�֮ǰ֤�����鷳���ظ�����ѳ����� *)

Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* �󲿷��������ֱ�Ӿ��� IH... *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
    (* ... ����ʣ�µ���� -- ANum �� APlus -- ��ͬ�� *)
  - (* ANum *) reflexivity.
  - (* APlus *)
    destruct a1 eqn:Ea1;
      (* ͬ�����󲿷��������ֱ�Ӿ��� IH�� *)
      try (simpl; simpl in IHa1; rewrite IHa1;
           rewrite IHa2; reflexivity).
    (* �� [e1 = ANum n] ʱ��������Ȥ����������� [try...] ʲôҲ������
       ��ʱ��������Ҫ�⹹ [n]����ȷ���Ż��Ƿ�Ӧ�ã����ù��ɼ�������д���� *)
    + (* a1 = ANum n *) destruct n eqn:En;
      simpl; rewrite IHa2; reflexivity.   Qed.

(** Coq ר�Ҿ������� [induction] �����Ĳ���֮��ʹ�����֡�[...; try... ]����ϰ�
    �Ա�һ�δ����������Ƶ��������Ȼ���ڷ���ʽ��֤����Ҳ��ͬ����������
    ���磬���¶Ը��Ż�����ķ���ʽ��֤������ʽ��֤���Ľṹһ�£�

    _'����'_���������е��������ʽ [a]��

       aeval (optimize_0plus a) = aeval a.

    _'֤��'_���� [a] ���й��ɡ��󲿷�������ݼ��� IH ��֤������������£�

      - ���������ĳЩ [n] �� [a = ANum n] for some [n]�����Ǳ���֤��

          aeval (optimize_0plus (ANum n)) = aeval (ANum n).

        ��һ����� [optimize_0plus] �Ķ��弴�ɵ�֤��

      - �������ĳЩ [a1] �� [a2] �� [a = APlus a1 a2]�����Ǳ���֤��

          aeval (optimize_0plus (APlus a1 a2)) = aeval (APlus a1 a2).

        ���� [a1] ���ܵ���ʽ�����ڴ󲿷ֵ������[optimize_0plus]
        ����ӱ��ʽ�򵥵صݹ���������ؽ�һ���� [a1] ��ʽ��ͬ���±��ʽ��
        ����Щ����£��������� IH ���ɵ�֤��

        ��ĳЩ [n] �� [a1 = ANum n] �Ǹ���Ȥ��������� [n = 0]����

          optimize_0plus (APlus a1 a2) = optimize_0plus a2

        �� [a2] �� IH ��������ġ���һ���棬�������ĳЩ [n'] �� [n = S n']
        ��ôͬ�� [optimize_0plus] ��򵥵صݹ������������������
        IH ���ɵ�֤�� [] *)

(** Ȼ������֤����Ȼ���ԸĽ�����һ�������[a = ANum n]���ǳ�ƽ����
    ���������Ǹ��ݹ��ɼ��軯����Ǹ������Ҫƽ����Ȼ������ȴ����������д�˳�����
    Ϊ�˸����������ð���ȥ����Ȼ����������˵�����󲿷�������������ó���
    ��ֱ�Ӵӹ��ɼ���ó���Ψһ��Ȥ������� [APlus]...��
    ����Ҳ��������ʽ��֤�����������ָĽ����������£� *)

Theorem optimize_0plus_sound'': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    (* ... or are immediate by definition *)
    try reflexivity.
  (* The interesting case is when a = APlus a1 a2. *)
  - (* APlus *)
    destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
                      rewrite IHa2; reflexivity).
    + (* a1 = ANum n *) destruct n;
      simpl; rewrite IHa2; reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(** *** [;] �����ԣ�һ����ʽ�� *)

(** [;] ��������ǰ������ļ���ʽ [T;T'] �⣬�����ָ�һ�����ʽ��
    ��� [T], [T1], ..., [Tn] ���ǲ��ԣ���ô

      T; [T1 | T2 | ... | Tn]

   ����һ������ִ�� [T]��Ȼ���� [T] ���ɵĵ�һ����ĸ����ִ�� [T1]��
   �ڵڶ�����Ŀ����ִ�� [T2]���Դ����ơ�

   ��ˣ�[T;T'] ֻ��һ�ֵ����� [Ti] Ϊ��ͬ����ʱ������Ƿ�������[T;T']
   ��������ʽ�ļ�д��

      T; [T' | T' | ... | T']
*)

(* ----------------------------------------------------------------- *)
(** *** [repeat] ������ *)

(** [repeat] �����Խ�����һ�����Բ��ظ�Ӧ����ֱ��ʧ�ܡ�����ʾ����
    [repeat] ֤���� [10] ��һ�����б��С� *)

Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.

(** ���� [repeat T] ��Զ����ʧ�ܣ�������� [T] ��δӦ�õ�ԭʼĿ���ϣ�
    ��ô [repeat] ��Ȼ��ɹ������ı�ԭʼĿ�꣨�������ظ�����Σ��� *)

Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (left; reflexivity).
  repeat (right; try (left; reflexivity)).
Qed.

(** ���� [repeat T] Ӧ�� [T] �Ĵ���Ҳû���κ��Ͻ硣��� [T] �������ǳɹ���
    ��ô�ظ� [T] ����Զѭ�������� [repeat simpl] ��һֱѭ������Ϊ [simpl]
    ���ǻ�ɹ�������Ȼ Coq �������� Gallina �е���ֵ��֤����ֹ��
    Ȼ������ȴ���ᣡȻ���Ⲣ����Ӱ�� Coq ���߼�һ���ԣ���Ϊ [repeat]
    ���������ԵĹ�������ָ�� Coq ȥ����֤�������������̷�ɢ��������ֹ����
    �Ǿ���ζ�����ǹ���֤��ʧ�ܣ����ǹ�����˴����֤���� *)

(** **** ��ϰ��3 �� (optimize_0plus_b_sound)  *)
(** ���� [optimize_0plus] �任����ı� [aexp] ��ֵ��
    ������ǿ��Խ���Ӧ�õ����г����� [bexp] �е� [aexp] �϶����ı�
    [bexp] ��ֵ�����дһ���� [bexp] ִ�д˱任�ĺ�������֤�����Ŀɿ��ԡ�
    �������Ǹ�ѧ���ķ�����������һ�����������ŵ�֤���� *)

Fixpoint optimize_0plus_b (b : bexp) : bexp
  (* �������滻�� ":= _���_����_ ." *). Admitted.

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  (* ���ڴ˴���� *) Admitted.
(** [] *)

(** **** ��ϰ��4 ��, optional (optimizer)  *)
(** _'�����ϰ'_��[optimize_0plus] ����ֻ���ڶ������Ͳ������ʽ�Ż��ķ���֮һ��
    ���дһ�����Ӵ������Ż�����֤��������ȷ�ԡ��������׵ķ������Ǵ�С�����֣�
    һ��ʼֻ��ӵ����򵥵��Ż���֤��������ȷ�ԣ�Ȼ����������������Ȥ���Ż����� *)

(* ���ڴ˴���� *)
(** [] *)

(* ================================================================= *)
(** ** �����µĲ��ԼǷ� *)

(** Coq ���ṩ�˼��ֶԲ��Խű����С���̡��ķ�ʽ��

    - ����չʾ�� [Tactic Notation] ϰ������˶��塰��д���ԡ��ļ�㷽ʽ��
      ����������Է�װ�ɵ���ָ�

    - ���ڸ��Ӹ��ӵı�̣�Coq �ṩ���ڽ��� [Ltac] ���ԣ�
      �����п��Լ����޸�֤��״̬��ԭ���������̫�����ӣ����ﲻ��չ��
      ��[Ltac] ͨ��Ҳ����Ϊ���� Coq �������������Ĳ��֣�����
      ������ڲο��ֲ���������� Coq �������ҵ�����Coq �ı�׼�����кܶ�
      [Ltac] ��������ӣ���Ҳ���Բο����ǡ�

    - ���� OCaml �� API�������Թ����ӵײ���� Coq �ڲ��ṹ�Ĳ��ԣ�
      ������ͨ Coq ���ں�����Ҫ�鷳����

    [Tactic Notation] ���������������յģ���Ϊ�ܶ���;�ṩ��ǿ���������
    ������Ǹ����ӡ� *)

Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.

(** �ⶨ����һ���µ���Ϊ [simpl_and_try] �ķ����ԣ�������һ������ [c]
    ��Ϊ�������䶨��ȼ��ڲ��� [simpl; try c]��������֤����д
    ��[simpl_and_try reflexivity.]����д��[simpl; try reflexivity.]����һ���ġ� *)

(* ================================================================= *)
(** ** [omega] ���� *)

(** [omega] ʵ����һ�־��߹��̣�������Ϊ_'Presburger ����'_��һ���߼���һ���Ӽ���
    ������������ William Pugh [Pugh 1991] (in Bib.v) �� Omega �㷨��

    ���֤��Ŀ����������Ԫ�ع��ɵ�ʽ�ӣ�

      - ��ֵ�������ӷ���[+] �� [S]����������[-] �� [pred]���Լ������˷�
        ������� Presburger �����Ĺ���Ҫ�أ�

      - ��ȹ�ϵ��[=] �� [<>]������[<=]��

      - �߼����� [/\]��[\/]��[~] �� [->]

    ��ô���� [omega] Ҫô������֤��Ŀ�꣬Ҫô�ͻ�ʧ�ܣ�����ζ�Ÿ�Ŀ��Ϊ��
    ��Ŀ��_'������'_����ʽҲ��ʧ�ܡ��� *)

Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. omega.
Qed.

(** ��ע�Ȿ�ļ����� [Require Import Coq.omega.Omega.]����*)

(* ================================================================= *)
(** ** ���෽��Ĳ��� *)

(** ��������г�һЩ������������ɡ�

     - [clear H]������������ɾ��ǰ�� [H]��

     - [subst x]�����������в��Ҽ��� [x = e] �� [e = x]��
       �����������ĺ͵�ǰĿ���е����� [x] �滻Ϊ [e] ������ü��衣

     - [subst]���滻��_'����'_���� [x = e] �� [e = x] �ļ��衣

     - [rename... into...]������֤����������ǰ������֡����磬
       ����������а�����Ϊ [x] �ı�������ô [rename x into y]
       �ͻὫ���г��ֵ� [x] ������Ϊ [y]��

     - [assumption]���������������в�����ȫƥ��Ŀ���ǰ�� [H]��
       ����ҵ��ˣ���ô����Ϊ�� [apply H] ��ͬ��

     - [contradiction]�������ڵ�ǰ�������в����߼��ȼ��� [False] ��ǰ�� [H]��
      ����ҵ��ˣ��ͽ����Ŀ�ꡣ

     - [constructor]�������ڵ�ǰ�����е� [Inductive]
       �����в��ҿ����ڽ����ǰĿ��Ĺ����� [c]������ҵ��ˣ���ô����Ϊ��
       [apply c] ��ͬ��

    ����֮��ῴ�����ǵ����ӡ� *)

(* ################################################################# *)
(** * ��ֵ��Ϊ��ϵ *)

(** �����Ѿ�չʾ���� [Fixpoint] ����ĺ��� [aeval] �� [beval]��
    ��һ��ͨ����������˼����ֵ�ķ�ʽ�����ǰ����������ʽ����ֵ��_'��ϵ'_��
    ����ע����ֵ��ϵ������Գ��ԣ���Ϊ�����з���ġ���
    �����Ȼ�ص������������������ʽ�� [Inductive] ����... *)

Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum n :
      aevalR (ANum n) n
  | E_APlus (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).

(** ��� [aevalR] ����׺�Ƿ��Ļ���ܷ��㡣������ [e \\ n]
    ��ʾ�������ʽ [e] ��ֵΪ [n]�� *)

Notation "e '\\' n"
         := (aevalR e n)
            (at level 50, left associativity)
         : type_scope.

End aevalR_first_try.

(** ʵ���ϣ�Coq �ṩ��һ���� [aevalR] ������ʹ�ô˼Ƿ��ķ�ʽ��
    �������Ա����ڽ����漰 [e \\ n] ��ʽ��֤��ʱ��������ǰ����
    [aevalR e n] ��ʽ�Ķ����������Ӷ����ٻ�����

    ���������ǣ������ȡ��������üǷ���Ȼ���ڸ��������ͬʱ�����������塣*)

Reserved Notation "e '\\' n" (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum n :
      (ANum n) \\ n
  | E_APlus e1 e2 n1 n2 :
      (e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus e1 e2 n1 n2 :
      (e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult e1 e2 n1 n2 :
      (e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1 * n2)

  where "e '\\' n" := (aevalR e n) : type_scope.

(* ================================================================= *)
(** ** �������ļǷ� *)

(** �ڷ���ʽ���������У��� [aevalR] �����ƵĹ�ϵд�ɸ����׶���
    _'�������Inference Rule��'_��ͼ����ʽ��ʮ�ַ��㣬
    ���к����Ϸ���ǰ��֤���˺����·��Ľ�������ȷ�ģ������Ѿ���
    [IndProp] һ���м��������ˣ��� *)

(** ���磬������ [E_APlus]...

      | E_APlus : forall (e1 e2: aexp) (n1 n2: nat),
          aevalR e1 n1 ->
          aevalR e2 n2 ->
          aevalR (APlus e1 e2) (n1 + n2)

    ...���������д����

                               e1 \\ n1
                               e2 \\ n2
                         --------------------                         (E_APlus)
                         APlus e1 e2 \\ n1+n2
*)

(** ��ʽ����˵���������ûʲô��̵ĺ��壺����ֻ���̺���ϵ��
    ����Խ��Ҳ�Ĺ���������������������������ÿ��ǰ����Ļ��У��Լ����߱���
    ���� [->]���������漰�����б������� [e1]��[n1] �ȣ���һ��ʼ����ȫ�������ġ�
    �����ֱ���ͨ����Ϊ_'Ԫ������Metavariables��'_���������������������ж���ı�����
    Ŀǰ�����ǵ��������ʽ�л�����������������֮���������ǡ���
    �������򼯺϶�����Ϊ������ [Inductive] �����С��ڷ���ʽ�������У�
    ��һ��Ҫô����ԣ�Ҫô��ͨ�������ڡ��� [aevalR] Ϊ�����¹����յ���С��ϵ...��
    �ľ����������� *)

(** ���磬[\\] �Ƕ����¹����յ���С��ϵ��

                             -----------                               (E_ANum)
                             ANum n \\ n

                               e1 \\ n1
                               e2 \\ n2
                         --------------------                         (E_APlus)
                         APlus e1 e2 \\ n1+n2

                               e1 \\ n1
                               e2 \\ n2
                        ---------------------                        (E_AMinus)
                        AMinus e1 e2 \\ n1-n2

                               e1 \\ n1
                               e2 \\ n2
                         --------------------                         (E_AMult)
                         AMult e1 e2 \\ n1*n2
*)

(* ================================================================= *)
(** ** ����ĵȼ۹�ϵ *)

(** ��ֵ�ĺ���ʽ�������ϵʽ����֮���һ����֤���ǳ�ֱ�ۣ� *)

Theorem aeval_iff_aevalR : forall a n,
  (a \\ n) <-> aeval a = n.
Proof.
 split.
 - (* -> *)
   intros H.
   induction H; simpl.
   + (* E_ANum *)
     reflexivity.
   + (* E_APlus *)
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   + (* E_AMinus *)
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   + (* E_AMult *)
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
 - (* <- *)
   generalize dependent n.
   induction a;
      simpl; intros; subst.
   + (* ANum *)
     apply E_ANum.
   + (* APlus *)
     apply E_APlus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   + (* AMinus *)
     apply E_AMinus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   + (* AMult *)
     apply E_AMult.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
Qed.

(** ���ǿ������÷����Խ���֤���������̡ܶ� *)

Theorem aeval_iff_aevalR' : forall a n,
  (a \\ n) <-> aeval a = n.
Proof.
  (* ��������� *)
  split.
  - (* -> *)
    intros H; induction H; subst; reflexivity.
  - (* <- *)
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity.
Qed.

(** **** ��ϰ��3 �� (bevalR)  *)
(** �ú� [aevalR] ͬ���ķ�ʽд����ϵ [bevalR]����֤�����ȼ��� [beval]�� *)

Inductive bevalR: bexp -> bool -> Prop :=
(* ���ڴ˴���� *)
.

Lemma beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
  (* ���ڴ˴���� *) Admitted.
(** [] *)

End AExp.

(* ================================================================= *)
(** ** ����ʽ�������ϵʽ���� *)

(** ���������Ͳ������ʽ��ֵ�Ķ��巽ʽ���ԣ�����ʽ�͹�ϵʽ���߾��ɣ�
    ѡ��������Ҫȡ����Ʒζ��

    Ȼ����ĳЩ����£���ֵ�Ĺ�ϵʽ����Ⱥ���ʽ����Ҫ���á�  *)

Module aevalR_division.

(** ���磬����������Ҫ�ó�����������չ�������㣺 *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp).   (* <--- ���� *)

(** ��չ [aeval] �Ķ����������Ѷ�㲢���Ǻ�ֱ�ۣ�����Ҫ����ʲô��Ϊ
    [ADiv (ANum 5) (ANum 0)] �Ľ��������Ȼ����չ [aevalR] ȴ��ֱ�ۡ�*)

Reserved Notation "e '\\' n"
                  (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),
      (ANum n) \\ n
  | E_APlus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (APlus a1 a2) \\ (n1 + n2)
  | E_AMinus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (AMinus a1 a2) \\ (n1 - n2)
  | E_AMult :  forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (AMult a1 a2) \\ (n1 * n2)
  | E_ADiv :  forall (a1 a2: aexp) (n1 n2 n3: nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (n2 > 0) ->
      (mult n2 n3 = n1) -> (ADiv a1 a2) \\ n3

where "a '\\' n" := (aevalR a n) : type_scope.

End aevalR_division.

Module aevalR_extended.

(** ���裬����ת����Ҫ�÷�ȷ���Ե���ֵ������ [any] ����չ�������㣬
    ��������������ֵʱ�����κ�������ע�⣬�ⲻͬ�������п��ܵ���ֵ������
    _'�����ϵ�'_ѡ�� -- ����û��Ϊ���ָ���κξ���ķֲ���ֻ��˵��
    _'���ܵĽ��'_���� *)

Reserved Notation "e '\\' n" (at level 50, left associativity).

Inductive aexp : Type :=
  | AAny                          (* <--- NEW *)
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

(** ͬ������չ [aeval] ��ܼ��֣���Ϊ���ڵ���ֵ_'������'_һ���ӱ��ʽ����ֵ��ȷ���Ժ�����
    ����չ [aevalR] ���޴�����... *)

Inductive aevalR : aexp -> nat -> Prop :=
  | E_Any : forall (n:nat),
      AAny \\ n                 (* <--- new *)
  | E_ANum : forall (n:nat),
      (ANum n) \\ n
  | E_APlus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (APlus a1 a2) \\ (n1 + n2)
  | E_AMinus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (AMinus a1 a2) \\ (n1 - n2)
  | E_AMult :  forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (AMult a1 a2) \\ (n1 * n2)

where "a '\\' n" := (aevalR a n) : type_scope.

End aevalR_extended.

(** ��ʱ����ܻ��ʣ�Ĭ�������Ӧ��ʹ�����ַ��
    ��������ӱ�����ϵʽ����Ӹ�����Ҫ�Ⱥ���ʽ�ĸ���ǿ��
    �������ֶ���Ķ�����̫�����ú���������ȷʵ_'����'_�����������˵��
    ���Ա���ѡ�񡣵�������ַ��������أ�

    ��ϵʽ�����һ���ŵ��ǣ����ǻ�����ţ���������⡣

    ��һ���ŵ��ǣ�Coq ����� [Inductive] �����Զ����ɲ���ķ������Ĺ���ԭ�� *)

(** ��һ���棬����ʽ����ͨ��������㣺
     - �����Ķ�����ȷ���Եģ��������в����϶��壻�����ڹ�ϵʽ������˵��
       ������Ҫ��Щ����ʱ������ʽ��֤�����ǡ�
     - ���˺��������ǻ��������� Coq �ļ��������֤�������м򻯱��ʽ��

    ���⣬����������ֱ����ȡΪ��OCaml �� Haskell �Ŀ�ִ�д��롣 *)

(** ���գ�ѡ���Ӿ����������������ֻ��Ʒζ���⡣ȷʵ���ڴ��͵� Coq
    �����У��������Կ���һ������ͬʱ�����˺���ʽ�͹�ϵʽ_'����'_���
    ����һ�������˶��ߵȼ۵������Ա���֮���֤�����ܹ����������ӽ��������л��� *)

(* ################################################################# *)
(** * �������ı��ʽ *)

(** �����ǻص� Imp �Ķ�������������������ҪΪ�����Ͳ������ʽ���ϱ�����
    Ϊ����������ǻ�������б����Ƕ�ȫ�ֵģ�������ֻ������ֵ�� *)

(* ================================================================= *)
(** ** ״̬ *)

(** ������Ҫ���ұ�����������ǵľ���ֵ��������������� [Maps]
    һ���е�ӳ�䡣������ Imp ���� [string] ��Ϊ���������͡�

    _'������״̬'_�����_'״̬'_����ʾ����ִ����ĳһʱ��_'���б���'_��ֵ�� *)

(** ��Ȼ�κθ����ĳ���ֻ���漰���������ı���������Ϊ�������
    ���Ǽ���״̬Ϊ_'���е�'_�������塣״̬�Ჶ���ڴ������е���Ϣ��
    �� Imp ������ԣ�����ÿ���������洢��һ����Ȼ����
    ������ǿ��Խ�״̬��ʾΪһ�����ַ����� [nat] ��ӳ�䣬������ [0]
    ��Ϊ�洢�е�Ĭ��ֵ�����ڸ����ӵı�����ԣ�״̬���и���ṹ�� *)

Definition state := total_map nat.

(* ================================================================= *)
(** ** �﷨  *)

(** ����ֻ��Ϊ֮ǰ���������ʽ�ټ�һ�������Ӿ�����ӱ����� *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x :  string)                   (* <----- ���� *)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

(** Ϊ��������������򵥼Ƿ�����ʾ�������׶��� *)

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

(** �������������������Լ����[X]��[Y]��[Z]��
    ������֮ǰʹ�ô�д��ĸ��ʾ�����е��ͻ�����������ڱ����п��� Imp
    ʱû��ôʹ�ö�̬��������������Ӧ�ò�������������� *)

(** [bexp] �Ķ������ڳ����������µ� [aexp] ֮�Ⲣδ���ģ� *)

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

(* ================================================================= *)
(** ** �Ƿ� *)
(** Ҫ�� Imp ������׶�д������������һЩ�Ƿ�����ʽת����Coercion����

    �ڱ������������������������������Щʲô�����Զ�֮��Coq �е� [Coercion]
    �����涨��һ�������������ӣ����Ա�����ϵͳ��ʽ�����ڽ�һ���������͵�ֵ
    ת����������͵�ֵ�����磬[AId] ��ת����������Ҫһ�� [aexp]
    ʱֱ��ʹ����ͨ���ַ��������ַ����ᱻ��ʽ���� [AId] ����װ�� *)

(** ���мǷ��ھ����_'�Ƿ�������'_���������Ա���������������ͬ�Ľ������ͻ��
    ͬ������Ҳ��ʱ����������е�ϸ�ڡ� *)

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.
Definition bool_to_bexp (b: bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.

Bind Scope aexp_scope with aexp.
Infix "+" := APlus : aexp_scope.
Infix "-" := AMinus : aexp_scope.
Infix "*" := AMult : aexp_scope.
Bind Scope bexp_scope with bexp.
Infix "<=" := BLe : bexp_scope.
Infix "=" := BEq : bexp_scope.
Infix "&&" := BAnd : bexp_scope.
Notation "'!' b" := (BNot b) (at level 60) : bexp_scope.

(** �������ǿ����� [3 + (X * 2)] ������ [APlus 3 (AMult X 2)] �ˣ�ͬ��������
    [true && !(X <= 4)] ������ [BAnd true (BNot (BLe X 4))] *)

(* ================================================================= *)
(** ** ��ֵ *)

(** �����Ͳ�����ֵ������չ���Ժ���Ȼ�ķ�ʽ�����������
    ������һ��״̬��Ϊ����Ĳ����� *)

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                (* <----- ���� *)
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

(** ����Ϊ����״̬��ȫӳ����������ļǷ�����ʹ�� [{ --> 0 }] ��Ϊ��״̬�� *)

Notation "{ a --> x }" :=
  (t_update { --> 0 } a x) (at level 0).
Notation "{ a --> x ; b --> y }" :=
  (t_update ({ a --> x }) b y) (at level 0).
Notation "{ a --> x ; b --> y ; c --> z }" :=
  (t_update ({ a --> x ; b --> y }) c z) (at level 0).
Notation "{ a --> x ; b --> y ; c --> z ; d --> t }" :=
    (t_update ({ a --> x ; b --> y ; c --> z }) d t) (at level 0).
Notation "{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u }" :=
  (t_update ({ a --> x ; b --> y ; c --> z ; d --> t }) e u) (at level 0).
Notation "{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v }" :=
  (t_update ({ a --> x ; b --> y ; c --> z ; d --> t ; e --> u }) f v) (at level 0).

Example aexp1 :
  aeval { X --> 5 } (3 + (X * 2))
  = 13.
Proof. reflexivity. Qed.

Example bexp1 :
  beval { X --> 5 } (true && !(X <= 4))
  = true.
Proof. reflexivity. Qed.

(* ################################################################# *)
(** * ָ�� *)

(** �������ǿ��Զ��� Imp _'ָ�Command��'_����ʱ����_'��䣨Statement��'_��
    ���﷨����Ϊ�ˡ� *)

(* ================================================================= *)
(** ** �﷨ *)

(** ָ�� [c] ���������� BNF �ķ�����ʽ������������Ϊ���ܹ�ʹ�� Coq
    �ļǷ����������� Imp �﷨������ѡ�������������εľ����﷨��������˵��
    ����ʹ���� [IFB] ����������п��е� [if] �Ƿ����ͻ��)

     c ::= SKIP | x ::= a | c ;; c | IFB b THEN c ELSE c FI
         | WHILE b DO c END
*)
(**
    ���磬�������� Imp ��д�Ľ׳ˣ�

     Z ::= X;;
     Y ::= 1;;
     WHILE ! (Z = 0) DO
       Y ::= Y * Z;;
       Z ::= Z - 1
     END

   ����ָ����ֹ��[Y] �ᱣ���ʼֵ [X] �Ľ׳ˡ� *)

(** ������ָ��ĳ����﷨����ʽ�����壺 *)

Inductive com : Type :=
  | CSkip
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

(** ���ڱ��ʽ�����ǿ�����һЩ [Notation] �������� Imp ����Ķ�д���ӷ��㡣 *)

Bind Scope com_scope with com.
Notation "'SKIP'" :=
   CSkip : com_scope.
Notation "x '::=' a" :=
  (CAss x a) (at level 60) : com_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : com_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : com_scope.
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity) : com_scope.

(** ����������������Щ�Ƿ���ģʽƥ����ʹ�á� *)
Open Scope com_scope.

(** ���磬�����Ǹ��׳˺�����д�� Coq ����ʽ�����壺 *)

Definition fact_in_coq : com :=
  Z ::= X;;
  Y ::= 1;;
  WHILE ! (Z = 0) DO
    Y ::= Y * Z;;
    Z ::= Z - 1
  END.

(* ================================================================= *)
(** ** ����ʾ�� *)

(** ��ֵ�� *)

Definition plus2 : com :=
  X ::= X + 2.

Definition XtimesYinZ : com :=
  Z ::= X * Y.

Definition subtract_slowly_body : com :=
  Z ::= Z - 1 ;;
  X ::= X - 1.

(* ----------------------------------------------------------------- *)
(** *** Loops *)

Definition subtract_slowly : com :=
  WHILE ! (X = 0) DO
    subtract_slowly_body
  END.

Definition subtract_3_from_5_slowly : com :=
  X ::= 3 ;;
  Z ::= 5 ;;
  subtract_slowly.

(* ----------------------------------------------------------------- *)
(** *** An infinite loop: *)

Definition loop : com :=
  WHILE true DO
    SKIP
  END.

(* ################################################################# *)
(** * ��ֵָ�� *)

(** ����������Ҫ����� Imp ָ�������ֵ��ʲô��˼��
    [WHILE] δ�ػ���ֹ����ʵ�ö���������ֵ�����е㼬��... *)

(* ================================================================= *)
(** ** ��ֵ��Ϊ������ʧ�ܵĳ��ԣ� *)

(** ������һ��Ϊָ�����ֵ�����ĳ��ԣ����Ǻ����� [WHILE] ������� *)

Fixpoint ceval_fun_no_while (st : state) (c : com)
                          : state :=
  match c with
    | SKIP =>
        st
    | x ::= a1 =>
        st & { x --> (aeval st a1) }
    | c1 ;; c2 =>
        let st' := ceval_fun_no_while st c1 in
        ceval_fun_no_while st' c2
    | IFB b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_fun_no_while st c1
          else ceval_fun_no_while st c2
    | WHILE b DO c END =>
        st  (* ��װ���� *)
  end.

(** �� OCaml �� Haskell ���ഫͳ�ĺ���ʽ��������У����ǿ����������������
    [WHILE] �������

        Fixpoint ceval_fun (st : state) (c : com) : state :=
          match c with
            ...
            | WHILE b DO c END =>
                if (beval st b)
                  then ceval_fun st (c;; WHILE b DO c END)
                  else st
          end.

    Coq ��ܾ����ֶ��壨��Error: Cannot guess decreasing argument of fix����
    �����޷��²���̶��ĵݼ�����������Ϊ������Ҫ����ĺ���������֤��ֹ��
    ȷʵ��������_'���ǻ���ֹ'_�����磬[ceval_fun] ����Ӧ�õ������ [loop]
    ����������汾��Զ������ֹ������ Coq ������һ������ʽ������ԣ�
    ���Ǹ��߼�һ�µ����ԣ�����κ�Ǳ�ڵĲ�����ֹ�������ᱻ�ܾ���������һ��
    ����Ч�ģ�������չʾ����� Coq ��������ֹ�ĵݹ麯���Ļ������ʲô����

         Fixpoint loop_false (n : nat) : False := loop_false n.

    Ҳ����˵���� [False] �����ļ�������Ա�֤����[loop_false 0] ���� [False]
    ��һ��֤����������� Coq ���߼�һ������˵�Ǹ����ѡ�

    �������������е����붼������ֹ����� [ceval_fun] �޷��� Coq ��д��
    -- ������ҪһЩ���ɺͱ�ͨ���У������Դ˺���Ļ����Ķ�
    [ImpCEvalFun] һ�£��� *)

(* ================================================================= *)
(** ** ��ֵ��Ϊһ�ֹ�ϵ *)

(** ������һ�ָ��õķ������� [ceval] �����һ��_'��ϵ'_����һ��_'����'_
    -- ������ [Prop] ������ [Type] ����������������ǰ��� [aevalR] ���������� *)

(** ����һ���ǳ���Ҫ�ĸ��ġ������ܽ����Ǵ����εı�ͨ�н�ų���֮�⣬
    ���������ǵĶ��帳���˸��������ԡ����磬�������ҪΪ��������Ӹ�����
    [any] ������ȷ���Ե����ԣ�������Ҫ����ֵ�Ķ���Ҳ�Ƿ�ȷ���Ե� --
    �������������в���ȫ�ԣ����������Բ��Ǹ������� *)

(** ���ǽ�ʹ�üǷ� [c / st \\ st'] ����ʾ [ceval] ���ֹ�ϵ��[c / st \\ st']
    ��ʾ�ڿ�ʼ״̬ [st] �����������ڽ���״̬ [st'] �²�������������Զ�����
    ��[c] ��״̬ [st] ��� [st']���� *)

(* ----------------------------------------------------------------- *)
(** *** �������� *)

(** ��������ֵ�ķ���ʽ�����壬Ϊ�˿ɶ��Ա�ʾ���������

                           ----------------                            (E_Skip)
                           SKIP / st \\ st

                           aeval st a1 = n
                   --------------------------------                     (E_Ass)
                   x := a1 / st \\ st & { x --> n }

                           c1 / st \\ st'
                          c2 / st' \\ st''
                         -------------------                            (E_Seq)
                         c1;;c2 / st \\ st''

                          beval st b1 = true
                           c1 / st \\ st'
                -------------------------------------                (E_IfTrue)
                IF b1 THEN c1 ELSE c2 FI / st \\ st'

                         beval st b1 = false
                           c2 / st \\ st'
                -------------------------------------               (E_IfFalse)
                IF b1 THEN c1 ELSE c2 FI / st \\ st'

                         beval st b = false
                    ------------------------------               (E_WhileFalse)
                    WHILE b DO c END / st \\ st

                          beval st b = true
                           c / st \\ st'
                  WHILE b DO c END / st' \\ st''
                  ---------------------------------               (E_WhileTrue)
                    WHILE b DO c END / st \\ st''
*)

(** ������������ʽ�����塣��ȷ��������������������������������Ӧ�ġ� *)

Reserved Notation "c1 '/' st '\\' st'"
                  (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st \\ st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      (x ::= a1) / st \\ st & { x --> n }
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st  \\ st' ->
      c2 / st' \\ st'' ->
      (c1 ;; c2) / st \\ st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      c1 / st \\ st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      c2 / st \\ st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      (WHILE b DO c END) / st \\ st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      c / st \\ st' ->
      (WHILE b DO c END) / st' \\ st'' ->
      (WHILE b DO c END) / st \\ st''

  where "c1 '/' st '\\' st'" := (ceval c1 st st').

(** ����ֵ����ɹ�ϵ���Ǻ����Ĵ����ǣ�������Ҫ�Լ�Ϊĳ��������ֵ��ĳ�ֽ���״̬_'����֤��'_��
    ������ֻ�ǽ��� Coq �ļ������ȥ���ˡ� *)

Example ceval_example1:
    (X ::= 2;;
     IFB X <= 1
       THEN Y ::= 3
       ELSE Z ::= 4
     FI)
   / { --> 0 } \\ { X --> 2 ; Z --> 4 }.
Proof.
  (* ���Ǳ����ṩ�м�״̬ *)
  apply E_Seq with { X --> 2 }.
  - (* ��ֵָ�� *)
    apply E_Ass. reflexivity.
  - (* if ָ�� *)
    apply E_IfFalse.
      reflexivity.
      apply E_Ass. reflexivity.  Qed.

(** **** ��ϰ��2 �� (ceval_example2)  *)
Example ceval_example2:
  (X ::= 0;; Y ::= 1;; Z ::= 2) / { --> 0 } \\
  { X --> 0 ; Y --> 1 ; Z --> 2 }.
Proof.
  (* ���ڴ˴���� *) Admitted.
(** [] *)

(** **** ��ϰ��3 ��, optional (pup_to_n)  *)
(** дһ�� Imp ����Դ� [1] �� [X] ������ֵ���������� [1 + 2 + ... + X]) ������� [Y]��
   ֤���˳������ [X] = [2] �ᰴԤ��ִ�У�����ܱ���Ԥ��Ļ�Ҫ���֣��� *)

Definition pup_to_n : com
  (* �������滻�� ":= _���_����_ ." *). Admitted.

Theorem pup_to_2_ceval :
  pup_to_n / { X --> 2 }
     \\ { X --> 2 ; Y --> 0 ; Y --> 2 ; X --> 1 ; Y --> 3 ; X --> 0 }.
Proof.
  (* ���ڴ˴���� *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** ��ֵ��ȷ���� *)

(** ����ֵ�Ӽ���ʽ���廻�ɹ�ϵʽ�����Ǹ�����ĸı䣬
    ��Ϊ�������Ǵ���ֵ������ȫ�������˹������н���˳�������������Ȼ������һ�����⣺
    ��ֵ�ĵڶ��ֶ��������һ��ƫ�����𣿴�ͬ���� [st]
    ��ʼ, �����Ƿ��п��ܰ��ղ�ͬ�ķ�ʽ��ĳ��ָ�� [c] ������ֵ��
    �Ӷ�����������ͬ�����״̬ [st'] �� [st'']?

    ʵ�����ⲻ���ܷ�������Ϊ [ceval] _'ȷʵ'_��һ��ƫ������ *)

Theorem ceval_deterministic: forall c st st1 st2,
     c / st \\ st1  ->
     c / st \\ st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1;
           intros st2 E2; inversion E2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Ass *) reflexivity.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1.
    { (* �Զ��Ե�֤�� *) apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption.
  - (* E_IfTrue��b1 ��ֵΪ true *)
      apply IHE1. assumption.
  - (* E_IfTrue��b1 ��ֵΪ false��ì�ܣ� *)
      rewrite H in H5. discriminate H5.
  - (* E_IfFalse, b1 ��ֵΪ true��ì�ܣ� *)
    rewrite H in H5. discriminate H5.
  - (* E_IfFalse��b1 ��ֵΪ false *)
      apply IHE1. assumption.
  - (* E_WhileFalse��b1 ��ֵΪ false *)
    reflexivity.
  - (* E_WhileFalse��b1 ��ֵΪ true��ì�ܣ� *)
    rewrite H in H2. discriminate H2.
  - (* E_WhileTrue, b1 ��ֵΪ false��ì�ܣ� *)
    rewrite H in H4. discriminate H4.
  - (* E_WhileTrue��b1 ��ֵΪ true *)
      assert (st' = st'0) as EQ1.
      { (* �Զ��Ե�֤�� *) apply IHE1_1; assumption. }
      subst st'0.
      apply IHE1_2. assumption.  Qed.

(* ################################################################# *)
(** * �� Imp �������� *)

(** ���ǻ���_'��������Ի�����'_�и��������̽�ֶ� Imp ������������ϵͳ�Լ�����
    ����Ŀǰֻ���ݶ���������ܶ๤���������л����ǻ�̽��һЩʵ���� *)

Theorem plus2_spec : forall st n st',
  st X = n ->
  plus2 / st \\ st' ->
  st' X = (n + 2).
Proof.
  intros st n st' HX Heval.

  (** ��ת [Heval] ʵ���ϻ�ǿ���� Coq չ�� [ceval] ��ֵ��һ������ --
      ���� [plus2] ��һ����ֵ��������������ʾ�� [st'] һ���� [st]
      ͨ���µ�ֵ [X] ��չ�����ġ� *)

  inversion Heval. subst. clear Heval. simpl.
  apply t_update_eq.  Qed.

(** **** ��ϰ��3 ��, recommended (XtimesYinZ_spec)  *)
(** ������֤�� [XtimesYinZ] �Ĺ淶��Specification���� *)

(* ���ڴ˴���� *)

(* �����޸�������һ�У� *)
Definition manual_grade_for_XtimesYinZ_spec : option (nat*string) := None.
(** [] *)

(** **** ��ϰ��3 ��, recommended (loop_never_stops)  *)
Theorem loop_never_stops : forall st st',
  ~(loop / st \\ st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE true DO SKIP END) as loopdef
           eqn:Heqloopdef.

  (** �������ۼ��衰[loopdef] ����ֹ��֮���죬���ж������ε�ì���Զ��׼���
      ���� [discriminate] һ������� *)

  (* ���ڴ˴���� *) Admitted.
(** [] *)

(** **** ��ϰ��3 �� (no_whiles_eqv)  *)
(** �������º����� *)

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP =>
      true
  | _ ::= _ =>
      true
  | c1 ;; c2 =>
      andb (no_whiles c1) (no_whiles c2)
  | IFB _ THEN ct ELSE cf FI =>
      andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END  =>
      false
  end.

(** �˶���ֻ��û�� [WHILE] ѭ���ĳ������ [true]������ [Inductive]
    д��һ������ [no_whilesR] ʹ�� [no_whilesR c] ���� [c] �Ǹ�û��
    [WHILE] ѭ���ĳ���ʱ�ſ���֤����֮��֤������ [no_whiles] �ȼۡ� *)

Inductive no_whilesR: com -> Prop :=
 (* ���ڴ˴���� *)
.

Theorem no_whiles_eqv:
   forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  (* ���ڴ˴���� *) Admitted.
(** [] *)

(** **** ��ϰ��4 �� (no_whiles_terminating)  *)
(** ���漰 [WHILE] ѭ���� Imp ����һ������ֹ���������֤������
    [no_whiles_terminating] ��˵����һ�㡣 *)
(** �������ƫ��ʹ�� [no_whiles] �� [no_whilesR]�� *)

(* ���ڴ˴���� *)

(* �����޸�������һ�У� *)
Definition manual_grade_for_no_whiles_terminating : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * ������ϰ *)

(** **** ��ϰ��3 �� (stack_compiler)  *)
(** ��ʽ���ռ������ı������������ Forth �� Postscript������������������
    Java ������������ж��������ʽ����ֵ��ʹ��_'ջ'_�����С����磬���ʽ

      (2*3)+(3*(4-2))

   �ᱻд��

      2 3 * 3 4 2 - * +

   ����ʽ������ֵ�������£��Ҳ�Ϊ����ֵ�ĳ������Ϊջ�е����ݣ���

      [ ]           |    2 3 * 3 4 2 - * +
      [2]           |    3 * 3 4 2 - * +
      [3, 2]        |    * 3 4 2 - * +
      [6]           |    3 4 2 - * +
      [3, 6]        |    4 2 - * +
      [4, 3, 6]     |    2 - * +
      [2, 4, 3, 6]  |    - * +
      [2, 3, 6]     |    * +
      [6, 6]        |    +
      [12]          |

  ����ϰ��Ŀ�����ڱ�дһ��С�ͱ����������� [aexp] �����ջ����ָ�

  ջ���Ե�ָ�������ָ��ɣ�
     - [SPush n]������ [n] ѹջ��
     - [SLoad x]���Ӵ洢�м��ر�ʶ�� [x] ������ѹջ��
     - [SPlus]��  ��ջ����������������������ӣ���������ѹջ��
     - [SMinus]�� ���ƣ�����ִ�м�����
     - [SMult]��  ���ƣ�����ִ�г˷��� *)

Inductive sinstr : Type :=
| SPush (n : nat)
| SLoad (x : string)
| SPlus
| SMinus
| SMult.

(** ���дһ��������ջ���Գ��������ֵ����Ӧ������һ��״̬��
    һ����ʾΪ�����б��ջ��ջ�����ڱ�ͷ�����Լ�һ����ʾΪָ���б�ĳ�����Ϊ���룬
    ���ڳ���ִ�к󷵻ظ�ջ����������ʾ���в�����ĺ�����

    ע�⣬��ջ�е�Ԫ����������ʱ���淶��δָ�� [SPlus]��[SMinus] �� [SMult] ָ�����Ϊ��
    ��ĳ��������˵�����������ޱ�Ҫ����Ϊ���ǵı�������Զ����������ֻ��εĳ��� *)

Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                 : list nat
  (* �������滻�� ":= _���_����_ ." *). Admitted.

Example s_execute1 :
     s_execute { --> 0 } []
       [SPush 5; SPush 3; SPush 1; SMinus]
   = [2; 5].
(* ���ڴ˴���� *) Admitted.

Example s_execute2 :
     s_execute { X --> 3 } [3;4]
       [SPush 4; SLoad X; SMult; SPlus]
   = [15; 4].
(* ���ڴ˴���� *) Admitted.

(** ���������дһ���� [aexp] �����ջ��������ĺ��������д˳����Ч��
    Ӧ���ͽ��ñ��ʽ��ֵѹ��ջ��һ�¡� *)

Fixpoint s_compile (e : aexp) : list sinstr :=
  match e with
  | ANum n => [SPush n]
  | AId x => [SLoad x]
  | APlus a1 a2 => s_compile a1 ++ s_compile a2 ++ [SPlus]
  | AMinus a1 a2 => s_compile a1 ++ s_compile a2 ++ [SMinus]
  | AMult a1 a2 => s_compile a1 ++ s_compile a2 ++ [SMult]
  end.

(** �ڶ����� [s_compile] ֮����֤������ʾ�����������Ƿ������á� *)

Example s_compile1 :
  s_compile (X - (2 * Y))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
(* ���ڴ˴���� *) Admitted.
(** [] *)

(** **** ��ϰ��4 ��, advanced (stack_compiler_correct)  *)
(** �������ǽ�֤����֮ǰ��ϰ��ʵ�ֵı���������ȷ�ԡ���ס��ջ�е�Ԫ����������ʱ��
    �淶��δָ�� [SPlus]��[SMinus] �� [SMult] ָ�����Ϊ��
    ��Ϊ������ȷ��֤���������ף��������Ҫ����ȥ�޸����ʵ�֣���

    ��֤�����¶�������Ҫ�ȳ���һ����һ����������õ�һ�����õĹ��ɼ��裬
    �����Ļ��������ֻ��һ���򵥵������ˡ� *)

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  (* ���ڴ˴���� *) Admitted.
(** [] *)

(** **** ��ϰ��3 ��, optional (short_circuit)  *)
(** �󲿷��ִ�������ԶԲ��� [and] �����ṩ�ˡ���·��ֵ���ķ�����Ҫ��
    [BAnd b1 b2] ������ֵ�����ȶ� [b1] ��ֵ��������Ϊ [false]����ô����
    [BAnd] ���ʽ����ֵ���� [false]��������� [b2] ��ֵ������[b2]
    ����ֵ����;����� [BAnd] ���ʽ��ֵ��

    ���д [beval] ����һ�ְ汾�����������ַ�ʽ�� [BAnd] ִ�ж�·��ֵ��
    ��֤�����ȼ��� [beval]����ע�����ߵȼ�ֻ����Ϊ Imp �ı��ʽ��ֵ�൱�򵥡�
    �ڸ���������иñ��ʽ���ܻᷢɢ����ʱ��·��ֵ�� [BAnd] _'����'_
    �ȼ���ԭʼ�汾����Ϊ�����ø��������ֹ���� *)

(* ���ڴ˴���� *)
(** [] *)

Module BreakImp.
(** **** ��ϰ��4 ��, advanced (break_imp)  *)
(** �� C �� Java ������ָ��ʽ����ͨ������� [break] �����Ƶ�������ж�ѭ����ִ�С�
    �ڱ���ϰ�У����ǿ������Ϊ Imp ���� [break]�����ȣ�������Ҫ�ḻ���Ե�ָ� *)

Inductive com : Type :=
  | CSkip
  | CBreak                        (* <-- ���� *)
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Notation "'SKIP'" :=
  CSkip.
Notation "'BREAK'" :=
  CBreak.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

(** ���ţ�������Ҫ���� [BREAK] ����Ϊ������ʽ����˵��ֻҪ [BREAK]
    ��ָ��������ִ�У����ͻ���ֹ�����е�ִ�в��������ڲ�Χ������ѭ��Ӧ����ֹ���źš�
    �����û���κ�Χ������ѭ������ô����ֹ�������򡣣�����״̬Ӧ����
    [BREAK] ���ִ�к��״̬��ͬ��

    ��Ҫ��֮һ���ڵ�һ�������� [BREAK] λ�ڶ��ѭ����ʱӦ����ʲô��
    ��ʱ��[BREAK] Ӧ��ֻ��ֹ_'���ڲ�'_��ѭ������ˣ���ִ��������ָ��֮��...

       X ::= 0;;
       Y ::= 1;;
       WHILE 0 <> Y DO
         WHILE TRUE DO
           BREAK
         END;;
         X ::= 1;;
         Y ::= Y - 1
       END

    ...[X] ��ֵӦΪ [1] ���� [0]��

    ���������Ϊ��һ�ַ�ʽ��ֵΪ��ֵ��ϵ���һ���βΣ�ָ��ĳ��ָ���Ƿ��ִ��
    [BREAK] ��䣺 *)

Inductive result : Type :=
  | SContinue
  | SBreak.

Reserved Notation "c1 '/' st '\\' s '/' st'"
                  (at level 40, st, s at level 39).

(** ֱ����˵��[c / st \\ s / st'] ��ʾ��� [c] �� [st] ״���¿�ʼ��
    ������ [st'] ״̬����ֹ��Χ���������ڲ�ѭ��������������
    Ҫô�յ������˳����źţ�[s = SBreak]����Ҫô��������ִ�У�[s = SContinue]����

    ��[c / st \\ s / st']����ϵ�Ķ���ǳ�������֮ǰ����Ϊһ����ֵ��ϵ
    ��[c / st \\ st']�������Ķ��� -- ����ֻ��Ҫǡ���ش�����ֹ�źš�

    - ��ָ��Ϊ [SKIP]����״̬���䣬�κ�Χ������ѭ����������ִ�С�

    - ��ָ��Ϊ [BREAK]����״̬���ֲ��䵫���� [SBreak] ���źš�

    - ��ָ��Ϊ��ֵ�������״̬���¸ñ����󶨵�ֵ����������������ִ�е��źš�

    - ��ָ��Ϊ [IFB b THEN c1 ELSE c2 FI] ����ʽ������ Imp ��ԭʼ�������״̬��
      ����֮�����ǻ�Ҫ�ӱ�ѡ��ִ�еķ�֧�д����źš�

    - ��ָ��Ϊһϵ�� [c1 ;; c2]����������ִ�� [c1]�������������
      [SBreak]�����Ǿ����� [c2] ��ִ�в��� [SBreak] ���źŴ�������Χ����������;
      ���״̬��ִ�� [c1] ���õ���ͬ������������ִ���� [c1] ���״̬��ִ��
      [c2] �������������������źš�

    - ��󣬶������� [WHILE b DO c END] ��ѭ��������������ʹ�ǰ��ͬ��
      Ψһ�Ĳ�ͬ�ǣ��� [b] ��ֵΪ [true] ʱִ�� [c] ��������������źš�
      ���ź�Ϊ [SContinue]������ԭʼ�������ִ�С�����������ֹ��ѭ����ִ�У�
      ������״̬�뵱ǰ����ִ�еĽ����ͬ������������������� [BREAK]
      ֻ��ֹ���ڲ��ѭ������� [WHILE] ���� [SContinue] ���źš� *)

(** ������������������� [ceval] ��ϵ�Ķ��塣 *)

Inductive ceval : com -> state -> result -> state -> Prop :=
  | E_Skip : forall st,
      CSkip / st \\ SContinue / st
  (* ���ڴ˴���� *)

  where "c1 '/' st '\\' s '/' st'" := (ceval c1 st s st').

(** ����֤���㶨��� [ceval] ���������ʣ� *)

Theorem break_ignore : forall c st st' s,
     (BREAK;; c) / st \\ s / st' ->
     st = st'.
Proof.
  (* ���ڴ˴���� *) Admitted.

Theorem while_continue : forall b c st st' s,
  (WHILE b DO c END) / st \\ s / st' ->
  s = SContinue.
Proof.
  (* ���ڴ˴���� *) Admitted.

Theorem while_stops_on_break : forall b c st st',
  beval st b = true ->
  c / st \\ SBreak / st' ->
  (WHILE b DO c END) / st \\ SContinue / st'.
Proof.
  (* ���ڴ˴���� *) Admitted.
(** [] *)

(** **** ��ϰ��3 ��, advanced, optional (while_break_true)  *)
Theorem while_break_true : forall b c st st',
  (WHILE b DO c END) / st \\ SContinue / st' ->
  beval st' b = true ->
  exists st'', c / st'' \\ SBreak / st'.
Proof.
(* ���ڴ˴���� *) Admitted.
(** [] *)

(** **** ��ϰ��4 ��, advanced, optional (ceval_deterministic)  *)
Theorem ceval_deterministic: forall (c:com) st st1 st2 s1 s2,
     c / st \\ s1 / st1  ->
     c / st \\ s2 / st2 ->
     st1 = st2 /\ s1 = s2.
Proof.
  (* ���ڴ˴���� *) Admitted.

(** [] *)
End BreakImp.

(** **** ��ϰ��4 ��, optional (add_for_loop)  *)
(** Ϊ��������� C ���� [for] ѭ��ָ����� [ceval] �Ķ���������
    [for] ѭ����������� [for] ѭ�������ʹ�ñ��ļ��е�����֤������
    Coq �����ܡ�

    [for] ѭ���Ĳ���Ӧ������ (a) һ����ʼ��ִ�е���䣻
    (b) һ����ѭ����ÿ�ε����ж�ִ�еĲ��ԣ���������ѭ���Ƿ�Ӧ��������
    (c) һ����ѭ����ÿ�ε������ִ�е���䣬�Լ� (d) һ������ѭ��������
    ���㲻�ع���Ϊ [for] ����һ������ļǷ������������ϲ������������ȥ������ *)

(* ���ڴ˴���� *)
(** [] *)



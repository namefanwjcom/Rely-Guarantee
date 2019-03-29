(** * Maps: ȫӳ����ƫӳ�� *)

(** _'ӳ�䣨Map��'_����_'�ֵ䣨Dictionary��'_����һ�ַǳ��ձ�����ݽṹ��
    �ڱ��������������������֮����½������ǻ����õ�����
    ӳ��Ҳ�ʺ�����֮ǰѧ���ĸ�������о�����������ڸ߽׺���֮�⹹�����ݽṹ
    ���� [Basics] �� [Poly]���Լ�ͨ����ӳ������֤������ [IndProp]����

    ���ǻᶨ������ӳ�䣺�ڲ��ҵļ�������ʱ��_'ȫӳ��'_�᷵�ء�Ĭ�ϡ�Ԫ�أ�
    ��_'ƫӳ��'_��᷵��һ�� [option] ��ָʾ�ɹ�����ʧ�ܡ����߸���ǰ�������壬
    ��ʹ�� [None] Ĭ��Ԫ�ء� *)

(* ################################################################# *)
(** * Coq ��׼�� *)

(** ��ʼǰ��С�廰...

    ������Ŀǰѧ�����½ڲ�ͬ����������ͨ�� [Require Import] ����֮ǰ���½�
    ����ȻҲ�Ͳ����ӵ��������½ڣ����ӱ��¿�ʼ���������ǽ�ֱ�Ӵ�
    Coq ��׼���е�����Ҫ�Ķ���Ͷ���Ȼ��Ӧ�ò���ע�⵽�����
    ��Ϊ����һֱС�ĵؽ��Լ��Ķ���Ͷ�����������׼���еĲ��ֱ���һ�£�
    ���������������ظ��� *)

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Export Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Import ListNotations.

(** ��׼����ĵ���
    http://coq.inria.fr/library/��

    [Search] ָ������ڲ����漰�������Ͷ���Ķ������ǻ���ʱ������Ϥһ������ *)

(* ################################################################# *)
(** * ��ʶ�� *)

(** First, we need a type for the keys that we use to index into our
    maps.  In [Lists.v] we introduced a fresh type [id] for this
    purpose; for the rest of _Software Foundations_ we will use the
    [string] type from Coq's standard library. *)

(** To compare strings, we define the function [eqb_string], which
    internally uses the function [string_dec] from Coq's string
    library. *)

Definition eqb_string x y :=
  if string_dec x y then true else false.

(** ������ [string_dec] ������ Coq ���ַ�����׼�⡣�����鿴
    [string_dec] �Ľ�����ͣ��ͻᷢ���䷵��ֵ�����Ͳ����� [bool]��
    ����һ������ [{x = y} + {x <> y}] �����ͣ����� [sumbool] ���ͣ�
    �����Կ���������֤�ݵĲ������͡�����ʽ����˵��һ�� [sumbool]
    ���͵�Ԫ��Ҫô������������ȵ�֤����Ҫô�������ǲ���ȵ�֤����
    ��һ����ǩһ����ָ����������һ����������Ŀǰ��˵������԰�������һ��
    ���ڵ� [bool]���� *)

(** Now we need a few basic properties of string equality... *)
Theorem eqb_string_refl : forall s, true = eqb_string s s.
Proof. intros s. unfold eqb_string. destruct (string_dec s s) as [|Hs].
  - reflexivity.
  - destruct Hs. reflexivity.
Qed.

(** The following useful property follows from an analogous
    lemma about strings: *)

Theorem eqb_string_true_iff : forall x y : string,
  eqb_string x y = true <-> x = y.
Proof.
   intros x y.
   unfold eqb_string.
   destruct (string_dec x y) as [|Hs].
   - subst. split. reflexivity. reflexivity.
   - split.
     + intros contra. discriminate contra.
     + intros H. rewrite H in Hs. destruct Hs. reflexivity.
Qed.

(** ���Ƶأ� *)

Theorem eqb_string_false_iff : forall x y : string,
  eqb_string x y = false
  <-> x <> y.
Proof.
  intros x y. rewrite <- eqb_string_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.

(** This handy variant follows just by rewriting: *)

Theorem false_eqb_string : forall x y : string,
   x <> y -> eqb_string x y = false.
Proof.
  intros x y. rewrite eqb_string_false_iff.
  intros H. apply H. Qed.

(* ################################################################# *)
(** * ȫӳ�� *)

(** �ڱ����У����ǵ���Ҫ������ǹ���һ��ƫӳ��Ķ��壬����Ϊ����������֮ǰ��
    [Lists]һ���п������Ǹ����ټ��ϰ�������Ϊ������

    ������һ�Σ����ǽ�ʹ��_'����'_���ǡ���-ֵ���Ե��б�������ӳ�䡣
    ���ֱ�ʾ�������ŵ��������ṩ��ӳ�����_'������'_���ӽǣ�
    ������ͬ��ʽ��Ӧ��ѯ������ӳ�佫����ʾΪ��ȫ��ͬ�Ķ�������һ��һ���ĺ�������
    ����ֻ�ǡ��ȼۡ������ݽṹ���ⷴ��������ʹ��ӳ���֤���� *)

(** ���ǻ����������ƫӳ�䡣���ȣ����Ƕ���һ��_'ȫӳ��'_���ͣ�
    ����ĳ��ӳ���в��Ҳ����ڵļ�ʱ�᷵��Ĭ��ֵ�� *)

Definition total_map (A:Type) := string -> A.

(** ֱ������˵��һ��Ԫ������Ϊ [A] ��ȫӳ�䲻�����Ǹ����� [string]
    ������ [A] �ĺ����� *)

(** �������� [t_empty] һ��Ĭ��Ԫ�أ��������һ���յ�ȫӳ�䡣
    ��ӳ����Ӧ�õ��κ��ַ���ʱ���᷵��Ĭ��Ԫ�ء� *)

Definition t_empty {A:Type} (v : A) : total_map A :=
  (fun _ => v).

(** ����Ȥ���� [update] ����������֮ǰһ��������һ��ӳ�� [m]��һ���� [x]
    �Լ�һ��ֵ [v]��������һ���� [x] ӳ�䵽 [v] ����ӳ�䣻����������
    [m] ��ԭ���ı���һ�¡� *)

Definition t_update {A:Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if eqb_string x x' then v else m x'.

(** �˶����Ǹ��߽ױ�̵ĺ����ӣ�[t_update] ����һ��_'����'_ [m]
    ������һ���µĺ��� [fun x' => ...]�����ı����������ӳ��һ�¡� *)

(** ���磬���ǿ��Թ���һ���� [string] �� [bool] ��ӳ�䣬���� ["foo"]
    �� ["bar"] ӳ�䵽 [true]����������ӳ�䵽 [false]������������ *)

Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true)
           "bar" true.

(** ����������������һЩ�µļǷ�������ӳ���ʹ�á� *)

(** ���ȣ����ǻ�ʹ�����¼Ƿ�������һ��Ĭ��ֵ�������յ�ȫӳ�䡣 *)
Notation "{ --> d }" := (t_empty d) (at level 0).

(** Ȼ����������һ�ַ���ļǷ���ͨ��һЩ������չ���е�ӳ�䡣 *)

(** �����ּǷ��Ķ����е����Ϊ Coq �ļǷ����Ʋ�̫��Ӧ�ݹ�Ƿ���
    ����������������õ��ˡ�) *)

Notation "m '&' { a --> x }" :=
  (t_update m a x) (at level 20).
Notation "m '&' { a --> x ; b --> y }" :=
  (t_update (m & { a --> x }) b y) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z }" :=
  (t_update (m & { a --> x ; b --> y }) c z) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z ; d --> t }" :=
    (t_update (m & { a --> x ; b --> y ; c --> z }) d t) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z ; d --> t ; e --> u }" :=
    (t_update (m & { a --> x ; b --> y ; c --> z ; d --> t }) e u) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v }" :=
    (t_update (m & { a --> x ; b --> y ; c --> z ; d --> t ; e --> u }) f v) (at level 20).

(** ǰ��� [examplemap] ���ڿ��Զ������£� *)

Definition examplemap' :=
  { --> false } & { "foo" --> true ; "bar" --> true }.

(** ������������ȫӳ��Ķ��塣ע���������趨�� [find] ������
    ��Ϊ���������Ǹ�����Ӧ�ã� *)

Example update_example1 : examplemap' "baz" = false.
Proof. reflexivity. Qed.

Example update_example2 : examplemap' "foo" = true.
Proof. reflexivity. Qed.

Example update_example3 : examplemap' "quux" = false.
Proof. reflexivity. Qed.

Example update_example4 : examplemap' "bar" = true.
Proof. reflexivity. Qed.

(** Ϊ���ں�����½���ʹ��ӳ�䣬������ҪһЩ��������ֵĻ�����ʵ�� *)

(** ������û�н����������ϰ��ҲҪȷ��͸���������������ĳ����� *)

(** ��������Щ֤����Ҫ�����������Թ���������[Logic]һ�������۹������� *)

(** **** ��ϰ��1 ��, optional (t_apply_empty)  *)
(** ���ȣ���ӳ��������еļ����᷵��Ĭ��Ԫ�أ�������ӳ�����Ƿ���Ĭ��Ԫ�أ��� *)

Lemma t_apply_empty:  forall (A:Type) (x: string) (v: A), { --> v } x = v.
Proof.
  (* ���ڴ˴���� *) Admitted.
(** [] *)

(** **** ��ϰ��2 ��, optional (t_update_eq)  *)
(** ���ţ������ӳ�� [m] �ļ� [x] ������ֵ����Ϊ [v]��Ȼ���� [update]
    ��������ӳ���в��� [x]���ͻ�õ� [v]����������ĳ������ӳ�䣬
    �������ͻ�õ����º��ֵ���� *)

Lemma t_update_eq : forall A (m: total_map A) x v,
  (m & {x --> v}) x = v.
Proof.
  (* ���ڴ˴���� *) Admitted.
(** [] *)

(** **** ��ϰ��2 ��, optional (t_update_neq)  *)
(** ���⣬�����ӳ�� [m] �ļ� [x1] ���º��ڷ��صĽ���в���_'��һ��'_��
    [x2]����ô�õ��Ľ������ [m] �в������Ľ����ͬ
    ����������ĳ������ӳ�䣬��Ӱ����������ӳ�䣩�� *)

Theorem t_update_neq : forall (X:Type) v x1 x2
                         (m : total_map X),
  x1 <> x2 ->
  (m & {x1 --> v}) x2 = m x2.
Proof.
  (* ���ڴ˴���� *) Admitted.
(** [] *)

(** **** ��ϰ��2 ��, optional (t_update_shadow)  *)
(** �����ӳ�� [m] �ļ� [x] ������ֵ����Ϊ [v1] ���ֽ�ͬһ���� [x]
    ����Ϊ��һ��ֵ [v2]����ô������ӳ��������ڶ��� [update] Ӧ���� [m]
    ���õ���ӳ�����һ�£�������Ӧ�õ�ͬһ��ʱ�����Ľ����ͬ���� *)

Lemma t_update_shadow : forall A (m: total_map A) v1 v2 x,
    m & {x --> v1 ; x --> v2} = m & {x --> v2}.
Proof.
  (* ���ڴ˴���� *) Admitted.
(** [] *)

(** �����������ȫӳ���������ԣ���[IndProp]һ��������Ļ�ӳ��
    ��Reflection idioms����֤����ʮ�ַ��㡣��������ͨ��֤��������_'��ӳ����'_��
    �� [id] �ϵ���ȹ�ϵ�����벼������ [eqb_id] ����������*)

(** **** ��ϰ��2 ��, optional (eqb_stringP)  *)
(** �����[IndProp]һ���ж� [eqb_natP] ��֤����֤���������� *)

Lemma eqb_stringP : forall x y, reflect (x = y) (eqb_string x y).
Proof.
  (* ���ڴ˴���� *) Admitted.
(** [] *)

(** ���ڣ����� [string] ���͵��ַ��� [x1] �� [x2]�����ǿ�����ʹ��
    [destruct (eqb_stringP x1 x2)] �� [eqb_string x1 x2]
    �Ľ�����з������۵�ͬʱ�����ɹ��� [x1] �� [x2] ���� [=] �������ϣ�
    ����ȹ�ϵǰ�ᡣ *)

(** **** ��ϰ��2 �� (t_update_same)  *)
(** �����[IndProp]һ���е�ʾ������ [eqb_stringP] ��֤�����¶���
    �������ˣ����������ӳ�� [m] ���Ѿ���� [x] �������ֵ������ [x]��
    ��ô������ [m] ��ȣ� *)

Theorem t_update_same : forall X x (m : total_map X),
    m & { x --> m x } = m.
  Proof.
  (* ���ڴ˴���� *) Admitted.
(** [] *)

(** **** ��ϰ��3 ��, recommended (t_update_permute)  *)
(** ʹ�� [eqb_stringP] ��֤�����һ�� [update] ���������ʣ�
    ������Ǹ�����ӳ�� [m] ��������ͬ�ļ�����ô���µ�˳���޹ؽ�Ҫ�� *)

Theorem t_update_permute : forall (X:Type) v1 v2 x1 x2
                             (m : total_map X),
  x2 <> x1 ->
  m & { x2 --> v2 ; x1 --> v1 }
  =  m & { x1 --> v1 ; x2 --> v2 }.
Proof.
  (* ���ڴ˴���� *) Admitted.
(** [] *)

(* ################################################################# *)
(** * ƫӳ�� *)

(** ���������ȫӳ��֮�϶���_'ƫӳ��'_��Ԫ������Ϊ [A] ��ƫӳ�䲻�����Ǹ�
    Ԫ������Ϊ [option A]��Ĭ��Ԫ��Ϊ [None] ��ȫӳ�䡣 *)

Definition partial_map (A:Type) := total_map (option A).

Definition empty {A:Type} : partial_map A :=
  t_empty None.

Definition update {A:Type} (m : partial_map A)
           (x : string) (v : A) :=
  m & { x --> (Some v) }.

(** ������˫������Ϊƫӳ���������ƵļǷ��� **)

Notation "m '&' {{ a --> x }}" :=
  (update m a x) (at level 20).
Notation "m '&' {{ a --> x ; b --> y }}" :=
  (update (m & {{ a --> x }}) b y) (at level 20).
Notation "m '&' {{ a --> x ; b --> y ; c --> z }}" :=
  (update (m & {{ a --> x ; b --> y }}) c z) (at level 20).
Notation "m '&' {{ a --> x ; b --> y ; c --> z ; d --> t }}" :=
    (update (m & {{ a --> x ; b --> y ; c --> z }}) d t) (at level 20).
Notation "m '&' {{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u }}" :=
    (update (m & {{ a --> x ; b --> y ; c --> z ; d --> t }}) e u) (at level 20).
Notation "m '&' {{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v }}" :=
    (update (m & {{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u }}) f v) (at level 20).

(** �������ǽ����й���ȫӳ��Ļ�������ֱ��ת���ɶ�Ӧ��ƫӳ������ *)

Lemma apply_empty : forall (A: Type) (x: string),  @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.

Lemma update_eq : forall A (m: partial_map A) x v,
    (m & {{ x --> v }}) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

Theorem update_neq : forall (X:Type) v x1 x2
                       (m : partial_map X),
  x2 <> x1 ->
  (m & {{ x2 --> v }}) x1 = m x1.
Proof.
  intros X v x1 x2 m H.
  unfold update. rewrite t_update_neq. reflexivity.
  apply H. Qed.

Lemma update_shadow : forall A (m: partial_map A) v1 v2 x,
    m & {{ x --> v1 ; x --> v2 }} = m & {{x --> v2}}.
Proof.
  intros A m v1 v2 x1. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall X v x (m : partial_map X),
  m x = Some v ->
  m & {{x --> v}} = m.
Proof.
  intros X v x m H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (X:Type) v1 v2 x1 x2
                                (m : partial_map X),
  x2 <> x1 ->
  m & {{x2 --> v2 ; x1 --> v1}}
  = m & {{x1 --> v1 ; x2 --> v2}}.
Proof.
  intros X v1 v2 x1 x2 m. unfold update.
  apply t_update_permute.
Qed.



Require Import Nat.
Require Import List.
Require Import Program.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Euclid.
Require Import Coq.Init.Logic.
Require Import Coq.Program.Wf.
Require Import Coq.Logic.Classical_Prop.

Definition sort : Type :=
  forall (A : Type), (A -> A -> bool) -> list A -> list A.

Definition sort_length (f : sort) : Prop :=
  forall (A : Type) (le : A -> A -> bool) (xs : list A),
  length (f A le xs) = length xs.

Inductive list_sorted {A : Type} (le : A -> A -> bool): list A -> Prop :=
| sorted_nil : list_sorted le []
| sorted_cons :
    forall x xs,
    Forall (fun y => le x y = true) xs
    -> list_sorted le xs
    -> list_sorted le (x :: xs).

Definition sort_sorted (f : sort) : Prop :=
  forall (A : Type) (le : A -> A -> bool) (xs : list A),
  (forall h k l : A, le h k = true -> le k l = true -> le h l = true) ->
  (forall k l : A, le k l = le l k -> l = k) ->
  (forall k : A, le k k = true) ->
  list_sorted le (f A le xs).

Definition sort_members (f : sort) : Prop :=
  forall (A : Type) (le : A -> A -> bool) (xs : list A) (x : A),
  In x xs <-> In x (f A le xs).

Definition valid_sort sort : Prop :=
  sort_length sort /\ sort_sorted sort /\ sort_members sort.

Fixpoint split_at {A : Type} (n : nat) (xs : list A) : list A * list A :=
  match n, xs with
  | O, _ => ([], xs)
  | S _, [] => ([], [])
  | S n', x :: xs' =>
      let (ys, zs) := split_at n' xs' in
      (x :: ys, zs)
  end.

Theorem list_sorted_cons :
  forall (A : Type) (le : A -> A -> bool) (a b : A) (xs : list A),
  (forall h k l : A, le h k = true -> le k l = true -> le h l = true) ->
  le a b = true -> list_sorted le (b :: xs) ->
  list_sorted le (a :: b :: xs).
Proof.
  intros A le a b xs le_trans le_a_b H.
  constructor; try assumption.
  constructor; try assumption.
  inversion H.
  apply Forall_impl with (P:=fun y : A => le b y = true); try assumption.
  intro. apply le_trans. assumption.
Qed.

Theorem list_sorted_cons_cons :
  forall (A : Type) (le : A -> A -> bool) (a b : A) (xs : list A),
  list_sorted le (a :: b :: xs) -> le a b = true.
Proof.
  intros A le a b xs H.
  inversion H.
  destruct (Forall_forall (fun y : A => le a y = true) (b :: xs)) as (Hall & _).
  apply Hall.
  assumption.
  constructor.
  reflexivity.
Qed.

Theorem list_sorted_cons_cons_sorted :
  forall (A : Type) (le : A -> A -> bool) (a b : A) (xs : list A),
  list_sorted le (a :: b :: xs) -> list_sorted le (a :: xs).
Proof.
  intros A le a b xs H.
  constructor.
  - inversion H. inversion H2. assumption.
  - inversion H. inversion H3. assumption.
Qed.

Lemma split_at_concat : forall (A : Type) (n : nat) (xs ys zs : list A),
    (ys, zs) = split_at n xs -> ys ++ zs = xs.
Proof.
  induction n; induction xs;
    simpl; intros ys zs H; try (inversion H; reflexivity).
  destruct (split_at n xs) as (ys' & zs') eqn:S in H. inversion H. simpl.
  rewrite (IHn xs ys' zs' (eq_sym S)). reflexivity.
Qed.

Lemma split_at_length : forall (A : Type) (n : nat) (xs ys zs : list A),
    n < length xs -> (ys, zs) = split_at n xs -> length ys = n.
Proof.
  intros A n.
  induction n as [|n'].
  - intros xs ys zs Hlt Hsplit. simpl in Hsplit. inversion Hsplit. reflexivity.
  - induction xs as [|x xs'].
    * intros ys zs Hlt Hsplit. inversion Hlt.
    * intros ys zs Hlt Hsplit.
      simpl in Hsplit. destruct (split_at n' xs') eqn:S in Hsplit.
      inversion Hsplit. simpl.
      simpl in Hlt. apply lt_S_n in Hlt.
      rewrite (IHn' xs' l l0 Hlt (eq_sym S)).
      reflexivity.
Qed.

Definition split {A : Type} (xs : list A) : list A * list A :=
  match xs with
  | [] => ([], [])
  | _ :: _ =>
    match eucl_dev 2 (gt_Sn_O 1) (length xs) with
    | divex _ _ q r _ _ => split_at q xs
    end
  end.

Theorem split_concat :
  forall (A : Type) (xs ys zs : list A), (ys, zs) = split xs -> ys ++ zs = xs.
Proof.
  induction xs; try (intros ys zs H; inversion H; reflexivity).
  unfold split.
  destruct (eucl_dev 2 (gt_Sn_O 1) (length (a :: xs))).
  apply split_at_concat.
Qed.

Theorem split_length :
  forall (A : Type) (xs ys zs : list A),
  (ys, zs) = split xs -> length ys + length zs = length xs.
Proof.
  intros A xs ys zs H.
  rewrite <- split_concat with (xs:=xs) (ys:=ys) (zs:=zs); try assumption.
  symmetry. apply app_length.
Qed.

Theorem split_members :
  forall (A : Type) (a : A) (xs ys zs : list A),
  (ys, zs) = split xs -> In a ys \/ In a zs <-> In a xs.
Proof.
  intros A a xs ys zs Hsplit.
  split; intro H.
  - rewrite <- split_concat with (ys:=ys) (zs:=zs); try assumption.
    apply in_or_app; assumption.
  - rewrite <- split_concat with (ys:=ys) (zs:=zs) in H; try assumption.
    apply in_app_or; assumption.
Qed.

Theorem split_smaller_l :
  forall (A : Type) (a b : A) (xs ys zs : list A),
  (ys, zs) = split (a :: b :: xs) -> length ys < length (a :: b :: xs).
Proof.
  intros A a b xs ys zs H.
  simpl in H. destruct (eucl_dev 2 (gt_Sn_O 1) (S (S (length xs)))).
  destruct q.
  - simpl in e. unfold gt in g. rewrite <- e in g.
    repeat apply lt_S_n in g. inversion g.
  - assert (forall n : nat, n < S (n * 2) + r).
    {
      induction n.
      * apply Nat.lt_0_succ.
      * simpl. apply lt_n_S. rewrite <- plus_Sn_m.
        apply Nat.lt_lt_succ_r. apply IHn.
    }
    rewrite split_at_length with (n:=S q) (xs:=a::b::xs) (zs:=zs);
      apply H || simpl; rewrite e; simpl; apply lt_n_S; apply H0.
Qed.

Theorem split_smaller_r : forall (A : Type) (a b : A) (xs ys zs : list A),
    (ys, zs) = split (a :: b :: xs) -> length zs < length (a :: b :: xs).
Proof.
  intros A a b xs ys zs H.
  rewrite <- split_concat with (xs:=a::b::xs) (ys:=ys) (zs:=zs).
  - rewrite app_length. apply Nat.lt_add_pos_l.
    simpl in H. destruct (eucl_dev 2 (gt_Sn_O 1) (S (S (length xs)))).
    destruct q.
    * simpl in e. rewrite <- e in g.
      repeat apply lt_S_n in g. inversion g.
    * rewrite split_at_length with (n:=S q) (xs:=a::b::xs) (ys:=ys) (zs:=zs).
      apply Nat.lt_0_succ.
      simpl. rewrite e. rewrite Nat.mul_comm. apply lt_plus_trans. simpl.
      apply lt_n_S. apply Nat.lt_add_pos_r. apply Nat.lt_0_succ.
      assumption.
  - assumption.
Qed.

Program Fixpoint merge_sorted_lists {A : Type} (le : A -> A -> bool)
    (xs ys : list A) { measure (length (xs ++ ys)) } : list A :=
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x :: xs', y :: ys' =>
      if le x y
        then x :: merge_sorted_lists le xs' ys
        else y :: merge_sorted_lists le xs ys'
  end.
Next Obligation.
  rewrite app_length. rewrite app_length. simpl.
  destruct (length xs'); try auto.
  simpl. repeat rewrite <- Nat.succ_lt_mono. rewrite <- Nat.add_lt_mono_l.
  auto.
Qed.

Lemma merge_sorted_lists_body :
  forall (A : Type) (le : A -> A -> bool) (xs ys : list A),
  merge_sorted_lists le xs ys =
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x :: xs', y :: ys' =>
      if le x y
        then x :: merge_sorted_lists le xs' ys
        else y :: merge_sorted_lists le xs ys'
  end.
Proof.
  intros A le xs ys.
  unfold merge_sorted_lists.
  unfold merge_sorted_lists_func; rewrite WfExtensionality.fix_sub_eq_ext;
    fold merge_sorted_lists_func; simpl.
  destruct xs; destruct ys; try reflexivity.
Qed.

Lemma merge_sorted_lists_length :
  forall (A : Type) (le : A -> A -> bool) (xs ys : list A),
  length (merge_sorted_lists le xs ys) = length xs + length ys.
Proof.
  intros A le xs ys.
  rewrite merge_sorted_lists_body.
  revert ys; induction xs as [|x xs']; try reflexivity.
  induction ys as [|y ys']; simpl; try rewrite Nat.add_0_r; try reflexivity.
  destruct (le x y).
  - simpl. apply eq_S. rewrite merge_sorted_lists_body.
    apply IHxs' with (ys:=y::ys').
  - simpl. apply eq_S. rewrite merge_sorted_lists_body.
    rewrite <- plus_n_Sm. apply IHys'.
Qed.

Theorem merge_sorted_lists_nil_l :
  forall (A : Type) (le : A -> A -> bool) (xs : list A),
  merge_sorted_lists le [] xs = xs.
Proof.
  intros A le xs.
  rewrite merge_sorted_lists_body.
  reflexivity.
Qed.

Theorem merge_sorted_lists_nil_r :
  forall (A : Type) (le : A -> A -> bool) (xs : list A),
  merge_sorted_lists le xs [] = xs.
Proof.
  intros A le xs.
  rewrite merge_sorted_lists_body.
  destruct xs; reflexivity.
Qed.

Lemma merge_sorted_lists_singleton_le_l :
  forall (A : Type) (le : A -> A -> bool) (a y : A) (ys : list A),
  le a y = true ->
  merge_sorted_lists le [a] (y :: ys) = a :: y :: ys.
Proof.
  intros A le a y ys H.
  rewrite merge_sorted_lists_body. rewrite H.
  reflexivity.
Qed.

Lemma merge_sorted_lists_singleton_le_r :
  forall (A : Type) (le : A -> A -> bool) (a y : A) (ys : list A),
  (forall k l : A, le k l = le l k -> l = k) ->
  list_sorted le (y :: ys) -> le a y = true ->
  merge_sorted_lists le (y :: ys) [a] = a :: y :: ys.
Proof.
  intros A le a y ys le_antisymm Hsorted le_a_y.
  rewrite merge_sorted_lists_body.
  destruct (le y a) eqn:le_y_a.
  - rewrite <- le_antisymm  with (k:=a) (l:=y); try assumption.
    induction ys as [|y' ys]; try reflexivity.
    destruct (le y' y) eqn:le_yp_a.
    * inversion Hsorted.
      assert (y = y') as Hyyp.
      {
        destruct (Forall_forall (fun y0 : A => le y y0 = true) (y' :: ys))
          as (Hall & _).
        rewrite le_antisymm with (k:=y') (l:=y);
          try assumption; try reflexivity.
        rewrite Hall. assumption. assumption. constructor. reflexivity.
      }
      rewrite merge_sorted_lists_body. rewrite le_yp_a. rewrite <- Hyyp.
      rewrite IHys.
      repeat rewrite merge_sorted_lists_body. reflexivity.
      rewrite <- Hyyp in H2. assumption.
    * rewrite merge_sorted_lists_body. rewrite le_yp_a.
      rewrite merge_sorted_lists_body. reflexivity.
    * rewrite le_a_y; rewrite le_y_a; reflexivity.
  - rewrite merge_sorted_lists_nil_r.
    reflexivity.
Qed.

Theorem merge_sorted_lists_same_head :
  forall (A : Type) (le : A -> A -> bool) (a : A) (xs ys : list A),
  (forall k l : A, le k l = le l k -> l = k) ->
  list_sorted le (a :: xs) -> list_sorted le (a :: ys) ->
  merge_sorted_lists le (a :: xs) (a :: ys)
    = a :: a :: merge_sorted_lists le xs ys.
Proof.
  intros A le a xs ys le_antisymm. revert ys.
  induction xs as [|x xs']; induction ys as [|y ys']; intros H1 H2.
  - repeat rewrite merge_sorted_lists_body. destruct (le a a); reflexivity.
  - rewrite merge_sorted_lists_body.
    destruct (le a a).
    * repeat rewrite merge_sorted_lists_body. reflexivity.
    * rewrite merge_sorted_lists_singleton_le_l; try reflexivity.
      apply list_sorted_cons_cons with (xs:=ys').
      assumption.
  - destruct (le a a) eqn:le_a_a;
      rewrite merge_sorted_lists_nil_r; rewrite merge_sorted_lists_body;
      rewrite le_a_a; try (rewrite merge_sorted_lists_body; reflexivity).
    rewrite merge_sorted_lists_singleton_le_r;
      inversion H1; try (reflexivity || assumption).
    destruct (Forall_forall (fun y : A => le a y = true) (x :: xs'))
      as (Hall & _).
    apply Hall with (x0:=x). assumption. constructor; reflexivity.

  (* xs := x :: xs' and ys := y :: ys' *)
  - rewrite merge_sorted_lists_body.
    destruct (le a a) eqn:le_a_a.

    (* le a a = true *)
    * destruct (le x a) eqn:le_x_a.
      + inversion H1.
        rewrite le_antisymm with (k:=a) (l:=x); try assumption.
        rewrite IHxs'; try assumption.
        rewrite merge_sorted_lists_body with (xs:=a::xs').
        inversion H2.
        destruct (Forall_forall (fun y : A => le a y = true) (y :: ys'))
          as (Hall & _).
        rewrite Hall with (x:=y); try (reflexivity || assumption).
        constructor; reflexivity.
        apply list_sorted_cons_cons_sorted with (b:=x); assumption.
        destruct (Forall_forall (fun y : A => le a y = true) (x :: xs'))
          as (Hall & _).
        rewrite Hall with (x0:=x); try assumption.
        rewrite le_x_a; reflexivity.
        constructor; reflexivity.
      + rewrite merge_sorted_lists_body. rewrite le_x_a. reflexivity.

    (* le a a = false *)
    * rewrite merge_sorted_lists_body.
      inversion H2.
      destruct (Forall_forall (fun y : A => le a y = true) (y :: ys'))
        as (Hall & _).
      rewrite Hall with (x:=y).
      reflexivity. assumption. constructor. reflexivity.
Qed.

Theorem merge_sorted_lists_cons_l :
  forall (A : Type) (le : A -> A -> bool) (x : A) (xs ys : list A),
  (forall k l : A, le k l = le l k -> l = k) ->
  list_sorted le (x :: xs) -> list_sorted le (x :: ys) ->
  merge_sorted_lists le (x :: xs) ys = x :: merge_sorted_lists le xs ys.
Proof.
  intros A le x xs ys le_antisymm Hxxs_sorted Hxys_sorted.
  rewrite merge_sorted_lists_body.
  induction ys as [|y ys'].
  - rewrite merge_sorted_lists_nil_r. reflexivity.
  - inversion Hxys_sorted.
    assert (le x y = true) as le_x_y.
    { inversion H1. assumption. }
    rewrite le_x_y.
    reflexivity.
Qed.

Theorem merge_sorted_lists_cons_r :
  forall (A : Type) (le : A -> A -> bool) (y : A) (xs ys : list A),
  (forall k l : A, le k l = le l k -> l = k) ->
  list_sorted le (y :: xs) -> list_sorted le (y :: ys) ->
  merge_sorted_lists le xs (y :: ys) = y :: merge_sorted_lists le xs ys.
Proof.
  intros A le y xs ys le_antisymm Hyxs_sorted Hyys_sorted.
  induction xs as [|x xs'].
  - rewrite merge_sorted_lists_body.
    rewrite merge_sorted_lists_nil_l. reflexivity.
  - inversion Hyxs_sorted.
    rewrite merge_sorted_lists_body.
    destruct (le x y) eqn:le_x_y; try reflexivity.
    assert (x = y) as eq_x_y.
    {
      inversion Hyxs_sorted.
      destruct (Forall_forall (fun y0 : A => le y y0 = true) (x :: xs'))
        as (Hall & _).
      apply le_antisymm with (k:=y) (l:=x).
      rewrite le_x_y. apply Hall.
      assumption. constructor; reflexivity.
    }
    rewrite merge_sorted_lists_cons_l; try (reflexivity || assumption).
    rewrite IHxs'.
    rewrite eq_x_y; reflexivity.
    apply list_sorted_cons_cons_sorted with (b:=x); assumption.
    rewrite eq_x_y; assumption.
Qed.

Theorem merge_sorted_lists_comm :
  forall (A : Type) (le : A -> A -> bool) (xs ys : list A),
  (forall k l : A, le k l = le l k -> l = k) ->
  list_sorted le xs -> list_sorted le ys ->
  merge_sorted_lists le xs ys = merge_sorted_lists le ys xs.
Proof.
  intros A le xs ys le_antisymm. revert ys.
  induction xs as [|x xs'];
    try (intro; rewrite merge_sorted_lists_nil_l;
          rewrite merge_sorted_lists_nil_r; reflexivity).
  induction ys as [|y ys'];
    try (rewrite merge_sorted_lists_nil_l; rewrite merge_sorted_lists_nil_r;
          reflexivity).
  intros Hxs_sorted Hys_sorted; inversion Hxs_sorted; inversion Hys_sorted.
  rewrite merge_sorted_lists_body;
    rewrite merge_sorted_lists_body with (xs:=y::ys') (ys:=x::xs').
  destruct (le x y) eqn:le_x_y; destruct (le y x) eqn:le_y_x.

  (* le x y = true and le y x = true *)
  - rewrite le_antisymm with (k:=x) (l:=y) at 2; try assumption.
    rewrite IHxs'; try assumption.
    rewrite le_antisymm with (k:=x) (l:=y); try assumption.
    assert (list_sorted le (x :: ys')) as Hxysp_sorted.
    {
      rewrite <- le_antisymm with (k:=x) (l:=y).
      assumption. rewrite le_y_x. assumption.
    }
    rewrite merge_sorted_lists_cons_l;
      try rewrite merge_sorted_lists_cons_r;
      try reflexivity; try assumption.
    rewrite le_y_x; rewrite le_x_y; reflexivity.
    rewrite le_y_x; rewrite le_x_y; reflexivity.

  (* le x y = true and le y x = false *)
  - rewrite IHxs' with (ys:=y::ys'); try (reflexivity || assumption).

  (* le x y = false and le y x = true *)
  - rewrite IHys'; try (reflexivity || assumption).

  (* le x y = false and le y x = false *)
  - rewrite le_antisymm with (k:=x) (l:=y); try assumption.
    rewrite IHys'; try assumption.
    assert (list_sorted le (x :: ys')).
    {
      rewrite <- le_antisymm with (k:=x) (l:=y).
      assumption. rewrite le_x_y. rewrite le_y_x. reflexivity.
    }
    rewrite merge_sorted_lists_cons_l;
      try rewrite merge_sorted_lists_cons_r;
      try reflexivity; try assumption.
    rewrite le_x_y. rewrite le_y_x. reflexivity.
Qed.

Theorem merge_sorted_lists_members :
  forall (A : Type) (le : A -> A -> bool) (a : A) (xs ys : list A),
  In a (merge_sorted_lists le xs ys) <-> In a xs \/ In a ys.
Proof.
  induction xs as [|x xs']; induction ys as [|y ys']; try simpl; try tauto.
  split; rewrite merge_sorted_lists_body; destruct (le x y) eqn:le_x_y; intro H.

  - inversion H.
    * auto.
    * destruct IHxs' with (ys:=y::ys') as (H1 & _).
      destruct (H1 H0); try auto.

  - inversion H; try auto.
    destruct IHys' as (H1 & _).
    destruct (H1 H0); auto.

  - destruct IHxs' with (ys:=y::ys') as (_ & H1).
    simpl. destruct H; destruct H; try auto.
    * right. apply H1. simpl. auto.
    * right. apply H1. simpl. auto.

  - destruct IHys' as (_ & H1).
    simpl. destruct H; destruct H; try auto.
    * right. apply H1. simpl. auto.
    * right. apply H1. simpl. auto.
Qed.

(* Lemma merge_sorted_lists_sorted_1 :
  forall (A : Type) (le : A -> A -> bool) (x y : A) (xs ys : list A),
  list_sorted le (x :: xs) -> list_sorted le (y ::ys) -> le x y = true ->
  list_sorted le (x :: merge_sorted_lists le xs (y :: ys)). *)

Lemma le_trans_contra :
  forall (A : Type) (le : A -> A -> bool) (h k l : A),
  (forall h k l : A, le h k = true -> le k l = true -> le h l = true) ->
  (forall k l : A, le k l = le l k -> l = k) ->
  le k l = true -> le k h = false -> le h l = true.
Proof.
  intros A le h k l le_trans le_antisymm H1 H2.
  destruct (le h k) eqn:le_h_k.
  - apply le_trans with (k:=k); assumption.
  - rewrite le_antisymm with (l:=h) (k:=k).
    assumption. rewrite H2. rewrite le_h_k. reflexivity.
Qed.

Theorem merge_sorted_lists_sorted :
  forall (A : Type) (le : A -> A -> bool) (xs ys : list A),
  (forall h k l : A, le h k = true -> le k l = true -> le h l = true) ->
  (forall k l : A, le k l = le l k -> l = k) ->
  (forall k : A, le k k = true) ->
  list_sorted le xs -> list_sorted le ys ->
  list_sorted le (merge_sorted_lists le xs ys).
Proof.
  intros A le xs ys le_trans le_antisymm  le_refl Hxs Hys.
  revert ys Hys. induction xs as [|x xs']; intros ys Hys; try apply Hys.
  induction ys as [|y ys']; try apply Hxs.
  rewrite merge_sorted_lists_body.
  destruct (le x y) eqn:le_x_y.

  (* le x y = true *)
  - inversion Hxs.
    constructor; try (apply IHxs' with (ys:=y::ys'); assumption).
    apply Forall_forall; intros a Ha.
    destruct merge_sorted_lists_members
      with (le:=le) (a:=a) (xs:=xs') (ys:=y::ys') as (Hin & _).
    destruct (Hin Ha).
    * destruct (Forall_forall (fun y : A => le x y = true) xs') as (Hall & _).
      apply Hall; try assumption.
    * inversion H3.
      + rewrite <- H4. assumption.
      + apply le_trans with (k:=y); try assumption.
        inversion Hys.
        destruct (Forall_forall (fun y0 : A => le y y0 = true) ys')
          as (Hall & _).
        apply Hall; try assumption.

  (* le x y = false *)
  - inversion Hys.
    constructor; try (apply IHys'; assumption).
    apply Forall_forall; intros a Ha.
    destruct merge_sorted_lists_members
      with (a:=a) (le:=le) (xs:=x::xs') (ys:=ys') as (Hin & _).
    destruct (Hin Ha).
    * apply le_trans_contra with (k:=x); try assumption.
      inversion H3.
      rewrite H4. apply le_refl.
      inversion Hxs.
      destruct (Forall_forall (fun y : A => le x y = true) xs') as (Hall & _).
      apply Hall; try assumption.
    * destruct (Forall_forall (fun y0 : A => le y y0 = true) ys') as (Hall & _).
      apply Hall; try assumption.
Qed.

Program Fixpoint merge_sort (A : Type) (le : A -> A -> bool)
    (xs : list A) { measure (length xs) } : list A :=
  match xs with
  | [] => []
  | [x] => [x]
  | _ :: _ :: _ =>
    match split xs with
    | (ys, zs) =>
      let sorted_ys := merge_sort A le ys in
      let sorted_zs := merge_sort A le zs in
      merge_sorted_lists le sorted_ys sorted_zs
    end
  end.

Next Obligation.
  apply split_smaller_l with (zs:=zs).
  assumption.
Qed.

Next Obligation.
  apply split_smaller_r with (ys:=ys).
  assumption.
Qed.

Theorem merge_sort_nil :
  forall (A : Type) (le : A -> A -> bool), merge_sort A le [] = [].
Proof. reflexivity. Qed.

Example merge_sort_list_nat :
  merge_sort nat leb [1;7;2;9;3;5;2] = [1;2;2;3;5;7;9].
Proof. reflexivity. Qed.

Lemma merge_sort_body :
  forall (A : Type) (le : A -> A -> bool) (xs : list A),
  merge_sort A le xs =
  match xs with
  | [] => []
  | [x] => [x]
  | _ :: _ :: _ =>
    match split xs with
    | (ys, zs) =>
      let sorted_ys := merge_sort A le ys in
      let sorted_zs := merge_sort A le zs in
      merge_sorted_lists le sorted_ys sorted_zs
    end
  end.
Proof.
  intros A le xs.
  unfold merge_sort.
  unfold merge_sort_func; rewrite WfExtensionality.fix_sub_eq_ext;
    fold merge_sort_func; simpl.
  induction xs; try reflexivity.
  induction xs; try reflexivity.
  destruct (split (a :: a0 :: xs)).
  reflexivity.
Qed.

Lemma merge_sort_length_le_n0 :
  forall (A : Type) (le : A -> A -> bool) (n0 : nat) (xs : list A),
  length xs <= n0 -> length (merge_sort A le xs) = length xs.
Proof.
  induction n0 as [|n0']; intros.
  - destruct xs. reflexivity. inversion H.
  - induction xs as [|a xs]; try reflexivity.
    induction xs as [|b xs]; try reflexivity.
    rewrite merge_sort_body.
    destruct (split (a :: b :: xs)) as (ys & zs) eqn:S; symmetry in S.
    simpl. rewrite merge_sorted_lists_length.
    repeat rewrite IHn0'.
    rewrite split_length with (xs:=a::b::xs); reflexivity || assumption.
    apply lt_n_Sm_le;
      apply lt_le_trans with (m:=length (a::b::xs)); try assumption.
    apply split_smaller_r with (ys:=ys). assumption.
    apply lt_n_Sm_le;
      apply lt_le_trans with (m:=length (a::b::xs)); try assumption.
    apply split_smaller_l with (zs:=zs). assumption.
Qed.

Theorem merge_sort_length : sort_length merge_sort.
Proof.
  intros A le xs.
  apply merge_sort_length_le_n0 with (n0:=length xs).
  apply Nat.le_refl.
Qed.

Lemma merge_sort_sorted_le_n0 :
  forall (A : Type) (le : A -> A -> bool) (n0 : nat) (xs : list A),
  (forall h k l : A, le h k = true -> le k l = true -> le h l = true) ->
  (forall k l : A, le k l = le l k -> l = k) ->
  (forall k : A, le k k = true) ->
  length xs <= n0 -> list_sorted le (merge_sort A le xs).
Proof.
  intros A le n0 xs le_trans le_antisymm le_refl.
  revert xs; induction n0 as [|n0']; intros xs H.
  - destruct xs. constructor. inversion H.
  - induction xs as [|a xs]; try constructor.
    induction xs as [|b xs].
    * constructor. apply Forall_nil. constructor.
    * rewrite merge_sort_body.
      destruct (split (a::b::xs)) eqn:Hsplit.
      simpl.
      apply merge_sorted_lists_sorted; try assumption; try apply IHn0'.
      + apply lt_n_Sm_le.
        apply Nat.lt_le_trans with (m:=length (a::b::xs)); try assumption.
        apply split_smaller_l with (a:=a) (b:=b) (xs:=xs) (ys:=l) (zs:=l0).
        symmetry; assumption.
      + apply lt_n_Sm_le.
        apply Nat.lt_le_trans with (m:=length (a::b::xs)); try assumption.
        apply split_smaller_r with (a:=a) (b:=b) (xs:=xs) (ys:=l) (zs:=l0).
        symmetry; assumption.
Qed.

Theorem merge_sort_sorted : sort_sorted merge_sort.
Proof.
  intros A le xs le_trans le_antisymm le_refl.
  apply merge_sort_sorted_le_n0 with (n0:=length xs); try assumption.
  apply Nat.le_refl.
Qed.

Lemma merge_sort_members_le_n0 :
  forall (A : Type) (le : A -> A -> bool) (n0 : nat) (x : A) (xs : list A),
  length xs <= n0 ->
  In x xs <-> In x (merge_sort A le xs).
Proof.
  intros A le n0 x.
  induction n0 as [|n0']; intros xs Hlen.
  - destruct xs. rewrite merge_sort_nil. tauto. inversion Hlen.
  - induction xs as [|a xs]; try (simpl; tauto).
    induction xs as [|b xs]; try (simpl; tauto).
    split; intro H.

    (* In x (a :: b :: xs) -> In x (merge_sort A le (a :: b :: xs)) *)
    * rewrite merge_sort_body.
      destruct (split (a::b::xs)) eqn:Hsplit.
      simpl.
      destruct merge_sorted_lists_members
        with (le:=le) (a:=x) (xs:=merge_sort A le l) (ys:=merge_sort A le l0)
        as (_ & Hin).
      apply Hin.
      destruct IHn0' with (xs:=l) as (Hl & _).
        apply lt_n_Sm_le. apply Nat.lt_le_trans with (m:=length (a::b::xs)).
        apply split_smaller_l with (zs:=l0). symmetry; assumption. assumption.
      destruct IHn0' with (xs:=l0) as (Hl0 & _).
        apply lt_n_Sm_le. apply Nat.lt_le_trans with (m:=length (a::b::xs)).
        apply split_smaller_r with (ys:=l). symmetry; assumption. assumption.
      apply imply_and_or2 with (P:=In x l); try assumption.
      apply or_comm.
      apply imply_and_or2 with (P:=In x l0); try assumption.
      apply or_comm.
      apply in_app_or with (a:=x) (l:=l) (m:=l0).
      rewrite split_concat with (xs:=a::b::xs); try symmetry; try assumption.

    (* In x (merge_sort A le (a :: b :: xs)) -> In x (a :: b :: xs) *)
    * rewrite merge_sort_body in H.
      destruct (split (a::b::xs)) eqn:Hsplit.
      simpl in H.
      destruct merge_sorted_lists_members
        with (le:=le) (a:=x) (xs:=merge_sort A le l) (ys:=merge_sort A le l0)
        as (Hin & _).
      destruct (split_members A x (a::b::xs) l l0) as (Hin' & _);
        try (symmetry; assumption).
      apply Hin'.
      destruct (Hin H).
      + left.
        destruct IHn0' with (xs:=l) as (_ & Hinl).
          apply lt_n_Sm_le. apply Nat.lt_le_trans with (m:=length (a::b::xs)).
          apply split_smaller_l with (zs:=l0). symmetry; assumption. assumption.
        apply Hinl. assumption.
      + right.
        destruct IHn0' with (xs:=l0) as (_ & Hinl0).
          apply lt_n_Sm_le. apply Nat.lt_le_trans with (m:=length (a::b::xs)).
          apply split_smaller_r with (ys:=l). symmetry; assumption. assumption.
        apply Hinl0. assumption.
Qed.

Theorem merge_sort_members : sort_members merge_sort.
Proof.
  intros A le xs x.
  apply merge_sort_members_le_n0 with (n0:=length xs).
  auto.
Qed.

Theorem merge_sort_valid : valid_sort merge_sort.
Proof.
  split.
  apply merge_sort_length.
  split.
  apply merge_sort_sorted.
  apply merge_sort_members.
Qed.

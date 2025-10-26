Require Import List.
Open Scope list_scope.
Import ListNotations.
Require Import PeanoNat.

(* Inductive option (A : Type) := *)
(* | Just : A -> option A *)
(* | Nothing : option A. *)

(* Arguments Just [A] _. *)
(* Arguments Nothing [A]. *)

Inductive queue {X:Type} : Type :=
| fun_queue (F : list X) (R : list X).

Definition queue_empty {X: Type} (q: @queue X) :=
  match q with
  | fun_queue nil nil => true
  | fun_queue _ _ => false
  end.

(* Inductive list_reversed : forall X , list X -> list X -> Prop := *)
(*   | reversed X (a b : list X): (a = List.rev b) -> list_reversed X a b. *)

Inductive eq_queue : forall X : Type , @queue X -> @queue X -> Prop :=
| eq_q X (F1 R1 F2 R2 : @list X) (e: F1 ++ (rev R1) = F2 ++ (rev R2)): eq_queue X (fun_queue F1 R1) (fun_queue F2 R2).

Check pair.
Print option.
Locate pair.
Locate "[ ]".
Print list.
Check nil.
Check [1;2].
Check @fun_queue nat.
Definition myqueue := @fun_queue nat [1;2] [4;3].

Definition dequeue {X : Type} (q : @queue X) : option (X * (@queue X)) :=
  match q with
  | fun_queue F R =>
    match F with
    | nil => match R with
             | nil => None
             | cons h t => Some (let reverse := (rev R) in (pair
                                      (hd h reverse)
                                      (fun_queue (tl reverse) nil)))
             end
    | cons h t => Some (pair h (fun_queue t R))
    end
  end.

Definition enqueue {X : Type} (a : X) (q : queue) : queue :=
  match q with
  | fun_queue F R =>
    fun_queue F (cons a R)
  end.

Theorem queue_empty_reflection (X : Type): forall q:@queue X,
    queue_empty q = true <-> q = fun_queue nil nil.
Proof.
  intros. split.
  - intros H. destruct q eqn:E. destruct F eqn:EF, R eqn:ER;try (simpl in H; discriminate).
    + reflexivity.
  - intros H. rewrite -> H. simpl. reflexivity.
Qed.

Theorem dequeue_for_empty_q_gives_none (X : Type): forall q:@queue X,
    dequeue q = None <-> q = fun_queue nil nil.
Proof.
  intros. split.
  - intros H. destruct q eqn:E. destruct F eqn:EF, R eqn:ER.
    + reflexivity.
    + simpl in H. discriminate H.
    + simpl in H. discriminate H.
    + simpl in H. discriminate H.
  - intros H. rewrite H. simpl. reflexivity.
Qed.

(* Fixpoint dequeue {X : Type} (q : queue X) : option (X * (queue X)) *)
(* Fixpoint enqueue {X : Type} (a : X) (q : queue X) : queue X *)
Theorem dequeue_enqueue (X : Type): forall x:X, forall q:@queue X,
      queue_empty q = true -> dequeue (enqueue x q) = Some (x, fun_queue nil nil).
Proof.
  intros. apply queue_empty_reflection in H. rewrite -> H. simpl. reflexivity.
Qed.

Inductive eq_dequeue: forall (X: Type)
                      (r1: option (X * (@queue X)))
                      (r2: option (X * (@queue X))),
            Prop :=
  | queues_empty (X: Type) : eq_dequeue X None None
  | queues_nonempty (X: Type)
                    (h: X)
                    (q1 : @queue X)
                    (q2 : @queue X)
                    (e: eq_queue X q1 q2) : eq_dequeue X (Some (h, q1)) (Some (h, q2)).

Notation "X '||' x '~==~' y" := (eq_dequeue X x y)
                                  (at level 50, left associativity).
Check nat || None ~==~ None.
Lemma eq_correct {X: Type} (q1 : @queue X) (q2: @queue X) :
      eq_queue X q1 q2 -> eq_dequeue X (dequeue q1) (dequeue q2).
Proof.
   destruct q1, q2.
   destruct F, F0 ; simpl.
   - destruct R, R0 ; simpl.
     + intro.
       apply (queues_empty X).
     + intro.
       remember (fun_queue [] []) as EQ.
       remember (fun_queue [] (x :: R0)) as NQ.
       destruct H.
       inversion HeqEQ ; subst.
       inversion HeqNQ ; subst.
       simpl in e.
       destruct (rev R0) ; simpl in e ; inversion e.
     + intro.
       remember (fun_queue [] []) as EQ.
       remember (fun_queue [] (x :: R)) as NQ.
       destruct H.
       inversion HeqEQ ; subst.
       inversion HeqNQ ; subst.
       simpl in e.
       destruct (rev R) ; simpl in e ; inversion e.
     + intro.
       remember (fun_queue [] (x :: R)) as Q1.
       remember (fun_queue [] (x0 :: R0)) as Q2.
       destruct H.
       inversion HeqQ1 ; subst.
       inversion HeqQ2 ; subst.
       Search "app_nil".
       rewrite app_nil_l in e.
       rewrite app_nil_l in e.
       Search "rev_".
       Search "f_equal".
       apply (f_equal (@rev X)) in e.
       rewrite rev_involutive in e.
       rewrite rev_involutive in e.
       inversion e ; subst.
       apply queues_nonempty.
       apply eq_q.
       reflexivity.
   - destruct R, R0 ; simpl.
     + intro.
       remember (fun_queue [] []) as EQ.
       remember (fun_queue (x :: F0) []) as NQ.
       destruct H.
       inversion HeqEQ ; subst.
       inversion HeqNQ ; subst.
       simpl in e. discriminate e.
     + intro.
       remember (fun_queue [] []) as EQ.
       remember (fun_queue (x :: F0) (x0 :: R0)) as NQ.
       destruct H.
       inversion HeqEQ ; subst.
       inversion HeqNQ ; subst.
       simpl in e. discriminate e.
     + intro.
       remember (fun_queue [] (x0 :: R)) as EQ.
       remember (fun_queue (x :: F0) []) as NQ.
       destruct H.
       inversion HeqEQ ; subst.
       inversion HeqNQ ; subst.
       simpl in e.
       rewrite app_nil_r in e.
       rewrite -> e.
       simpl.
       apply queues_nonempty.
       apply eq_q.
       reflexivity.
     + intro.
       remember (fun_queue [] (x0 :: R)) as EQ.
       remember (fun_queue (x :: F0) (x1 :: R0)) as NQ.
       destruct H.
       inversion HeqEQ ; subst.
       inversion HeqNQ ; subst.
       simpl in e.
       rewrite -> e.
       simpl.
       apply queues_nonempty.
       apply eq_q.
       simpl.
       rewrite app_nil_r.
       reflexivity.
   - destruct R, R0 ; simpl.
     + intro.
       remember (fun_queue [] []) as EQ.
       remember (fun_queue (x :: F) []) as NQ.
       destruct H.
       inversion HeqEQ ; subst.
       inversion HeqNQ ; subst.
       simpl in e. discriminate e.
     + intro.
       remember (fun_queue (x :: F) []) as EQ.
       remember (fun_queue [] (x0 :: R0)) as NQ.
       destruct H.
       inversion HeqEQ ; subst.
       inversion HeqNQ ; subst.
       simpl in e.
       rewrite <- e.
       simpl.
       apply queues_nonempty.
       rewrite app_nil_r.
       apply eq_q.
       reflexivity.
     + intro.
       remember (fun_queue (x :: F) (x0 :: R)) as EQ.
       remember (fun_queue [] []) as NQ.
       destruct H.
       inversion HeqEQ ; subst.
       inversion HeqNQ ; subst.
       simpl in e.
       discriminate e.
     + intro.
       remember (fun_queue (x :: F) (x0 :: R)) as EQ.
       remember (fun_queue [] (x1 :: R0)) as NQ.
       destruct H.
       inversion HeqEQ ; subst.
       inversion HeqNQ ; subst.
       simpl in e.
       rewrite <- e.
       simpl.
       apply queues_nonempty.
       apply eq_q.
       simpl.
       rewrite app_nil_r.
       reflexivity.
   - destruct R, R0 ; simpl.
     + intro.
       remember (fun_queue (x :: F) []) as EQ.
       remember (fun_queue (x0 :: F0) []) as NQ.
       destruct H.
       inversion HeqEQ ; subst.
       inversion HeqNQ ; subst.
       simpl in e.
       rewrite app_nil_r in e.
       rewrite app_nil_r in e.
       inversion e ; subst.
       apply queues_nonempty.
       apply eq_q.
       reflexivity.
     + intro.
       remember (fun_queue (x :: F) []) as EQ.
       remember (fun_queue (x0 :: F0) (x1 :: R0)) as NQ.
       destruct H.
       inversion HeqEQ ; subst.
       inversion HeqNQ ; subst.
       simpl in e.
       rewrite app_nil_r in e.
       inversion e ; subst.
       apply queues_nonempty.
       apply eq_q.
       simpl.
       rewrite app_nil_r.
       reflexivity.
     + intro.
       remember (fun_queue (x :: F) (x1 :: R)) as EQ.
       remember (fun_queue (x0 :: F0) []) as NQ.
       destruct H.
       inversion HeqEQ ; subst.
       inversion HeqNQ ; subst.
       simpl in e.
       inversion e ; subst.
       rewrite app_nil_r in e.
       rewrite app_nil_r in H1.
       apply queues_nonempty.
       apply eq_q.
       simpl.
       rewrite app_nil_r.
       rewrite <- H1.
       reflexivity.
     + intro.
       remember (fun_queue (x :: F) (x1 :: R)) as EQ.
       remember (fun_queue (x0 :: F0) (x2 :: R0)) as NQ.
       destruct H.
       inversion HeqEQ ; subst.
       inversion HeqNQ ; subst.
       simpl in e.
       inversion e ; subst.
       apply queues_nonempty.
       apply eq_q.
       simpl.
       rewrite <- H1.
       reflexivity.
Qed.

Lemma eq_correct_enqueue {X: Type} (q1 : @queue X) (q2: @queue X) :
      forall (x : X), eq_queue X q1 q2 -> eq_queue X (enqueue x q1) (enqueue x q2).
Proof.
  intros.
  destruct q1, q2.
  destruct F, F0 ; simpl.
  - destruct R, R0 ; simpl.
    + apply eq_q. reflexivity.
    + remember (fun_queue [] []) as EQ.
      remember (fun_queue [] (x0 :: R0)) as NQ.
      destruct H.
      inversion HeqEQ ; subst.
      inversion HeqNQ ; subst.
      simpl in e.
      destruct (rev R0).
      ++ rewrite app_nil_l in e.
         discriminate e.
      ++ simpl in e. discriminate e.
    + remember (fun_queue [] (x0 :: R)) as EQ.
      remember (fun_queue [] []) as NQ.
      destruct H.
      inversion HeqEQ ; subst.
      inversion HeqNQ ; subst.
      simpl in e.
      destruct (rev R).
      ++ rewrite app_nil_l in e.
         discriminate e.
      ++ simpl in e. discriminate e.
    + remember (fun_queue [] (x0 :: R)) as EQ.
      remember (fun_queue [] (x1 :: R0)) as NQ.
      destruct H.
      inversion HeqEQ ; subst.
      inversion HeqNQ ; subst.
      rewrite app_nil_l in e.
      rewrite app_nil_l in e.
      apply (f_equal (@rev X)) in e.
      rewrite rev_involutive in e.
      rewrite rev_involutive in e.
      inversion e ; subst.
      apply eq_q.
      reflexivity.
  - destruct R, R0 ; simpl.
    + remember (fun_queue [] []) as EQ.
      remember (fun_queue (x0 :: F0) []) as NQ.
      destruct H.
      inversion HeqEQ ; subst.
      inversion HeqNQ ; subst.
      simpl in e.
      rewrite app_nil_r in e.
      discriminate e.
    + remember (fun_queue [] []) as EQ.
      remember (fun_queue (x0 :: F0) (x1 :: R0)) as NQ.
      destruct H.
      inversion HeqEQ ; subst.
      inversion HeqNQ ; subst.
      simpl in e.
      discriminate e.
    + remember (fun_queue [] (x1 :: R)) as EQ.
      remember (fun_queue (x0 :: F0) []) as NQ.
      destruct H.
      inversion HeqEQ ; subst.
      inversion HeqNQ ; subst.
      simpl in e.
      rewrite app_nil_r in e.
      destruct (rev R) eqn:ER.
      ++ rewrite app_nil_l in e.
         intros.
         apply eq_q.
         rewrite app_nil_l.
         simpl.
         rewrite ER.
         rewrite app_nil_l.
         rewrite e.
         reflexivity.
      ++ injection e.
         intros.
         apply eq_q.
         rewrite app_nil_l.
         simpl.
         rewrite ER.
         rewrite -> e.
         reflexivity.
    + remember (fun_queue [] (x1 :: R)) as EQ.
      remember (fun_queue (x0 :: F0) (x2 :: R0)) as NQ.
      destruct H.
      inversion HeqEQ ; subst.
      inversion HeqNQ ; subst.
      simpl in e.
      apply eq_q.
      simpl.
      rewrite -> e.
      simpl.
      rewrite <- app_assoc.
      reflexivity.
  - destruct R, R0 ; simpl.
    + remember (fun_queue (x0 :: F) []) as EQ.
      remember (fun_queue [] []) as NQ.
      destruct H.
      inversion HeqEQ ; subst.
      inversion HeqNQ ; subst.
      simpl in e.
      rewrite app_nil_r in e.
      discriminate e.
    + remember (fun_queue (x0 :: F) []) as EQ.
      remember (fun_queue [] (x1 :: R0)) as NQ.
      destruct H.
      inversion HeqEQ ; subst.
      inversion HeqNQ ; subst.
      simpl in e.
      rewrite app_nil_r in e.
      apply eq_q.
      rewrite app_nil_l.
      rewrite e.
      simpl.
      reflexivity.
    + remember (fun_queue (x0 :: F) (x1 :: R)) as EQ.
      remember (fun_queue [] []) as NQ.
      destruct H.
      inversion HeqEQ ; subst.
      inversion HeqNQ ; subst.
      simpl in e.
      discriminate e.
    + remember (fun_queue (x0 :: F) (x1 :: R)) as EQ.
      remember (fun_queue [] (x2 :: R0)) as NQ.
      destruct H.
      inversion HeqEQ ; subst.
      inversion HeqNQ ; subst.
      rewrite app_nil_l in e.
      simpl in e.
      apply eq_q.
      simpl.
      rewrite <- e.
      (* rewrite <- app_assoc. *)
      rewrite app_assoc.
      simpl.
      reflexivity.
  - destruct R, R0 ; simpl.
    + remember (fun_queue (x0 :: F) []) as EQ.
      remember (fun_queue (x1 :: F0) []) as NQ.
      destruct H.
      inversion HeqEQ ; subst.
      inversion HeqNQ ; subst.
      simpl in e.
      rewrite app_nil_r in e.
      rewrite app_nil_r in e.
      rewrite e.
      apply eq_q.
       reflexivity.
    + remember (fun_queue (x0 :: F) []) as EQ.
      remember (fun_queue (x1 :: F0) (x2 :: R0)) as NQ.
      destruct H.
      inversion HeqEQ ; subst.
      inversion HeqNQ ; subst.
      simpl in e.
      rewrite app_nil_r in e.
      rewrite e.
      apply eq_q.
      simpl.
      rewrite <- app_assoc.
      reflexivity.
    + remember (fun_queue (x0 :: F) (x2 :: R)) as EQ.
      remember (fun_queue (x1 :: F0) []) as NQ.
      destruct H.
      inversion HeqEQ ; subst.
      inversion HeqNQ ; subst.
      simpl in e.
      rewrite app_nil_r in e.
      apply eq_q.
      rewrite <- e.
      simpl.
      rewrite app_assoc.
      reflexivity.
    + remember (fun_queue (x0 :: F) (x2 :: R)) as EQ.
      remember (fun_queue (x1 :: F0) (x3 :: R0)) as NQ.
      destruct H.
      inversion HeqEQ ; subst.
      inversion HeqNQ ; subst.
      simpl in e.
      inversion e ; subst.
      apply eq_q.
      simpl.
      rewrite <- app_assoc.
      assert (myH: x1 :: F ++ rev R ++ [x2] ++ [x] = (x1 :: F ++ rev R ++ [x2]) ++ [x]).
      ++ simpl. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
      ++ rewrite -> myH. rewrite -> e.

      (* autorewrite *)
      repeat ( rewrite app_assoc ; simpl).
      repeat ( rewrite app_assoc in e ; simpl in e).
      reflexivity.


      (* Our attempts *)
      (* Check app_inv_tail [x] (x0 :: F ++ rev R ++ [x2]) (x1 :: F0 ++ (rev R0 ++ [x3])). *)
     (*  rewrite <- app_assoc. *)
     (*  Check (app_assoc (x0 :: F ++ rev R) [x2]). *)
     (*  rewrite -> (app_inv_tail [x] (x0 :: F ++ rev R ++ [x2]) (x1 :: F0 ++ (rev R0 ++ [x3]))). *)
     (*  apply Ha. *)
     (*  rewrite -> (app_inv_tail [x] _ (x1 :: F0 ++ (rev R0 ++ [x3]))). *)
     (*  rewrite -> (app_inv_tail [x] (x0 :: F ++ (rev R ++ [x2])) (F0 ++ (rev R0 ++ [x3]))). *)


     (*  rewrite e. *)
     (*  (* rewrite -> 2? app_assoc. *) *)
     (*  rewrite -> app_assoc with _ (x0 :: F ++ rev R) _ _. *)
     (*  remember (x0 :: F ++ rev R ++ [x2]) as A. *)
     (*  rewrite <- HeqA. *)
     (* (*  app_assoc *) *)
     (* (* : forall (A : Type) (l m n : list A), l ++ m ++ n = (l ++ m) ++ n *) *)

     (*  rewrite -> (app_assoc ) *)
      (*  rewrite -> e. *)
Qed.
(* Inductive eq_queue *)
(* Inductive eq_dequeue *)
(*
Inductive eq_dequeue: forall (X: Type)
                      (r1: option (X * (@queue X)))
                      (r2: option (X * (@queue X))),
            Prop :=
  | queues_empty (X: Type) : eq_dequeue X None None
  | queues_nonempty (X: Type)
                    (h: X)
                    (q1 : @queue X)
                    (q2 : @queue X)
                    (e: eq_queue X q1 q2) : eq_dequeue X (Some (h, q1)) (Some (h, q2)).
 *)
Lemma head_equal: forall (X : Type), forall (l: list X) (x:X) (x0:X),
      hd x ((rev l) ++ [x0]) = hd x (((rev l) ++ [x0]) ++ [x]).
Proof.
  intros. destruct ((rev l) ++ [x0]).
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma tail_equal: forall (X : Type), forall (l: list X) (x:X),
      l <> [] -> tl (l ++ [x]) = tl (l) ++ [x].
Proof.
  destruct l as [|h t] eqn:E.
  - unfold not. simpl. intros. exfalso. apply H. reflexivity.
  - intros. simpl. reflexivity.
Qed.

Theorem dequeue_enqueue2 : forall (X : Type) (x:X), forall q:(@queue X),
      queue_empty q = false ->
      exists y:X, exists (q':@queue X), dequeue q = Some (y, q')
      -> X || (dequeue (enqueue x q)) ~==~ (Some (y, enqueue x q')).
Proof.
  intros X x q H. destruct q eqn:E. destruct F eqn:EF, R eqn:ER.
  - simpl in H. discriminate H.
  - clear H. exists (hd x (rev R)). exists (fun_queue (tl (rev R)) nil).
    intros H.
    rewrite -> ER.
    simpl. rewrite <- head_equal.
    (* hd x ((rev l ++ [x0]) ++ [x]) *)
    (* hd x (rev R) *)
    apply (queues_nonempty X). apply eq_q. simpl. rewrite app_nil_r. apply tail_equal.
    destruct l as [|h t].
    + simpl. unfold not. intros H1. discriminate H1.
    + simpl. unfold not. intros H1. destruct (rev t ++ [h]) as [|h1 t1].
      ++ simpl in H1. discriminate H1.
      ++ simpl in H1. discriminate H1.
  - clear H. exists (hd x F). exists (fun_queue (tl F) nil).
    intros H. rewrite -> EF.
    simpl. apply (queues_nonempty X). apply eq_q. reflexivity.
  - clear H. exists (hd x F). exists (fun_queue (tl F) R). intros H.
    rewrite -> EF. rewrite -> ER. simpl.
    apply (queues_nonempty X). apply eq_q. reflexivity.
Qed.

(* Unit tests *)

Example test_dequeue1 :
  dequeue (@fun_queue nat nil nil) = None.
Proof. reflexivity. Qed.

Example test_dequeue2 :
  dequeue (fun_queue [1] nil) = Some (1, (fun_queue [] nil)).
Proof. reflexivity. Qed.

Example test_dequeue3 :
  dequeue (fun_queue [1;2;3] [5;4]) = Some (1, (fun_queue [2;3] [5;4])).
Proof. reflexivity. Qed.

Compute dequeue (fun_queue nil [2;1]).

Example test_dequeue4 :
  dequeue (fun_queue nil [3;2;1]) = Some (1, (fun_queue [2;3] nil)).
Proof. reflexivity. Qed.

Example test_dequeue5 :
  dequeue (fun_queue nil [1]) = Some (1, (fun_queue nil nil)).
Proof. reflexivity. Qed.

Compute dequeue myqueue.
Compute enqueue 1 (fun_queue nil nil).

Example test_enque1 :
  enqueue 1 (fun_queue nil nil) = fun_queue nil [1].
Proof. reflexivity. Qed.

Example test_enque2 :
  enqueue 5 (fun_queue [1;2] [4;3]) = fun_queue [1;2] [5;4;3].
Proof. reflexivity. Qed.

Require Import List.
Open Scope list_scope.
Import ListNotations.

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

Check pair.
Print option.
Locate pair.
Locate "[ ]".
Print list.
Check nil.
Check [1;2].
Check @fun_queue nat.
Definition myqueue := @fun_queue nat [1;2] [4;3].

Fixpoint dequeue {X : Type} (q : @queue X) : option (X * (@queue X)) :=
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

Fixpoint enqueue {X : Type} (a : X) (q : queue) : queue :=
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

Theorem dequeue_enqueue2 : forall (X : Type) (x:X), forall q:(@queue X),
      queue_empty q = false ->
      exists y:X, exists (q':@queue X), dequeue q = Some (y, q')
      -> dequeue (enqueue x q) = Some (y, enqueue x q').
Proof.
  intros X x q H. destruct q eqn:E. destruct F eqn:EF, R eqn:ER.
  - simpl in H. discriminate H.
  - clear H. exists (hd x (rev R)). exists (fun_queue (tl (rev R)) nil).
    simpl. intros H.

Example test_dequeue1 :
  dequeue (fun_queue nat nil nil) = None.
Proof. reflexivity. Qed.

Example test_dequeue2 :
  dequeue (fun_queue nat [1] nil) = Some (1, (fun_queue nat [] nil)).
Proof. reflexivity. Qed.

Example test_dequeue3 :
  dequeue (fun_queue nat [1;2;3] [5;4]) = Some (1, (fun_queue nat [2;3] [5;4])).
Proof. reflexivity. Qed.

Compute dequeue (fun_queue nat nil [2;1]).

Example test_dequeue4 :
  dequeue (fun_queue nat nil [3;2;1]) = Some (1, (fun_queue nat [2;3] nil)).
Proof. reflexivity. Qed.

Example test_dequeue5 :
  dequeue (fun_queue nat nil [1]) = Some (1, (fun_queue nat nil nil)).
Proof. reflexivity. Qed.

Compute dequeue myqueue.
Compute enqueue 1 (fun_queue nat nil nil).

Example test_enque1 :
  enqueue 1 (fun_queue nat nil nil) = fun_queue nat nil [1].
Proof. reflexivity. Qed.

Example test_enque2 :
  enqueue 5 (fun_queue nat [1;2] [4;3]) = fun_queue nat [1;2] [5;4;3].
Proof. reflexivity. Qed.
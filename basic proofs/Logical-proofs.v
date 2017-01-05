Inductive bool : Type :=
| false : bool  
| true : bool.

Definition neg_b (b:bool) : bool :=
match b with
| false => true
| true => false
end.

Definition and_b (b1:bool) (b2:bool) : bool :=
match b1 with
| false => false
| true => b2
end. 

Definition or_b (b1:bool) (b2:bool) : bool :=
match b1 with
| true => true
| false => b2
end.

Notation "a || b" := (or_b a b).
Notation "a && b" := (and_b a b).
Notation "- a" := (neg_b a).


Check (false && true).

    (* Equivalent à : - simpl. reflexivity. tapé 4 fois (pour chaque pair (a, b))*)
Theorem deMorgan : forall a b, (-a || -b) = -(a && b).
Proof. 
    intros a b.
    destruct a; destruct b; (simpl; reflexivity).
Qed.


Theorem doubleNeg : forall n, --n = n.
Proof.
    intro n.
    destruct n.
    - (*cas n = false*) trivial. (*équivalent à simpl. reflexivity. (+ d'autre trucs)*)
    - (* cas n = true*) trivial.
Qed.

Theorem existBool : exists p, p && true = true.
Proof.
   exists true.
   simpl. reflexivity.
Qed.
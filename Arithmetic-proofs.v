Inductive expr : Type :=
 | Int : nat -> expr
 | Add : expr -> expr -> expr
 | Mul : expr -> expr -> expr.

(* Fixpoint = let rec *)
Fixpoint eval (e:expr) : nat := 
match e with
| Int x => x
| Add e1 e2 => (eval e1) + (eval e2)
| Mul e1 e2 => (eval e1) * (eval e2)
end.

(* Calcul 3+4 *)
Compute (eval (Add (Int 3) (Int 4))).

(* 1 + 1 = 2 *)
Lemma onePlusone : (eval (Add (Int 1) (Int 1))) = 2.
Proof.
    simpl.
    reflexivity. 
Qed.

(* x + 0 = x*)
(* Preuve sur les entiers naturel (type de Coq) *)
Lemma nPlusZero : forall n, n = n+0.
Proof.
    intro n.
    induction n.
    - simpl. reflexivity.
    - simpl. rewrite <- IHn. reflexivity. Qed.

(* Preuve sur notre système d'expression *)
Lemma xPlusZero : forall n, (eval (Add (Int n) (Int 0))) = n.
Proof.
    intro n.
    induction n.
    - simpl. reflexivity.
    - rewrite <- IHn. simpl. rewrite <- nPlusZero. reflexivity. Qed.


Lemma xPlusB : forall a b, a+b = b+a.
Proof.
    intros a b.
    induction a.
    - simpl. rewrite <- nPlusZero. reflexivity.
    - simpl. 
(* Assert = preuve auxiliaire *)
assert (forall x y, S (x+y) = x + S y) as H_assert.
{ intros x y.
  induction x.
  - simpl. reflexivity.
  - simpl. rewrite IHx. reflexivity. }
  rewrite IHa. rewrite H_assert. reflexivity. 
Qed.
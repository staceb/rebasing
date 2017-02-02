Require Import Coq.Bool.Bool.
Require Import Coq.Arith.EqNat.
Require Import List.
Require Import Coq.Arith.Plus.
Open Scope list_scope.
Import ListNotations.


(** Approfondissements des tactiques **)

Definition admit {T: Type} : T.  Admitted.

(** UNFOLD **)
(* Remarque : on peut aussi unfold dans les hypothèses en faisant 'unfold in H'.
   Mais cela ne servira pas ici. *)

Definition square n := n*n.

Theorem th0 : square 6 = 36.
Proof.
  unfold square. simpl. reflexivity.
Qed.

(** SYMMETRY **)
(* S'applique soit sur le goal en faisant 'symmetry' soit sur une hypothèse H en faisant
   'symmetry H' *)
(* Permet d'inverser le côté gauche et droit d'une égalité *)
(* Pas d'exercice car c'est trop nul mais tu peux tester quand tu veux lol *)

(** DESTRUCT **)
(* 1. Il est possible de faire la destruction sur une expression *)
(* 2. Il est possible de conserver la valeur de destruction avec destruct (expr) eqn:H
      où H est le nom de l'égalité associée à la destruction 
   3. La tactique 'unfold' permet de révéler les définitions opaques
      Remarques : l'utilisation de pattern matching match..with rend les définitions 
      transparentes mais les conditions if..then else conserve l'opacité des définitions. *)

Definition s (n : nat) : nat :=
  if (beq_nat n 0) then 1
  else n+1.

Theorem th1 : forall n, s n = n + 1.
Proof.
Admitted.

Definition f (n : nat) : nat :=
  if (beq_nat n 0) then 1
  else if (beq_nat n 5) then 1
  else if (beq_nat n 10) then 1
  else 1.

Theorem th2 : forall n, f n = 1.
Proof.
Admitted.

(** APPLY **)

(* RESTRICTION : Utiliser seulement 'apply' et 'intros' *)
Theorem impl_transitivity : forall (P Q R : Prop),
  (P -> Q) -> (Q-> R) -> (P -> R).
Proof.
  intros P Q R.
  intros H1 H2 H3.
  apply H2. apply H1. apply H3.
Qed.

(* RESTRICTION : Utiliser seulement 'apply in et 'intros' *)
Theorem impl_transitivity' : forall (P Q R : Prop),
  (P -> Q) -> (Q-> R) -> (P -> R).
Proof.
  intros P Q R.
  intros H1 H2 H3.
  apply H1 in H3.
  apply H2 in H3.
  apply H3.
Qed.

(* Montrer une équivalence <-> on doit montrer -> et <-.
   - Si l'équivalence est dans le goal : on utilise 'split'
   - Si l'équivalence H est dans le contexte : on utilise 'destruct H' *)
(*
Split permet d'obtenir les deux implications d'une équivalence
*)
Theorem equiv_comm : forall (P Q : Prop),
  (P <-> Q) <-> (Q <-> P).
Proof.
  split.
  - intro H. destruct H. split.
    * intro Q'. apply H0. apply Q'.
    * intro P'. apply H in P'. apply P'.
  - intro H. destruct H. split.
    * intro P'. apply H0 in P'. apply P'.
    * intro Q'. apply H. apply Q'.
Qed.
 
(* S'il y a une contradiction dans le contexte, utiliser la tactique 'contradiction'
   pour résoudre le goal. *)
Theorem pair_eq : forall (n:nat), Nat.even n = true <-> Nat.odd n = false.
Proof.
  intro n.
  split. 
  - intro nT. unfold Nat.odd. rewrite -> nT. simpl. reflexivity.
  - intro nF. unfold Nat.odd in nF. destruct (Nat.even n).
    * trivial.
    * simpl in nF. rewrite nF. reflexivity.
(*Regarde les constructeur sur une hypothèse du contexte, si c'est impossible
il va résoudre lui-même le goal à la place du rewrite + reflexivity*)
(*inversion nF.*)
Qed.

Axiom ex : forall P, P \/ not P.

Theorem tiersexclu : (1 = 1).
Proof.
  pose (ex (1 =1)) as ex.
  destruct ex.
  - apply H.
  - unfold not in H. assert (1 = 1). reflexivity.
    apply H in H0. contradiction.
Qed.

(*Quand on a une hypothèse = False c'est une contradiction.*)
Theorem contra1 : False -> 1 = 0.
Proof.
  intro F. contradiction.
Qed.

(*On a 1 = 0, inversion va voir si ils ont un constructeur commun
si ce n'est pas le cas c'est une contradiction*)
Theorem contra2 : 1 = 0 -> 3 = 6.
Proof.
  intro UnZ. inversion UnZ.
Qed.

(** Inversion **)
(* La tactique 'inversion' s'applique sur une hypothèse par ex : 'inversion H' et 
   permet de faire un raisonnement inverse sur la structure d'un hypothèse.
   Disons que H énonce l'égalité de deux entiers.
   - Soit on a H : S m = S n. La tactique 'inversion' va déduire qu'on a forcément m = n
     et va changer automatiquement le goal s'il peut
   - Soit on a H : 0 = S n ou S n = 0. La tactique 'inversion' va voir que c'est impossible
     d'après la définition des constructeurs donc contradiction : le goal est résolu 
     automatiquement. *)

Example S_injective : forall (n m : nat), S n = S m -> n = m.
Proof.
  intros n m H.
  inversion H. (* Remarque : inversion met automatiquement le goal à jour *)
  reflexivity.
Qed.

Theorem inversion_listes : forall (n m : nat), [n] = [m] -> n = m.
Proof.
  intros n m H.
  inversion H.
  reflexivity.
Qed.

Theorem inversion_trivial1 : forall {X:Type} (h:X) (t:list X),
  [] = h::t -> 1 + 1 = 11.
Proof.
  intros X h t H.
  inversion H.
Qed.

Theorem inversion_trivial2 : false = true -> 1 + 1 = 11.
Proof.
  intro H.
  inversion H.
Qed.

Inductive t :=
  | a
  | z
  | b : t -> t -> t
  | c : t -> t -> t -> t
  | d : t -> t.

Theorem inversion_general : forall (c1 c2 c3 c1' c2' c3' : t),
  c c1 c2 c3 = c c1' c2' c3' -> c2 = c2'.
Proof.
  intros. (*Vide toute la pile*)
  inversion H. reflexivity. 
Qed.

(** Puissance de l'hypothèse d'induction **)
(* Parfois il est nécessaire de laisser général les autres termes en dehors du sujet
   d'induction pour donner plus de puissance à l'hypothèse d'induction *)
(* - Soit on introduit tout et on fait 'generalize dependent' sur un terme autre que le
     sujet d'induction
   - Soit on introduit juste le sujet d'induction et on lance l'induction. *)
Lemma add_succ_l n m : m + (S n) = S (n + m). Admitted.

Theorem double_injective: forall n m, 2*n = 2*m -> n = m.
Proof.
  intros. generalize dependent n. 
  induction m.
  - intros. simpl in H. destruct n eqn:Hn. (*Garde la valeur de n*)
    * trivial. 
    * inversion H.
  - intros. destruct n.
    * inversion H.
    * simpl in H. inversion H. rewrite -> (plus_comm n 0) in H1. simpl in H1.
      rewrite -> (plus_comm m 0) in H1. simpl in H1.
      rewrite -> add_succ_l in H1. rewrite -> add_succ_l in H1.
      inversion H1. 
Qed.

Theorem beq_nat_eq : forall (n m:nat), n = m <-> beq_nat n m = true.
Proof.
Admitted.

Theorem beq_nat_sym : forall (n m : nat), beq_nat n m = beq_nat m n.
Proof.
Admitted.




  



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
Admitted.

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

Theorem impl_transitivity : forall (P Q R : Prop),
  (P -> Q) -> (Q-> R) -> (P -> R).
Proof.
  (* RESTRICTION : Utiliser seulement 'apply' et 'intros' *)
Admitted.

Theorem impl_transitivity' : forall (P Q R : Prop),
  (P -> Q) -> (Q-> R) -> (P -> R).
Proof.
  (* RESTRICTION : Utiliser seulement 'apply with' et 'intros' *)
Admitted.

(* Montrer une équivalence <-> on doit montrer -> et <-.
   - Si l'équivalence est dans le goal : on utilise 'split'
   - Si l'équivalence H est dans le contexte : on utilise 'destruct H' *)
Theorem equiv_comm : forall (P Q : Prop),
  (P <-> Q) <-> (Q <-> P).
Proof.
Admitted.
 
(* S'il y a une contradiction dans le contexte, utiliser la tactique 'contradiction'
   pour résoudre le goal. *)
Theorem pair_eq : forall (n:nat), Nat.even n = true <-> Nat.odd n = false.
Proof.
Admitted.

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
Admitted.

Theorem inversion_trivial1 : forall {X:Type} (h:X) (t:list X),
  [] = h::t -> 1 + 1 = 11.
Proof.
Admitted.

Theorem inversion_trivial2 : false = true -> 1 + 1 = 11.
Proof.
Admitted.

Inductive t :=
  | a
  | z
  | b : t -> t -> t
  | c : t -> t -> t -> t
  | d : t -> t.

Theorem inversion_general : forall (c1 c2 c3 c1' c2' c3' : t),
  c c1 c2 c3 = c c1' c2' c3' -> c2 = c2'.
Proof.
Admitted.

(** Puissance de l'hypothèse d'induction **)
(* Parfois il est nécessaire de laisser général les autres termes en dehors du sujet
   d'induction pour donner plus de puissance à l'hypothèse d'induction *)
(* - Soit on introduit tout et on fait 'generalize dependent' sur un terme autre que le
     sujet d'induction
   - Soit on introduit juste le sujet d'induction et on lance l'induction. *)

Theorem double_injective: forall n m, 2*n = 2*m -> n = m.
Proof.
Admitted.

Theorem beq_nat_eq : forall (n m:nat), n = m <-> beq_nat n m = true.
Proof.
Admitted.

Theorem beq_nat_sym : forall (n m : nat), beq_nat n m = beq_nat m n.
Proof.
Admitted.




  



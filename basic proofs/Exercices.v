(* Importation de module *)
Require Import Coq.Arith.Plus.
Require Import List.
(* Contexte de listes *)
Open Scope list_scope.
(* Important des notations [] et h::t *)
Import ListNotations.

Definition admit {T: Type} : T.  Admitted.

(** PAIRS : ECHAUFFEMENT **)

Definition swap_pair {X Y:Type} (p : X * Y) : (Y * X) :=
  match p with
  | (x, y) => (y, x)
  end.

Theorem swap_theorem : forall X Y (p : X * Y), (snd p, fst p) = swap_pair p.
Proof.
  destruct p.
  - simpl. reflexivity. (*Equivalent à "trivial."*)
Qed.

(** LISTES : ENTRAINEMENT **)

Theorem nil_app : forall (X:Type) (l:list X), [] ++ l = l.
Proof.
  destruct l.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* Attention : parfois destruct suffit à la place de l'induction *)
Theorem tl_length_pred : forall (X:Type) (l:list X),
  pred (length l) = length (tl l).
Proof.
  destruct l.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem app_assoc : forall (X:Type) (l1 l2 l3 : list X),
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros X l1 l2 l3.
  generalize dependent l1. (*Rajoute un forall dans le goal sur l1 (forall l1, .... à la place de (l1 ++ l2) ...*)
  induction l1.
  - trivial.
  - simpl. rewrite <- IHl1. reflexivity.
Qed.

Theorem app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
Admitted.
(* Indice : utiliser un lemme de la librairie List et la commutativité de l'addition *)
Theorem rev_length : forall (X:Type) (l:list X),
  length (rev l) = length l.
Proof.
Admitted.

Theorem rev_involutive : forall (X:Type) (l:list X),
  rev (rev l) = l.
Proof.
Admitted.

Theorem app_nil_r : forall (X:Type) (l:list X),
  l ++ [] = l.
Proof.
Admitted.

(* FORMULES : PRATIQUE *)

Definition variable : Type := nat.

Inductive formula : Type :=
  | Var : variable -> formula
  | Neg : formula -> formula
  | Or : formula -> formula -> formula
  | And : formula -> formula -> formula.


(* Définir une fonction qui calcule le nombre de parenthèses d'une formule
   et remplacer 'Prop' par 'formula' *)
Fixpoint nb_par (p:formula) : nat := admit.

(* Pareil pour le nombre de ET et de OU logiques *)
Fixpoint nb_and (p:formula) : nat := admit.
Fixpoint nb_or (p:formula) : nat := admit.

(* Se renseigner sur la tactique 'omega' de Coq qui peuvent
   résoudre automatiquement certaines preuves purement arithmétiques *)
Theorem prop1_ol5 : forall p, nb_par p = 2 * (nb_and p + nb_or p).
Proof.
Admitted.

(* Définir ces fonctions dont le nom devrait refléter le sens *)
(*taille_formula = nombre de caractères*)
Fixpoint taille_formula (p:formula) : nat := admit.
Fixpoint nb_par_left (p:formula) : nat := admit.
Fixpoint nb_par_right (p:formula) : nat := admit.
Fixpoint nb_neg (p:formula) : nat := admit.

Theorem prop2_olg5 : forall p, 
  taille_formula p = (nb_neg p) + (2 * nb_par_left p) + (2 * nb_par_right p) + 1.
Proof.
Admitted.

(* Définir l'évaluation où les valuations sont des fonctions Var -> {0, 1} *)
Fixpoint eval (v : variable -> bool) (p : formula) : bool := admit.

Notation "[[ p ]] v" := (eval v p) (at level 15).

Theorem trivial_theorem : forall x v, [[Var x]]v = v(x).
Proof.
Admitted.

(* Dans la correspondance de Curry-Howard, forall et l'implication sont vu
   comme des fonctions Preuve->Preuve.
   - S'ils sont dans le goal, on peut introduire les paramètres/hypothèses avec 'intros'
   - S'ils sont dans le contexte, on peut les appliquer comme des fonctions avec 'apply' *)
Theorem exo2_td2_ol5 : forall p v1 v2,
  (forall x, v1(x) = v2(x)) -> ([[p]]v1 = [[p]]v2).
Proof.
Admitted.



 








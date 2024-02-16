Require Export stdpp.prelude.
Require Export stdpp.finite.
From Coq Require Import ssreflect.

Ltac vm_decide := apply: bool_decide_eq_true_1; vm_compute; reflexivity.
Ltac solve_finite_nodup := vm_decide.
Ltac solve_finite_total := case; vm_decide.

Module Type eqdec_type.
  Parameter t : Type.
  #[global] Declare Instance t_eq_dec : EqDecision t.
End eqdec_type.

Module Type finite_type <: eqdec_type.
  Include eqdec_type.
  #[global] Declare Instance t_finite : Finite t.
End finite_type.

Module Type finite_encoded_type <: finite_type.
  Include finite_type.
  Parameter to_N : t -> N.
End finite_encoded_type.

Section finite_preimage.
  Context `{Finite A} `{EqDecision B}.
  Implicit Types (a : A) (b : B) (f : A → B).

  Definition finite_preimage f b : list A := filter (λ a, f a = b) (enum A).

  Lemma elem_of_finite_preimage f a b :
    a ∈ finite_preimage f b ↔ f a = b.
  Admitted.

  (** Teach [set_solver] to use [elem_of_finite_preimage]! *)
  #[global] Instance set_unfold_finite_preimage f a b P :
    SetUnfold (f a = b) P →
    SetUnfoldElemOf a (finite_preimage f b) P.
  Proof. split. rewrite elem_of_finite_preimage. set_solver. Qed.

  Lemma finite_preimage_inj_singleton `{!Inj eq eq f} a :
    finite_preimage f (f a) = [a].
  Admitted.

  Definition finite_inverse f b : option A := head $ finite_preimage f b.

  Lemma finite_inverse_Some_inv f a b :
    finite_inverse f b = Some a → f a = b.
  Proof. intros Hof%head_Some_elem_of. set_solver. Qed.

  Lemma finite_inverse_is_Some f a b :
    f a = b → is_Some (finite_inverse f b).
  Proof.
    intros Heq%elem_of_finite_preimage%elem_of_not_nil.
    exact /head_is_Some.
  Qed.

  Lemma finite_inverse_None_equiv f b :
    finite_inverse f b = None ↔ ¬(∃ a, f a = b).
  Proof.
    rewrite eq_None_not_Some. f_equiv.
    split. { intros [a ?%finite_inverse_Some_inv]. by exists a. }
    by intros [a ?%finite_inverse_is_Some].
  Qed.

  #[global] Instance set_unfold_finite_inverse_None f b P :
    (∀ a, SetUnfold (f a = b) (P a)) →
    SetUnfold (finite_inverse f b = None) (¬ (∃ a, P a)).
  Proof. constructor. rewrite finite_inverse_None_equiv. set_solver. Qed.

  Section finite_preimage_inj.
    Context `{Hinj : !Inj eq eq f}.
    #[local] Set Default Proof Using "Type*".

    Lemma finite_inverse_inj_cancel a :
      finite_inverse f (f a) = Some a.
    Proof. by rewrite /finite_inverse finite_preimage_inj_singleton. Qed.

    Lemma finite_inverse_inj_Some_equiv a b :
      finite_inverse f b = Some a ↔ f a = b.
    Proof.
      naive_solver eauto using finite_inverse_Some_inv, finite_inverse_inj_cancel.
    Qed.

    #[global] Instance set_unfold_finite_inverse_inj_Some a b P :
      SetUnfold (f a = b) P →
      SetUnfold (finite_inverse f b = Some a) P.
    Proof. constructor. rewrite finite_inverse_inj_Some_equiv. set_solver. Qed.
  End finite_preimage_inj.
End finite_preimage.


Module Type finite_encoded_type_mixin (Import F : finite_encoded_type).
  Definition of_N n := finite_inverse to_N n.

  Lemma of_to_N `[Hinj : !Inj eq eq to_N] (x : t) :
    of_N (to_N x) = Some x.
  Proof. exact: finite_inverse_inj_cancel. Qed.

  Lemma to_of_N (n : N) (x : t) :
    of_N n = Some x → to_N x = n.
  Proof. apply finite_inverse_Some_inv. Qed.
End finite_encoded_type_mixin.

Definition encode_N `{Countable A} (x : A) : N :=
  Pos.pred_N (encode x).
Definition decode_N `{Countable A} (i : N) : option A :=
  decode (N.succ_pos i).

(* Mixin hierarchy 2: *)
Module Type finite_type_mixin (Import F : finite_type).
  (*
  Not marked as an instance because it is derivable.
  It is here just in case some mixin wants it. *)
  Definition t_countable : Countable t := _.

  (* Obtain encoding from [t_finite] *)
  Definition to_N : t -> N := encode_N.
  Definition of_N : N -> option t := decode_N.

  Definition card_N A `{Finite A} : N := N.of_nat $ card A.

  Lemma of_to_N x : of_N (to_N x) = Some x.
  Admitted.

  Lemma to_of_N n x : of_N n = Some x → to_N x = n.
  Admitted.

  Lemma to_N_lt_card_N x : (to_N x < card_N t)%N.
  Admitted.
End finite_type_mixin.


From elpi.apps Require Import derive.finite_type.
From elpi.apps Require Import derive.finite.
From elpi.apps Require Import derive.eq_dec.
From elpi.apps Require Import derive.eq.
From elpi.apps Require Import derive.

Module Ty1.
  Variant ty := A | B | C | D.
  #[only(finite_type),prefix="ty_"] derive ty.
End Ty1.

Module Ty2.
  #[only(finite_type)] derive
  Variant ty := A | B | C | D.
End Ty2.

Module Ty3.
  Variant aux := E | F.

  Variant ty := A of aux | B | C | D.
  Fail #[recursive,only(finite_type)] derive ty.
End Ty3.

Module Ty4.
  Variant aux := E | F.

  Fail
  #[recursive,only(finite_type)] derive
  Variant ty := A of aux | B | C | D.
End Ty4.

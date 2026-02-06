From NominalSSP Require Import Options.

Module Tests.


Definition I1 :=
  [interface #val #[ 1%N ] : 'unit → 'unit ].

Definition I2 :=
  [interface #val #[ 2%N ] : 'unit → 'unit ].

Definition I3 :=
  [interface #val #[ 3%N ] : 'unit → 'unit ].

Definition I12 := [interface
  #val #[ 1%N ] : 'unit → 'unit ;
  #val #[ 2%N ] : 'unit → 'unit ].

Definition I123 := unionm I3 I12.

Local Obligation Tactic := ssprove_valid.

Program Definition M12 : package _ _ :=
    {package ID I1 || ID I2 }.

Program Definition M123 : package _ _ :=
    {package ID I1 || ID I2 || ID I3 }.

Goal ((ID I1 || ID I2 || ID I3) ≡ (ID I3 || ID I12)).
Proof.
  rewrite -> id_sep_par by ssprove_valid.
  rewrite -> sep_par_commut by ssprove_valid.
  rewrite -> id_sep_par by ssprove_valid.
  rewrite -> id_sep_par by ssprove_valid.
  reflexivity.
Qed.

End Tests.

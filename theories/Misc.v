From NominalSSP Require Import Options.

Notation dist := (code emptym [interface]).

Ltac ssp_ret :=
  ssprove_restore_mem; [ ssprove_invariant; try done | by apply r_ret ].

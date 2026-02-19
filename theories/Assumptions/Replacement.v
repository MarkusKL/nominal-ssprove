From NominalSSP Require Import Options Misc.

Section Replacement.
  Context (N : nat).

  Definition SAMPLE := 8%N.

  Definition I_Sample := [interface [ SAMPLE ] : { unit ~> 'I_N }].

  Definition Replaced : game I_Sample :=
    [package emptym ;
      [ SAMPLE ] (x) {
        r ← sample uniform N ;;
        ret r
      }
    ].

  Definition prev_loc := mkloc 8%N (nil : seq 'I_N).

  Definition NotReplaced : game I_Sample :=
    [package [fmap prev_loc ] ;
      [ SAMPLE ] (x) {
        prev ← get prev_loc ;;
        r ← sample uniform (N - size (fset prev)) ;;
        let r := bump (fset prev) r in
        #put prev_loc := r :: prev ;;
        ret r
      }
    ].

  Definition Replacement b := if b then Replaced else NotReplaced.
End Replacement.

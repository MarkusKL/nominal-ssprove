From NominalSSP Require Import Options Misc.

Section Replacement.
  Context (N : nat).
  Definition prev_loc := mkloc 8%N (nil : list 'Z_N). 

  Definition SAMPLE := 8%N.

  Definition I_SAMPLE := [interface [ SAMPLE ] : { unit ~> 'Z_N × bool }].

  Definition NotReplaced : game I_SAMPLE :=
    [package [fmap prev_loc ] ;
      [ SAMPLE ] (x) {
        r ← sample uniformZ N ;;
        prev ← get prev_loc ;;
        if r \in prev then
          ret (r, false)
        else
          #put prev_loc := r :: prev ;;
          ret (r, true)
      }
    ].

  Definition Replaced : game I_SAMPLE :=
    [package emptym ;
      [ SAMPLE ] (x) {
        r ← sample uniformZ N ;;
        ret (r, true)
      }
    ].

  Definition Replacement b := if b then Replaced else NotReplaced.
End Replacement.

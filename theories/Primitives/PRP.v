From NominalSSP Require Import Options Misc.

Section PRP.
  Context (k n : nat).
  Context (F : 'Z_k → 'Z_n → 'Z_n).
  Context (Finv : 'Z_k → 'Z_n → 'Z_n).

  Definition INIT := 9%N.
  Definition QUERY := 5%N.

  Definition I_PRP := [interface
    [ INIT ] : { unit ~> unit };
    [ QUERY ] : { 'Z_n ~> 'Z_n × bool } ].

  Definition key_loc := mkloc 4%N (None : option 'Z_k). 

  Definition PRP0 : game I_PRP :=
    [package [fmap key_loc] ;
      [ INIT ] (_) { 
        k ← sample uniformZ k ;;
        #put key_loc := Some k ;;
        ret tt
      } ;
      [ QUERY ] (x) {
        k ← getSome key_loc ;;
        ret (F k x, true)
      }
    ].

  Definition lazy_map_loc := mkloc 4%N (emptym : {fmap 'Z_n → 'Z_n}). 

  Definition PRP1 : game I_PRP :=
    [package [fmap lazy_map_loc ] ;
      [ INIT ] (_) {
        ret tt
      } ;
      [ QUERY ] (x) {
        L ← get lazy_map_loc ;;
        if L x is Some y then
          ret (y, true)
        else
          y ← sample uniformZ n ;;
          #put lazy_map_loc := setm L x y ;;
          ret (y, y \notin codomm L)
      }
    ].
  
  Definition PRP b := if b then PRP0 else PRP1.
End PRP.

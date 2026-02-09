From NominalSSP Require Import Options Misc.

Section PRF.
  Context (k n : nat).
  Context (F : 'Z_k → 'Z_n → 'Z_n).

  Definition INIT := 9%N.
  Definition QUERY := 5%N.

  Definition I_PRF := [interface
    [ INIT ] : { unit ~> unit };
    [ QUERY ] : { 'Z_n ~> 'Z_n } ].

  Definition key_loc := mkloc 4%N (None : option 'Z_k). 

  Definition PRF0 : game I_PRF :=
    [package [fmap key_loc] ;
      [ INIT ] (_) { 
        k ← sample uniformZ k ;;
        #put key_loc := Some k ;;
        ret tt
      } ;
      [ QUERY ] (x) {
        k ← getSome key_loc ;;
        ret (F k x)
      }
    ].

  Definition lazy_map_loc := mkloc 4%N (emptym : {fmap 'Z_n → 'Z_n}). 

  Definition PRF1 : game I_PRF :=
    [package [fmap lazy_map_loc ] ;
      [ INIT ] (_) { 
        ret tt
      } ;
      [ QUERY ] (x) {
        L ← get lazy_map_loc ;;
        if L x is Some y then
          ret y
        else
          y ← sample uniformZ n ;;
          #put lazy_map_loc := setm L x y ;;
          ret y
      }
    ].
  
  Definition PRF b := if b then PRF0 else PRF1.
End PRF.

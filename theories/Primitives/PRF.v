From NominalSSP Require Import Options Misc.

Section PRF.
  Context (K N : nat).
  Context (F : K.-bits → N.-bits → N.-bits).

  Definition INIT := 9%N.
  Definition QUERY := 5%N.

  Definition I_PRF := [interface
    [ INIT ] : { unit ~> unit };
    [ QUERY ] : { N.-bits ~> N.-bits } ].

  Definition key_loc := mkloc 4%N (None : option K.-bits).

  Definition PRF0 : game I_PRF :=
    [package [fmap key_loc] ;
      [ INIT ] (_) { 
        k ← sample uniform_bits K ;;
        #put key_loc := Some k ;;
        ret tt
      } ;
      [ QUERY ] (x) {
        k ← getSome key_loc ;;
        ret (F k x)
      }
    ].

  Definition lazy_map_loc := mkloc 4%N (emptym : {fmap N.-bits → N.-bits}).

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
          y ← sample uniform_bits N ;;
          #put lazy_map_loc := setm L x y ;;
          ret y
      }
    ].
  
  Definition PRF b := if b then PRF0 else PRF1.
End PRF.

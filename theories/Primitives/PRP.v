From NominalSSP Require Import Options Misc.

Section PRP.
  Context (K N : nat).
  Context (F : K.-bits → N.-bits → N.-bits).
  Context (Finv : K.-bits → N.-bits → N.-bits).

  Definition INIT := 9%N.
  Definition QUERY := 5%N.

  Definition I_PRP := [interface
    [ INIT ] : { unit ~> unit };
    [ QUERY ] : { N.-bits ~> N.-bits × bool } ].

  Definition key_loc := mkloc 4%N (None : option K.-bits).

  Definition PRP0 : game I_PRP :=
    [package [fmap key_loc] ;
      [ INIT ] (_) { 
        k ← sample uniform_bits K ;;
        #put key_loc := Some k ;;
        ret tt
      } ;
      [ QUERY ] (x) {
        k ← getSome key_loc ;;
        ret (F k x, true)
      }
    ].

  Definition lazy_map_loc := mkloc 4%N (emptym : {fmap N.-bits → N.-bits}).

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
          y ← sample uniform_bits N ;;
          #put lazy_map_loc := setm L x y ;;
          ret (y, y \notin codomm L)
      }
    ].
  
  Definition PRP b := if b then PRP0 else PRP1.
End PRP.

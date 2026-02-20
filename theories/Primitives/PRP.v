From NominalSSP Require Import Options Misc.

Section PRP.
  Context (K N : nat).
  Context (F : K.-bits → N.-bits → N.-bits).
  Context (Finv : K.-bits → N.-bits → N.-bits).

  Definition INIT := 9%N.
  Definition QUERY := 5%N.

  Definition I_PRP := [interface
    [ INIT ] : { unit ~> unit };
    [ QUERY ] : { N.-bits ~> N.-bits } ].

  Definition key_loc := mkloc 4%N (None : option K.-bits).

  Definition PRP0 : game I_PRP :=
    [package [fmap key_loc] ;
      [ INIT ] (_) { 
        getNone key_loc ;;
        k ← sample uniform_bits K ;;
        #put key_loc := Some k ;;
        ret tt
      } ;
      [ QUERY ] (x) {
        k ← getSome key_loc ;;
        ret (F k x)
      }
    ].

  Definition lazy_map_loc := mkloc 4%N (None : option {fmap N.-bits → N.-bits}).

  Definition PRP1 : game I_PRP :=
    [package [fmap lazy_map_loc ] ;
      [ INIT ] (_) {
        getNone lazy_map_loc ;;
        #put lazy_map_loc := Some emptym ;;
        ret tt
      } ;
      [ QUERY ] (x) {
        L ← getSome lazy_map_loc ;;
        if L x is Some y then
          ret y
        else
          y ← sample uniform (2 ^ N - size (codomm L)) ;;
          let y := bump (codomm L) y in
          #put lazy_map_loc := Some (setm L x y) ;;
          ret y
      }
    ].
  
  Definition PRP b := if b then PRP0 else PRP1.
End PRP.

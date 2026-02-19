From NominalSSP Require Import Options Misc.

Section Nonce.
  Context (N : nat).
  Definition nonce_loc := mkloc 12%N (nil : list 'I_N).

  Definition NONCE := 30%N.

  Definition I_Nonce := [interface [ NONCE ] : { unit ~> 'I_N × bool }].

  Definition Nonce0 : game I_Nonce :=
    [package emptym ;
      [ NONCE ] (x) {
        r ← sample uniform N ;;
        ret (r, true)
      }
    ].

  Definition Nonce1 : game I_Nonce :=
    [package [fmap nonce_loc ] ;
      [ NONCE ] (x) {
        r ← sample uniform N ;;
        prev ← get nonce_loc ;;
        if r \in prev then
          ret (r, false)
        else
          #put nonce_loc := r :: prev ;;
          ret (r, true)
      }
    ].


  Definition Nonce b := if b then Nonce0 else Nonce1.
End Nonce.

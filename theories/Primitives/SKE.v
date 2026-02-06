From NominalSSP Require Import Options Misc.

Record SKE :=
  { Key : choice_type
  ; Mes : choice_type
  ; Cip : choice_type
  ; KeyDist : dist Key
  ; Enc : Key → Mes → dist Cip
  ; Dec : Key → Cip → option Mes
  ; CipDist : dist Cip
  }.

Section SKE.
  Context (P : SKE).

  Definition ENCDEC := 0%N.

  Definition I_CORR :=
    [interface [ ENCDEC ] : { P.(Mes) ~> option P.(Mes) } ].

  Definition CORR0 : game I_CORR :=
    [package emptym ;
      [ ENCDEC ] (m) {
        k ← P.(KeyDist) ;;
        c ← P.(Enc) k m ;;
        ret (P.(Dec) k c)
      }
    ].

  Definition CORR1 :
    game I_CORR :=
    [package emptym ;
      [ ENCDEC ] (m) {
        ret (Some m)
      }
    ].

  Definition CORR b := if b then CORR0 else CORR1.


  Definition QUERY := 5%N.

  Definition I_OTS :=
    [interface [ QUERY ] : { P.(Mes) ~> P.(Cip) } ].

  Definition OTS b :
    game I_OTS :=
    [package emptym ;
      [ QUERY ] : { P.(Mes) ~> P.(Cip) } (m) {
        if b then
          k ← P.(KeyDist) ;; (* run keygen only in real? *)
          P.(Enc) k m
        else
          P.(CipDist)
      }
    ].
End SKE.

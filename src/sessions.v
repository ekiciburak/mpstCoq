From MPSTCoq Require Export src.unscoped src.expressions src.processes.
Require Import List String Relations.

Inductive session: Type :=
  | s_par : part    -> process -> session
  | s_cons: session -> session -> session.

Inductive s_cong: relation session :=
  | s_cong_multi: forall P Q p M, 
                  p_cong P Q -> 
                  s_cong (s_cons (s_par p P) M) (s_cons (s_par p Q) M)
  | s_cong_par1 : forall p M,
                  s_cong (s_cons (s_par p p_inact) M) M
  | s_cong_par2 : forall M M',
                  s_cong (s_cons M M') (s_cons M' M)
  | s_cong_par3 : forall M M' M'',
                  s_cong (s_cons (s_cons M M') M'') (s_cons M (s_cons M' M'')).


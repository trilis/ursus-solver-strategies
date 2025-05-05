Require Export CommonTactics.
Require Import UrsusEnvironment.Solidity.current.Environment.

Require Import If.If.
Import If.

Require Import If.Common.

Module IfLedger <: WithLedger.

Definition Ledger := LedgerLRecord rec.

End IfLedger.

Module Export ContractTactics := ContractTactics IfLedger.

Ltac preprocess_ifs :=
    repeat match goal with 
    | H: context[if ?b then _ else _] |- _ =>
      match goal with 
        | H0: b = ?t |- _=> repeat (
          match goal with 
            | _: b = ?t' |- _ => 
              match goal with
                | H: ?y = _ |- _ =>
                  match t' with 
                    | context[y] => 
                      rewrite H in H0
                  end
              end
          end
        ); lazy in H0; rewrite <- H0; clear H0
      end
  end.

  Ltac lift_lets P0 Heql Hprev :=
    (* repeat *) match goal with
    | |- P0 ?ll => 
        match ll with
        | (let x:=?t in @?f x) =>
            idtac "'let' is found in the goal with:" x;
            match goal with
            | _ =>  idtac "item is not found, making new for" t;
                    let y := fresh "y" in
                    pose (y:=t);
                    let f' := eval cbv beta in (f y) in
                    change_no_check (P0 ll) with (P0 f');
                    let H := fresh "H" in
                    assert (y = t) as H by (* (exact_no_check eq_refl) *) reflexivity;
                    clearbody y;
                    move y before Hprev;
                    move H before Hprev;
                    lift_lets P0 Heql (H)
            end
        | _ => idtac "'let' is not found in the goal";
               match goal with
               | H: ?z = ll |- _ => idtac "item is found:" z;
                                    change_no_check (P0 ll) with (P0 z)
                                
               | _ =>  idtac "item is not found, making new for" ll;
                       let y := fresh "y" in
                       pose (y:=ll);
                       change_no_check (P0 ll) with (P0 y);
                       let H := fresh "H" in
                       assert (y = ll) as H by (* (exact_no_check eq_refl) *) reflexivity;
                       clearbody y;  
                       move y before Hprev;
                       move H before Hprev
               end;        
               clear Heql;
               subst P0; 
               intros Heql;
               match type of Heql with 
                   | ?l = _ => subst l
               end
        end
    end.

Ltac continue f_exec f_exec_prf f_destructor Heql Hprev :=
(* let Heql := fresh "Heql" in *)
(* match goal with 
| |- ?P _ =>  *)
(* Heql = ? = exec_state ... *)
revert Heql;
erewrite <- (* ? *)f_exec_prf; [
(* |- fun_exec... *)
let ll := fresh "ll" in
let ll' := fresh "ll'" in
f_destructor ll ll'; (* ? *)
(* ll = fun_exec, ll' := ll |- f (ll) *)
change_no_check ll with ll';
(* ll = fun_exec, ll' := ll |- f (ll')  *)
revert ll';
(* ll = fun_exec |- let ll' := ll in f (ll')  *)
let P0 := fresh "P" in 
match goal with
| |- let ll' := _ in @?F ll' => (* remember F as P0 *)
     let HF := fresh "HeqF" in 
     pose F as P0; assert (P0 = F) as HF by (* (exact_no_check eq_refl) *)reflexivity; clearbody P0
end;
intros;
(* ll = fun_exec, ll' := ll, P0 = |- P0 (ll')  *)
(* match goal with
| |- ?G => *) assert (P0 ll'); [| subst P0; (* subst P; *) auto]
(* end *);
subst ll' ll;
cbv beta delta [f_exec];
lift_lets P0 Heql Hprev | .. ].

Ltac2 continue_iter x := 
let t := ltac1:(p |- 
idtac "looking for" p "in evals/execs";
let continue_once a :=
multimatch goal with
| H: ?y = ?X |- _ => match X with
                   | context [eval_state (UinterpreterUnf ?listInfinite ?t) ?l] =>
                     match t with 
                     | context [p] => 
                       idtac "eval found" p "in" H "with" y;
                       let h := eval cbn in ltac:(__index_hash p) in
                       let ee := constr:(__eval (f:=h)) in
                       let e := match ee with
                       | @__eval _ _ _ _ ?I => eval cbv beta iota delta [__eval I] in ee
                       end in
                       (* let e := eval simpl __eval in (__eval (f:=p))in *)
                       let d := ltac:(destructor_template e) in
                       let eprf := constr:(__eval_prf (f:=h)) in
                       let prf := match eprf with
                       | @__eval_prf _ _ _ _ ?I => eval cbv beta iota delta [__eval_prf I] in eprf
                       end in 
                       continue e prf d H (y) 
                     end   
                   | context [exec_state (UinterpreterUnf ?listInfinite ?t) ?l] => 
                     match t with 
                     | context [p] =>
                       idtac "exec found" p "in" H "with" y;
                       let h := eval cbn in ltac:(__index_hash p) in
                       let ee := constr:(__exec (f:=h)) in
                       let e := match ee with
                       | @__exec _ _ _ _ ?I => eval cbv beta iota delta [__exec I] in ee
                       end in
                       (* let e := eval simpl __exec in (__exec (f:=p))in *)
                       let d := ltac:(destructor_template e) in
                       let eprf := constr:(__exec_prf (f:=h)) in
                       let prf := match eprf with
                       | @__exec_prf _ _ _ _ ?I => eval cbv beta iota delta [__exec_prf I] in eprf
                       end in
                       continue e prf d H (y) 
                     end
                   (* | _ => idtac "no more" p "found in" H; fail *)
                  end
end in repeat2 continue_once) in t x.

Tactic Notation "continue_all" constr_list(cl) :=
idtac "Looking for list:" cl;
let f := ltac2:(cl_raw |-
let cl' := Option.get (Ltac1.to_list cl_raw) in
List.iter (fun c => continue_iter c) cl') in 
 f cl; (* simpl orb in * *) cbn [orb] in * . 
 (* TODO: sometimes simpl orb simplifies orb in goal which is bad *)
 (* Maybe cbn fixes that *)
